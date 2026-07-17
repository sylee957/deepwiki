import { realpath } from 'node:fs/promises'
import path from 'node:path'
import { fileURLToPath } from 'node:url'
import {
  LeanLanguageServer,
  highlightRanges,
  hoverRange,
  hoverText,
  plainGoalText,
  plainTermGoal,
  type LeanNotification,
  type Position
} from './lean-lsp.ts'
import {
  FileAccessError,
  isVisibleRepositoryPath,
  readRepositoryTextFile
} from './path-policy.ts'
import { buildFileTree, listRepositoryFiles } from './repository.ts'

const toolRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..')
const frontendRoot = path.join(toolRoot, 'frontend')
const distRoot = path.join(toolRoot, 'dist')

interface Logger {
  error(message?: unknown): void
}

export async function createLeanMobileApp(options: {
  repositoryRoot?: string
  logger?: Logger
} = {}) {
  const root = await realpath(options.repositoryRoot ?? path.resolve(toolRoot, '../..'))
  const logger = options.logger ?? console
  const lean = new LeanLanguageServer(root, logger)

  return {
    root,
    lean,
    fetch: async (request: Request) => {
      try {
        return await routeRequest(request, { root, lean })
      } catch (error) {
        const status = isAbortError(error) ? 499 : error instanceof FileAccessError ? error.statusCode : 500
        if (status === 500) logger.error(error)
        return jsonResponse(status, {
          error: error instanceof Error ? error.message : 'Unexpected server error'
        })
      }
    }
  }
}

async function routeRequest(
  request: Request,
  context: { root: string; lean: LeanLanguageServer }
) {
  const url = new URL(request.url)

  if (request.method === 'GET' && url.pathname === '/api/tree') {
    const files = await listRepositoryFiles(context.root)
    return jsonResponse(200, { tree: buildFileTree(files), count: files.length })
  }

  if (request.method === 'GET' && url.pathname === '/api/events') {
    return leanEventStream(request, context.root, context.lean)
  }

  if (request.method === 'GET' && url.pathname === '/api/file') {
    const relativePath = url.searchParams.get('path') ?? ''
    const file = await readRepositoryTextFile(context.root, relativePath)
    return jsonResponse(200, { path: relativePath, text: file.text, size: file.size })
  }

  if (request.method === 'POST' && url.pathname === '/api/hover') {
    const body = await readJson(request)
    const relativePath = body.path
    const position = validatePosition(body.position)
    const file = await readRepositoryTextFile(context.root, relativePath)
    if (typeof relativePath !== 'string' || !relativePath.endsWith('.lean')) {
      throw new FileAccessError('Hover is available for Lean files', 400)
    }
    const result = await context.lean.caretInfo(file.absolutePath, file.text, position, request.signal)
    return jsonResponse(200, {
      hover: hoverText(result.hover),
      range: hoverRange(result.hover),
      highlights: highlightRanges(result.highlights),
      goals: plainGoalText(result.goals),
      termGoal: plainTermGoal(result.termGoal)
    })
  }

  if (request.method === 'POST' && url.pathname === '/api/definition') {
    const body = await readJson(request)
    const relativePath = body.path
    const position = validatePosition(body.position)
    const file = await readRepositoryTextFile(context.root, relativePath)
    if (typeof relativePath !== 'string' || !relativePath.endsWith('.lean')) {
      throw new FileAccessError('Definition lookup is available for Lean files', 400)
    }
    const result = await context.lean.definition(file.absolutePath, file.text, position, request.signal)
    return jsonResponse(200, { definitions: normalizeDefinitions(context.root, result) })
  }

  if (request.method !== 'GET' && request.method !== 'HEAD') {
    return jsonResponse(405, { error: 'Read-only server: method not allowed' })
  }

  return serveStatic(
    url.pathname,
    request.method === 'HEAD',
    request.headers.get('accept')?.includes('text/html') ?? false
  )
}

function leanEventStream(request: Request, root: string, lean: LeanLanguageServer) {
  const encoder = new TextEncoder()
  let cleanup = () => {}
  const stream = new ReadableStream<Uint8Array>({
    start(controller) {
      let closed = false
      const send = (text: string) => {
        if (closed) return
        try {
          controller.enqueue(encoder.encode(text))
        } catch {
          cleanup()
        }
      }
      const unsubscribe = lean.onNotification(notification => {
        const event = leanProgressEvent(root, notification)
        if (event) send(`event: lean-progress\ndata: ${JSON.stringify(event)}\n\n`)
      })
      const heartbeat = setInterval(() => send(': keep-alive\n\n'), 5_000)
      const abort = () => {
        cleanup()
        try {
          controller.close()
        } catch {
          // The stream may already have been cancelled by the client.
        }
      }
      cleanup = () => {
        if (closed) return
        closed = true
        clearInterval(heartbeat)
        unsubscribe()
        request.signal.removeEventListener('abort', abort)
      }
      request.signal.addEventListener('abort', abort, { once: true })
      send(': connected\n\n')
    },
    cancel() {
      cleanup()
    }
  })
  return new Response(stream, {
    status: 200,
    headers: securityHeaders({
      'Content-Type': 'text/event-stream; charset=utf-8',
      'Cache-Control': 'no-store',
      Connection: 'keep-alive'
    })
  })
}

function leanProgressEvent(root: string, notification: LeanNotification) {
  if (notification.method !== '$/lean/fileProgress' || !isObject(notification.params)) return null
  const textDocument = notification.params.textDocument
  const processing = notification.params.processing
  if (!isObject(textDocument) || typeof textDocument.uri !== 'string' || !Array.isArray(processing)) {
    return null
  }
  const relativePath = repositoryPathFromUri(root, textDocument.uri)
  if (!relativePath) return null
  const state = processing.some(item => isObject(item) && item.kind === 2)
    ? 'error'
    : processing.length > 0 ? 'processing' : 'ready'
  return { path: relativePath, state }
}

async function serveStatic(pathname: string, headOnly: boolean, acceptsHtml: boolean) {
  const files: Record<string, [string, string]> = {
    '/': [path.join(frontendRoot, 'index.html'), 'text/html; charset=utf-8'],
    '/app.js': [path.join(distRoot, 'app.js'), 'text/javascript; charset=utf-8'],
    '/style.css': [path.join(frontendRoot, 'style.css'), 'text/css; charset=utf-8']
  }
  const isBrowserRoute = acceptsHtml && !pathname.startsWith('/api/')
  const item = files[pathname] ?? (isBrowserRoute ? files['/'] : undefined)
  if (!item) return jsonResponse(404, { error: 'Not found' })

  const file = Bun.file(item[0])
  if (!(await file.exists())) {
    return jsonResponse(503, { error: 'Frontend is not built; run `bun run build`' })
  }
  return new Response(headOnly ? null : file, {
    status: 200,
    headers: securityHeaders({
      'Content-Type': item[1],
      'Cache-Control': 'no-store'
    })
  })
}

interface DefinitionLocation {
  uri?: string
  targetUri?: string
  range?: { start?: Position }
  targetSelectionRange?: { start?: Position }
}

function normalizeDefinitions(root: string, result: unknown) {
  const locations = result == null ? [] : Array.isArray(result) ? result : [result]
  return locations.flatMap(location => {
    if (!isObject(location)) return []
    const typed = location as DefinitionLocation
    const uri = typed.targetUri ?? typed.uri
    const range = typed.targetSelectionRange ?? typed.range
    if (typeof uri !== 'string' || !uri.startsWith('file:') || !range?.start) return []
    const absolutePath = fileURLToPath(uri)
    const relativePath = path.relative(root, absolutePath).split(path.sep).join('/')
    if (!isVisibleRepositoryPath(relativePath)) return []
    return [{ path: relativePath, position: range.start }]
  })
}

function repositoryPathFromUri(root: string, uri: string) {
  if (!uri.startsWith('file:')) return null
  try {
    const relativePath = path.relative(root, fileURLToPath(uri)).split(path.sep).join('/')
    return isVisibleRepositoryPath(relativePath) ? relativePath : null
  } catch {
    return null
  }
}

function validatePosition(value: unknown): Position {
  if (!isObject(value)) throw new FileAccessError('Invalid source position', 400)
  const line = value.line
  const character = value.character
  if (!Number.isInteger(line) || Number(line) < 0 || !Number.isInteger(character) || Number(character) < 0) {
    throw new FileAccessError('Invalid source position', 400)
  }
  return { line: Number(line), character: Number(character) }
}

async function readJson(request: Request): Promise<Record<string, unknown>> {
  const length = Number(request.headers.get('content-length') ?? 0)
  if (length > 64 * 1024) throw new FileAccessError('Request is too large', 413)
  try {
    const text = await request.text()
    if (new TextEncoder().encode(text).length > 64 * 1024) {
      throw new FileAccessError('Request is too large', 413)
    }
    const value: unknown = JSON.parse(text)
    if (!isObject(value)) throw new Error('Expected an object')
    return value
  } catch (error) {
    if (error instanceof FileAccessError) throw error
    throw new FileAccessError('Invalid JSON request', 400)
  }
}

function jsonResponse(status: number, value: unknown) {
  return Response.json(value, {
    status,
    headers: securityHeaders({ 'Cache-Control': 'no-store' })
  })
}

function securityHeaders(extra: Record<string, string>) {
  return {
    'Content-Security-Policy': "default-src 'self'; style-src 'self' 'unsafe-inline'; script-src 'self'; connect-src 'self'; base-uri 'none'; form-action 'none'; frame-ancestors 'none'",
    'Referrer-Policy': 'no-referrer',
    'X-Content-Type-Options': 'nosniff',
    'X-Frame-Options': 'DENY',
    ...extra
  }
}

function parseArguments(argv: string[]) {
  const options: { host: string; port: number; repositoryRoot?: string } = {
    host: '127.0.0.1',
    port: 3210
  }
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index]
    if (argument === '--host') options.host = argv[++index] ?? ''
    else if (argument === '--port') options.port = Number(argv[++index])
    else if (argument === '--root') options.repositoryRoot = path.resolve(argv[++index] ?? '')
    else throw new Error(`Unknown argument: ${argument}`)
  }
  if (!options.host || !Number.isInteger(options.port) || options.port < 1 || options.port > 65535) {
    throw new Error('Usage: bun start [--host ADDRESS] [--port PORT] [--root REPOSITORY]')
  }
  return options
}

function isObject(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null
}

function isAbortError(error: unknown) {
  return error instanceof DOMException && error.name === 'AbortError'
}

if (import.meta.main) {
  const options = parseArguments(Bun.argv.slice(2))
  const app = await createLeanMobileApp(options)
  const server = Bun.serve({
    hostname: options.host,
    port: options.port,
    fetch: app.fetch
  })
  console.log(`Lean Mobile is reading ${app.root}`)
  console.log(`Open ${server.url}`)
  if (!['127.0.0.1', '::1', 'localhost'].includes(options.host)) {
    console.warn('Network binding enabled. Restrict access with a firewall or private VPN.')
  }

  const stop = async () => {
    server.stop(true)
    await app.lean.stop()
    globalThis.process.exit(0)
  }
  globalThis.process.once('SIGINT', () => void stop())
  globalThis.process.once('SIGTERM', () => void stop())
}
