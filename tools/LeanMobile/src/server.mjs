import http from 'node:http'
import { readFile, realpath } from 'node:fs/promises'
import path from 'node:path'
import { fileURLToPath } from 'node:url'
import { LeanLanguageServer, hoverText } from './lean-lsp.mjs'
import { FileAccessError, readRepositoryTextFile } from './path-policy.mjs'
import { buildFileTree, listRepositoryFiles } from './repository.mjs'

const toolRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..')
const publicRoot = path.join(toolRoot, 'public')

export async function createLeanMobileServer({ repositoryRoot, logger = console } = {}) {
  const root = await realpath(repositoryRoot ?? path.resolve(toolRoot, '../..'))
  const lean = new LeanLanguageServer(root, { logger })

  const server = http.createServer(async (request, response) => {
    try {
      await routeRequest(request, response, { root, lean })
    } catch (error) {
      const status = error instanceof FileAccessError ? error.statusCode : 500
      if (status === 500) logger.error(error)
      sendJson(response, status, { error: error.message ?? 'Unexpected server error' })
    }
  })

  server.on('close', () => void lean.stop())
  return { server, root, lean }
}

async function routeRequest(request, response, context) {
  const url = new URL(request.url, 'http://localhost')

  if (request.method === 'GET' && url.pathname === '/api/tree') {
    const files = await listRepositoryFiles(context.root)
    sendJson(response, 200, { tree: buildFileTree(files), count: files.length })
    return
  }

  if (request.method === 'GET' && url.pathname === '/api/file') {
    const file = await readRepositoryTextFile(context.root, url.searchParams.get('path') ?? '')
    sendJson(response, 200, { path: url.searchParams.get('path'), text: file.text, size: file.size })
    return
  }

  if (request.method === 'POST' && url.pathname === '/api/hover') {
    const body = await readJson(request)
    const position = validatePosition(body.position)
    const file = await readRepositoryTextFile(context.root, body.path)
    if (!body.path.endsWith('.lean')) throw new FileAccessError('Hover is available for Lean files', 400)
    const result = await context.lean.hover(file.absolutePath, file.text, position)
    sendJson(response, 200, { hover: hoverText(result), range: result?.range ?? null })
    return
  }

  if (request.method === 'POST' && url.pathname === '/api/definition') {
    const body = await readJson(request)
    const position = validatePosition(body.position)
    const file = await readRepositoryTextFile(context.root, body.path)
    if (!body.path.endsWith('.lean')) throw new FileAccessError('Definition lookup is available for Lean files', 400)
    const result = await context.lean.definition(file.absolutePath, file.text, position)
    sendJson(response, 200, { definitions: normalizeDefinitions(context.root, result) })
    return
  }

  if (request.method !== 'GET' && request.method !== 'HEAD') {
    sendJson(response, 405, { error: 'Read-only server: method not allowed' })
    return
  }

  await serveStatic(url.pathname, response, request.method === 'HEAD')
}

async function serveStatic(pathname, response, headOnly) {
  const names = {
    '/': ['index.html', 'text/html; charset=utf-8'],
    '/app.js': ['app.js', 'text/javascript; charset=utf-8'],
    '/style.css': ['style.css', 'text/css; charset=utf-8']
  }
  const item = names[pathname]
  if (!item) {
    sendJson(response, 404, { error: 'Not found' })
    return
  }
  const body = await readFile(path.join(publicRoot, item[0]))
  response.writeHead(200, securityHeaders({
    'Content-Type': item[1],
    'Content-Length': body.length,
    'Cache-Control': 'no-store'
  }))
  response.end(headOnly ? undefined : body)
}

function normalizeDefinitions(root, result) {
  const locations = result == null ? [] : Array.isArray(result) ? result : [result]
  return locations.flatMap(location => {
    const uri = location.targetUri ?? location.uri
    const range = location.targetSelectionRange ?? location.range
    if (typeof uri !== 'string' || !uri.startsWith('file:') || !range) return []
    const absolutePath = fileURLToPath(uri)
    const relativePath = path.relative(root, absolutePath)
    if (relativePath.startsWith('..') || path.isAbsolute(relativePath)) return []
    return [{ path: relativePath.split(path.sep).join('/'), position: range.start }]
  })
}

function validatePosition(position) {
  const line = position?.line
  const character = position?.character
  if (!Number.isInteger(line) || line < 0 || !Number.isInteger(character) || character < 0) {
    throw new FileAccessError('Invalid source position', 400)
  }
  return { line, character }
}

async function readJson(request) {
  const chunks = []
  let size = 0
  for await (const chunk of request) {
    size += chunk.length
    if (size > 64 * 1024) throw new FileAccessError('Request is too large', 413)
    chunks.push(chunk)
  }
  try {
    return JSON.parse(Buffer.concat(chunks).toString('utf8'))
  } catch {
    throw new FileAccessError('Invalid JSON request', 400)
  }
}

function sendJson(response, status, value) {
  if (response.headersSent) return
  const body = Buffer.from(JSON.stringify(value), 'utf8')
  response.writeHead(status, securityHeaders({
    'Content-Type': 'application/json; charset=utf-8',
    'Content-Length': body.length,
    'Cache-Control': 'no-store'
  }))
  response.end(body)
}

function securityHeaders(extra) {
  return {
    'Content-Security-Policy': "default-src 'self'; style-src 'self'; script-src 'self'; connect-src 'self'; base-uri 'none'; form-action 'none'; frame-ancestors 'none'",
    'Referrer-Policy': 'no-referrer',
    'X-Content-Type-Options': 'nosniff',
    'X-Frame-Options': 'DENY',
    ...extra
  }
}

function parseArguments(argv) {
  const options = { host: '127.0.0.1', port: 3210 }
  for (let index = 0; index < argv.length; index += 1) {
    if (argv[index] === '--host') options.host = argv[++index]
    else if (argv[index] === '--port') options.port = Number(argv[++index])
    else if (argv[index] === '--root') options.repositoryRoot = path.resolve(argv[++index])
    else throw new Error(`Unknown argument: ${argv[index]}`)
  }
  if (!options.host || !Number.isInteger(options.port) || options.port < 1 || options.port > 65535) {
    throw new Error('Usage: npm start -- [--host ADDRESS] [--port PORT] [--root REPOSITORY]')
  }
  return options
}

const isMain = process.argv[1]
  && await realpath(fileURLToPath(import.meta.url)) === await realpath(process.argv[1])

if (isMain) {
  const options = parseArguments(process.argv.slice(2))
  const { server, root } = await createLeanMobileServer(options)
  await new Promise((resolve, reject) => {
    server.once('error', reject)
    server.listen(options.port, options.host, resolve)
  })
  console.log(`Lean Mobile is reading ${root}`)
  console.log(`Open http://${options.host}:${options.port}`)
  if (options.host !== '127.0.0.1' && options.host !== '::1' && options.host !== 'localhost') {
    console.warn('Network binding enabled. Restrict access with a firewall or private VPN.')
  }
  await new Promise(resolve => server.once('close', resolve))
}
