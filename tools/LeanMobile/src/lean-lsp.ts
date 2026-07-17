import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process'
import { pathToFileURL } from 'node:url'

export interface Position {
  line: number
  character: number
}

export interface Range {
  start: Position
  end: Position
}

interface JsonRpcMessage {
  jsonrpc: '2.0'
  id?: number
  method?: string
  params?: unknown
  result?: unknown
  error?: { code?: number; message?: string }
}

interface PendingRequest {
  resolve: (value: unknown) => void
  reject: (error: Error) => void
  timeout: ReturnType<typeof setTimeout>
  removeAbortListener?: () => void
}

interface OpenDocument {
  uri: string
  text: string
  version: number
}

export interface LeanNotification {
  method: string
  params: unknown
}

export type LeanNotificationListener = (notification: LeanNotification) => void

interface Logger {
  error(message?: unknown): void
}

export class LeanLanguageServer {
  private process: ChildProcessWithoutNullStreams | null = null
  private buffer = Buffer.alloc(0)
  private nextId = 1
  private readonly pending = new Map<number, PendingRequest>()
  private readonly notificationListeners = new Set<LeanNotificationListener>()
  private document: OpenDocument | null = null
  private ready: Promise<void> | null = null

  constructor(private readonly root: string, private readonly logger: Logger = console) {}

  async start() {
    if (this.ready) return this.ready
    this.ready = this.startProcess()
    try {
      await this.ready
    } catch (error) {
      this.ready = null
      throw error
    }
  }

  private async startProcess() {
    this.process = spawn('lake', ['env', 'lean', '--server'], {
      cwd: this.root,
      stdio: ['pipe', 'pipe', 'pipe']
    })

    this.process.stdout.on('data', (chunk: Buffer) => this.receive(chunk))
    this.process.stderr.on('data', (chunk: Buffer) => {
      const message = chunk.toString('utf8').trim()
      if (message) this.logger.error(`[lean] ${message}`)
    })
    this.process.on('error', error => this.failAll(error))
    this.process.on('exit', (code, signal) => {
      this.failAll(new Error(`Lean language server exited (${signal ?? code})`))
      this.process = null
      this.ready = null
      this.document = null
    })

    const rootUri = pathToFileURL(this.root).href
    await this.request('initialize', {
      processId: globalThis.process.pid,
      clientInfo: { name: 'DeepWiki Lean Mobile', version: '0.2.0' },
      rootUri,
      capabilities: {
        textDocument: {
          hover: { contentFormat: ['markdown', 'plaintext'] },
          definition: { linkSupport: true },
          synchronization: { didSave: false, dynamicRegistration: false }
        },
        workspace: { workspaceFolders: true }
      },
      workspaceFolders: [{ uri: rootUri, name: 'deepwiki' }],
      initializationOptions: { editDelay: 50, hasWidgets: false }
    }, 30_000)
    this.notify('initialized', {})
  }

  onNotification(listener: LeanNotificationListener) {
    this.notificationListeners.add(listener)
    return () => this.notificationListeners.delete(listener)
  }

  async hover(absolutePath: string, text: string, position: Position, signal?: AbortSignal) {
    if (signal?.aborted) throw abortError('textDocument/hover')
    await this.openDocument(absolutePath, text)
    return this.request('textDocument/hover', {
      textDocument: { uri: pathToFileURL(absolutePath).href },
      position
    }, 60_000, signal)
  }

  async definition(absolutePath: string, text: string, position: Position, signal?: AbortSignal) {
    if (signal?.aborted) throw abortError('textDocument/definition')
    await this.openDocument(absolutePath, text)
    return this.request('textDocument/definition', {
      textDocument: { uri: pathToFileURL(absolutePath).href },
      position
    }, 60_000, signal)
  }

  private async openDocument(absolutePath: string, text: string) {
    await this.start()
    const uri = pathToFileURL(absolutePath).href
    const previous = this.document
    if (previous?.uri === uri && previous.text === text) return

    if (previous?.uri !== uri) {
      if (previous) {
        this.notify('textDocument/didClose', {
          textDocument: { uri: previous.uri }
        })
      }
      this.document = { uri, text, version: 1 }
      this.notify('textDocument/didOpen', {
        textDocument: { uri, languageId: 'lean4', version: 1, text }
      })
      return
    }

    const version = previous.version + 1
    this.document = { uri, text, version }
    this.notify('textDocument/didChange', {
      textDocument: { uri, version },
      contentChanges: [{ text }]
    })
  }

  request(method: string, params: unknown, timeoutMs = 30_000, signal?: AbortSignal): Promise<unknown> {
    if (!this.process) return Promise.reject(new Error('Lean language server is not running'))
    if (signal?.aborted) return Promise.reject(abortError(method))
    const id = this.nextId++
    return new Promise((resolve, reject) => {
      const timeout = setTimeout(() => {
        const request = this.takePending(id)
        if (!request) return
        this.notify('$/cancelRequest', { id })
        reject(new Error(`Lean request timed out: ${method}`))
      }, timeoutMs)
      const pending: PendingRequest = { resolve, reject, timeout }
      if (signal) {
        const abort = () => {
          const request = this.takePending(id)
          if (!request) return
          this.notify('$/cancelRequest', { id })
          request.reject(abortError(method))
        }
        signal.addEventListener('abort', abort, { once: true })
        pending.removeAbortListener = () => signal.removeEventListener('abort', abort)
      }
      this.pending.set(id, pending)
      this.send({ jsonrpc: '2.0', id, method, params })
    })
  }

  notify(method: string, params: unknown) {
    if (!this.process) return
    this.send({ jsonrpc: '2.0', method, params })
  }

  async stop() {
    if (!this.process) return
    const leanProcess = this.process
    if (this.document) {
      this.notify('textDocument/didClose', {
        textDocument: { uri: this.document.uri }
      })
      this.document = null
    }
    try {
      await this.request('shutdown', null, 5_000)
    } catch {
      // If shutdown cannot complete, the process is terminated below.
    }
    if (this.process === leanProcess) {
      this.notify('exit', {})
      const forceStop = setTimeout(() => leanProcess.kill(), 1_000)
      forceStop.unref()
    }
  }

  private send(message: JsonRpcMessage) {
    if (!this.process) return
    const body = Buffer.from(JSON.stringify(message), 'utf8')
    const header = Buffer.from(`Content-Length: ${body.length}\r\n\r\n`, 'ascii')
    this.process.stdin.write(Buffer.concat([header, body]))
  }

  private receive(chunk: Buffer) {
    this.buffer = Buffer.concat([this.buffer, chunk])
    while (true) {
      const headerEnd = this.buffer.indexOf('\r\n\r\n')
      if (headerEnd < 0) return
      const header = this.buffer.subarray(0, headerEnd).toString('ascii')
      const match = /Content-Length:\s*(\d+)/i.exec(header)
      if (!match?.[1]) {
        this.failAll(new Error('Invalid response from Lean language server'))
        return
      }
      const length = Number(match[1])
      const bodyStart = headerEnd + 4
      if (this.buffer.length < bodyStart + length) return
      const body = this.buffer.subarray(bodyStart, bodyStart + length)
      this.buffer = this.buffer.subarray(bodyStart + length)
      try {
        this.handleMessage(JSON.parse(body.toString('utf8')) as JsonRpcMessage)
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error)
        this.logger.error(`Unable to parse Lean response: ${message}`)
      }
    }
  }

  private handleMessage(message: JsonRpcMessage) {
    if (message.id === undefined) {
      if (message.method) this.emitNotification(message.method, message.params)
      return
    }

    if (message.method) {
      this.handleServerRequest(message.id, message.method, message.params)
      return
    }

    const pending = this.takePending(message.id)
    if (!pending) return
    if (message.error) pending.reject(new Error(message.error.message ?? 'Lean request failed'))
    else pending.resolve(message.result)
  }

  private handleServerRequest(id: number, method: string, params: unknown) {
    if (method === 'client/registerCapability'
      || method === 'workspace/semanticTokens/refresh'
      || method === 'workspace/inlayHint/refresh') {
      this.emitNotification(method, params)
      this.send({ jsonrpc: '2.0', id, result: null })
      return
    }
    if (method === 'workspace/applyEdit') {
      this.send({
        jsonrpc: '2.0',
        id,
        result: { applied: false, failureReason: 'Lean Mobile is read-only' }
      })
      return
    }
    this.send({
      jsonrpc: '2.0',
      id,
      error: { code: -32601, message: `Unsupported client request: ${method}` }
    })
  }

  private emitNotification(method: string, params: unknown) {
    for (const listener of this.notificationListeners) {
      try {
        listener({ method, params })
      } catch (error) {
        this.logger.error(error)
      }
    }
  }

  private takePending(id: number) {
    const pending = this.pending.get(id)
    if (!pending) return null
    this.pending.delete(id)
    clearTimeout(pending.timeout)
    pending.removeAbortListener?.()
    return pending
  }

  private failAll(error: Error) {
    for (const pending of this.pending.values()) {
      clearTimeout(pending.timeout)
      pending.removeAbortListener?.()
      pending.reject(error)
    }
    this.pending.clear()
  }
}

function abortError(method: string) {
  return new DOMException(`Lean request aborted: ${method}`, 'AbortError')
}

interface HoverResult {
  contents?: string | { value?: string } | Array<string | { value?: string }>
  range?: unknown
}

export function hoverText(result: unknown) {
  if (!isObject(result) || !('contents' in result)) return null
  const { contents } = result as HoverResult
  if (typeof contents === 'string') return contents
  if (Array.isArray(contents)) return contents.map(markedStringText).filter(Boolean).join('\n\n')
  if (contents && typeof contents.value === 'string') return contents.value
  return null
}

export function hoverRange(result: unknown) {
  if (!isObject(result) || !isObject(result.range)) return null
  const start = lspPosition(result.range.start)
  const end = lspPosition(result.range.end)
  return start && end ? { start, end } satisfies Range : null
}

function lspPosition(value: unknown): Position | null {
  if (!isObject(value)) return null
  const { line, character } = value
  if (!Number.isInteger(line) || Number(line) < 0) return null
  if (!Number.isInteger(character) || Number(character) < 0) return null
  return { line: Number(line), character: Number(character) }
}

function markedStringText(value: string | { value?: string }) {
  if (typeof value === 'string') return value
  return typeof value.value === 'string' ? value.value : ''
}

function isObject(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null
}
