import { spawn } from 'node:child_process'
import { pathToFileURL } from 'node:url'

export class LeanLanguageServer {
  constructor(root, { logger = console } = {}) {
    this.root = root
    this.logger = logger
    this.process = null
    this.buffer = Buffer.alloc(0)
    this.nextId = 1
    this.pending = new Map()
    this.documents = new Map()
    this.ready = null
  }

  async start() {
    if (this.ready) return this.ready
    this.ready = this.#start()
    try {
      await this.ready
    } catch (error) {
      this.ready = null
      throw error
    }
  }

  async #start() {
    this.process = spawn('lake', ['env', 'lean', '--server'], {
      cwd: this.root,
      stdio: ['pipe', 'pipe', 'pipe']
    })

    this.process.stdout.on('data', chunk => this.#receive(chunk))
    this.process.stderr.on('data', chunk => {
      const message = chunk.toString('utf8').trim()
      if (message) this.logger.error(`[lean] ${message}`)
    })
    this.process.on('error', error => this.#failAll(error))
    this.process.on('exit', (code, signal) => {
      this.#failAll(new Error(`Lean language server exited (${signal ?? code})`))
      this.process = null
      this.ready = null
      this.documents.clear()
    })

    const rootUri = pathToFileURL(this.root).href
    await this.request('initialize', {
      processId: process.pid,
      clientInfo: { name: 'DeepWiki Lean Mobile', version: '0.1.0' },
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

  async hover(absolutePath, text, position) {
    await this.#openDocument(absolutePath, text)
    return this.request('textDocument/hover', {
      textDocument: { uri: pathToFileURL(absolutePath).href },
      position
    }, 60_000)
  }

  async definition(absolutePath, text, position) {
    await this.#openDocument(absolutePath, text)
    return this.request('textDocument/definition', {
      textDocument: { uri: pathToFileURL(absolutePath).href },
      position
    }, 60_000)
  }

  async #openDocument(absolutePath, text) {
    await this.start()
    const uri = pathToFileURL(absolutePath).href
    const previous = this.documents.get(uri)
    if (previous?.text === text) return

    if (!previous) {
      this.documents.set(uri, { text, version: 1 })
      this.notify('textDocument/didOpen', {
        textDocument: { uri, languageId: 'lean4', version: 1, text }
      })
      return
    }

    const version = previous.version + 1
    this.documents.set(uri, { text, version })
    this.notify('textDocument/didChange', {
      textDocument: { uri, version },
      contentChanges: [{ text }]
    })
  }

  request(method, params, timeoutMs = 30_000) {
    if (!this.process) return Promise.reject(new Error('Lean language server is not running'))
    const id = this.nextId++
    return new Promise((resolve, reject) => {
      const timeout = setTimeout(() => {
        this.pending.delete(id)
        reject(new Error(`Lean request timed out: ${method}`))
      }, timeoutMs)
      this.pending.set(id, { resolve, reject, timeout })
      this.#send({ jsonrpc: '2.0', id, method, params })
    })
  }

  notify(method, params) {
    if (!this.process) return
    this.#send({ jsonrpc: '2.0', method, params })
  }

  async stop() {
    if (!this.process) return
    const process = this.process
    try {
      await this.request('shutdown', null, 5_000)
    } catch {
      // If shutdown cannot complete, the process is terminated below.
    }
    if (this.process === process) {
      this.notify('exit', {})
      const forceStop = setTimeout(() => process.kill(), 1_000)
      forceStop.unref()
    }
  }

  #send(message) {
    const body = Buffer.from(JSON.stringify(message), 'utf8')
    const header = Buffer.from(`Content-Length: ${body.length}\r\n\r\n`, 'ascii')
    this.process.stdin.write(Buffer.concat([header, body]))
  }

  #receive(chunk) {
    this.buffer = Buffer.concat([this.buffer, chunk])
    while (true) {
      const headerEnd = this.buffer.indexOf('\r\n\r\n')
      if (headerEnd < 0) return
      const header = this.buffer.subarray(0, headerEnd).toString('ascii')
      const match = /Content-Length:\s*(\d+)/i.exec(header)
      if (!match) {
        this.#failAll(new Error('Invalid response from Lean language server'))
        return
      }
      const length = Number(match[1])
      const bodyStart = headerEnd + 4
      if (this.buffer.length < bodyStart + length) return
      const body = this.buffer.subarray(bodyStart, bodyStart + length)
      this.buffer = this.buffer.subarray(bodyStart + length)
      try {
        this.#handleMessage(JSON.parse(body.toString('utf8')))
      } catch (error) {
        this.logger.error(`Unable to parse Lean response: ${error.message}`)
      }
    }
  }

  #handleMessage(message) {
    if (message.id === undefined) return

    if (message.method) {
      this.#send({
        jsonrpc: '2.0',
        id: message.id,
        error: { code: -32601, message: `Unsupported client request: ${message.method}` }
      })
      return
    }

    const pending = this.pending.get(message.id)
    if (!pending) return
    clearTimeout(pending.timeout)
    this.pending.delete(message.id)
    if (message.error) pending.reject(new Error(message.error.message ?? 'Lean request failed'))
    else pending.resolve(message.result)
  }

  #failAll(error) {
    for (const pending of this.pending.values()) {
      clearTimeout(pending.timeout)
      pending.reject(error)
    }
    this.pending.clear()
  }
}

export function hoverText(result) {
  if (!result?.contents) return null
  const { contents } = result
  if (typeof contents === 'string') return contents
  if (Array.isArray(contents)) return contents.map(markedStringText).filter(Boolean).join('\n\n')
  if (typeof contents.value === 'string') return contents.value
  return null
}

function markedStringText(value) {
  if (typeof value === 'string') return value
  if (typeof value?.value === 'string') return value.value
  return ''
}
