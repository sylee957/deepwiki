import assert from 'node:assert/strict'
import path from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'
import { createLeanMobileApp } from '../src/server.ts'
import {
  decodeSemanticTokens,
  type SemanticTokensPayload
} from '../src/semantic-tokens.ts'

const toolRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..')
const repositoryRoot = path.resolve(toolRoot, '../..')
const app = await createLeanMobileApp({ repositoryRoot })
const server = Bun.serve({ hostname: '127.0.0.1', port: 0, fetch: app.fetch })

try {
  const base = server.url.origin

  const indexResponse = await fetch(base)
  assert.equal(indexResponse.status, 200)
  assert.match(indexResponse.headers.get('content-security-policy') ?? '', /style-src 'self' 'unsafe-inline'/)
  assert.match(await indexResponse.text(), /id="root"/)

  const routedIndexResponse = await fetch(
    `${base}/file/DeepWiki/Algebra/GcdBasics.lean?line=14&character=6`,
    { headers: { Accept: 'text/html' } }
  )
  assert.equal(routedIndexResponse.status, 200)
  assert.match(routedIndexResponse.headers.get('content-type') ?? '', /text\/html/)
  assert.match(await routedIndexResponse.text(), /id="root"/)

  const fileRootResponse = await fetch(`${base}/file`, { headers: { Accept: 'text/html' } })
  assert.equal(fileRootResponse.status, 200)
  assert.match(fileRootResponse.headers.get('content-type') ?? '', /text\/html/)

  const missingApiResponse = await fetch(`${base}/api/missing`, { headers: { Accept: 'text/html' } })
  assert.equal(missingApiResponse.status, 404)
  assert.match(missingApiResponse.headers.get('content-type') ?? '', /application\/json/)

  const bundleResponse = await fetch(`${base}/app.js`)
  assert.equal(bundleResponse.status, 200)
  assert.match(bundleResponse.headers.get('content-type') ?? '', /javascript/)

  const treeResponse = await fetch(`${base}/api/tree`)
  assert.equal(treeResponse.status, 200)
  const treeBody = await treeResponse.json() as { tree: Array<{ name: string }> }
  assert.equal(treeBody.tree.some(node => node.name === 'DeepWiki'), true)
  assert.equal(treeBody.tree.some(node => node.name === '.git'), false)

  const fileResponse = await fetch(`${base}/api/file?path=${encodeURIComponent('DeepWiki/Algebra/GcdBasics.lean')}`)
  assert.equal(fileResponse.status, 200)
  const fileBody = await fileResponse.json() as { text: string }
  assert.match(fileBody.text, /def IsGCD/)

  const traversalResponse = await fetch(`${base}/api/file?path=${encodeURIComponent('../lakefile.toml')}`)
  assert.equal(traversalResponse.status, 403)

  const mutationResponse = await fetch(`${base}/api/file`, { method: 'PUT', body: 'forbidden' })
  assert.equal(mutationResponse.status, 405)

  const eventResponse = await fetch(`${base}/api/events`)
  assert.equal(eventResponse.status, 200)
  assert.match(eventResponse.headers.get('content-type') ?? '', /text\/event-stream/)
  assert.ok(eventResponse.body)
  const eventReader = eventResponse.body.getReader()
  const progressEvent = waitForServerEvent(eventReader, 'lean-progress')

  const leanNotifications: string[] = []
  const unsubscribe = app.lean.onNotification(notification => leanNotifications.push(notification.method))
  const hoverResponse = await fetch(`${base}/api/hover`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      path: 'DeepWiki/Algebra/GcdBasics.lean',
      position: { line: 17, character: 9 }
    })
  })
  assert.equal(hoverResponse.status, 200)
  const hoverBody = await hoverResponse.json() as {
    hover: unknown
    range: { start?: { line?: unknown; character?: unknown }; end?: { line?: unknown; character?: unknown } } | null
    highlights: Array<{ start?: { line?: unknown }; end?: { line?: unknown } }>
    goals: string | null
    termGoal: { goal?: unknown } | null
  }
  assert.equal(typeof hoverBody.hover, 'string')
  assert.match(String(hoverBody.hover), /IsGCD/)
  assert.equal(Number.isInteger(hoverBody.range?.start?.line), true)
  assert.equal(Number.isInteger(hoverBody.range?.start?.character), true)
  assert.equal(Number.isInteger(hoverBody.range?.end?.line), true)
  assert.equal(Number.isInteger(hoverBody.range?.end?.character), true)
  assert.equal(hoverBody.highlights.length > 0, true)
  assert.equal(typeof hoverBody.termGoal?.goal, 'string')

  const goalResponse = await fetch(`${base}/api/hover`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      path: 'DeepWiki/Algebra/GcdBasics.lean',
      position: { line: 94, character: 8 }
    })
  })
  assert.equal(goalResponse.status, 200)
  const goalBody = await goalResponse.json() as { goals: string | null }
  assert.match(goalBody.goals ?? '', /⊢ gcd/)

  let semanticBody: (SemanticTokensPayload & { path: string }) | null = null
  let semanticTypes = new Set<string>()
  let semanticTokens = [] as ReturnType<typeof decodeSemanticTokens>
  for (let attempt = 0; attempt < 6; attempt += 1) {
    const semanticResponse = await fetch(`${base}/api/semantic-tokens`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ path: 'DeepWiki/Algebra/GcdBasics.lean' })
    })
    assert.equal(semanticResponse.status, 200)
    semanticBody = await semanticResponse.json() as SemanticTokensPayload & { path: string }
    semanticTokens = decodeSemanticTokens(semanticBody.data, semanticBody.legend)
    semanticTypes = new Set(semanticTokens.map(token => token.type))
    if (['keyword', 'variable', 'property'].every(type => semanticTypes.has(type))) break
    await Bun.sleep(250)
  }
  assert.equal(semanticBody?.path, 'DeepWiki/Algebra/GcdBasics.lean')
  assert.deepEqual(semanticTokens[0], {
    line: 0,
    character: 0,
    length: 6,
    type: 'keyword',
    modifiers: []
  })
  assert.equal(semanticTypes.has('keyword'), true)
  assert.equal(semanticTypes.has('variable'), true)
  assert.equal(semanticTypes.has('property'), true)
  assert.equal(leanNotifications.includes('$/lean/fileProgress'), true)
  const progress = JSON.parse(await progressEvent) as { path?: string; state?: string }
  assert.equal(progress.path, 'DeepWiki/Algebra/GcdBasics.lean')
  assert.equal(['processing', 'ready'].includes(progress.state ?? ''), true)
  await eventReader.cancel()
  unsubscribe()

  const fileUri = pathToFileURL(path.join(repositoryRoot, 'DeepWiki/Algebra/GcdBasics.lean')).href
  const cancellation = new AbortController()
  const cancelledRequest = app.lean.request('textDocument/documentSymbol', {
    textDocument: { uri: fileUri }
  }, 60_000, cancellation.signal)
  cancellation.abort()
  await assert.rejects(cancelledRequest, error => error instanceof DOMException && error.name === 'AbortError')

  const secondFilePath = path.join(repositoryRoot, 'DeepWiki/Algebra.lean')
  const secondFileText = await Bun.file(secondFilePath).text()
  const firstFilePath = path.join(repositoryRoot, 'DeepWiki/Algebra/GcdBasics.lean')
  const [concurrentCaret] = await Promise.all([
    app.lean.caretInfo(firstFilePath, fileBody.text, { line: 17, character: 9 }),
    app.lean.hover(secondFilePath, secondFileText, { line: 0, character: 7 })
  ])
  assert.match(JSON.stringify(concurrentCaret.hover), /IsGCD/)

  console.log(`Smoke test passed: ${String(hoverBody.hover).split('\n')[0]}`)
} finally {
  server.stop(true)
  await app.lean.stop()
}

async function waitForServerEvent(
  reader: ReadableStreamDefaultReader<Uint8Array>,
  eventName: string
) {
  const decoder = new TextDecoder()
  let buffer = ''
  const read = async () => {
    while (true) {
      const result = await reader.read()
      if (result.done) throw new Error(`Event stream ended before ${eventName}`)
      buffer += decoder.decode(result.value, { stream: true })
      const records = buffer.split('\n\n')
      buffer = records.pop() ?? ''
      for (const record of records) {
        const lines = record.split('\n')
        if (lines.includes(`event: ${eventName}`)) {
          const data = lines.find(line => line.startsWith('data: '))
          if (data) return data.slice('data: '.length)
        }
      }
    }
  }
  let timeout: ReturnType<typeof setTimeout> | undefined
  try {
    return await Promise.race([
      read(),
      new Promise<never>((_, reject) => {
        timeout = setTimeout(() => reject(new Error(`Timed out waiting for ${eventName}`)), 20_000)
      })
    ])
  } finally {
    if (timeout) clearTimeout(timeout)
  }
}
