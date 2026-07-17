import assert from 'node:assert/strict'
import path from 'node:path'
import { fileURLToPath } from 'node:url'
import { createLeanMobileApp } from '../src/server.ts'

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
  }
  assert.equal(typeof hoverBody.hover, 'string')
  assert.match(String(hoverBody.hover), /IsGCD/)
  assert.equal(Number.isInteger(hoverBody.range?.start?.line), true)
  assert.equal(Number.isInteger(hoverBody.range?.start?.character), true)
  assert.equal(Number.isInteger(hoverBody.range?.end?.line), true)
  assert.equal(Number.isInteger(hoverBody.range?.end?.character), true)

  console.log(`Smoke test passed: ${String(hoverBody.hover).split('\n')[0]}`)
} finally {
  server.stop(true)
  await app.lean.stop()
}
