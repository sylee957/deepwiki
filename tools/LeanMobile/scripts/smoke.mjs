import assert from 'node:assert/strict'
import path from 'node:path'
import { fileURLToPath } from 'node:url'
import { createLeanMobileServer } from '../src/server.mjs'

const toolRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..')
const repositoryRoot = path.resolve(toolRoot, '../..')
const { server } = await createLeanMobileServer({ repositoryRoot })

try {
  await new Promise((resolve, reject) => {
    server.once('error', reject)
    server.listen(0, '127.0.0.1', resolve)
  })
  const address = server.address()
  const base = `http://127.0.0.1:${address.port}`

  const treeResponse = await fetch(`${base}/api/tree`)
  assert.equal(treeResponse.status, 200)
  const treeBody = await treeResponse.json()
  assert.equal(treeBody.tree.some(node => node.name === 'DeepWiki'), true)
  assert.equal(treeBody.tree.some(node => node.name === '.git'), false)

  const fileResponse = await fetch(`${base}/api/file?path=${encodeURIComponent('DeepWiki/Algebra/GcdBasics.lean')}`)
  assert.equal(fileResponse.status, 200)
  const fileBody = await fileResponse.json()
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
  const hoverBody = await hoverResponse.json()
  assert.equal(typeof hoverBody.hover, 'string')
  assert.match(hoverBody.hover, /IsGCD/)

  console.log(`Smoke test passed: ${hoverBody.hover.split('\n')[0]}`)
} finally {
  await new Promise(resolve => server.close(resolve))
}
