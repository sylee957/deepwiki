import assert from 'node:assert/strict'
import { test } from 'bun:test'
import { hoverText } from '../src/lean-lsp.ts'

test('hoverText normalizes LSP hover formats', () => {
  assert.equal(hoverText(null), null)
  assert.equal(hoverText({ contents: 'plain' }), 'plain')
  assert.equal(hoverText({ contents: { kind: 'markdown', value: '**type**' } }), '**type**')
  assert.equal(
    hoverText({ contents: [{ language: 'lean', value: '#check Nat' }, 'documentation'] }),
    '#check Nat\n\ndocumentation'
  )
})
