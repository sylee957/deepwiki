import assert from 'node:assert/strict'
import { test } from 'bun:test'
import { hoverRange, hoverText } from '../src/lean-lsp.ts'

test('hoverText normalizes LSP hover formats', () => {
  assert.equal(hoverText(null), null)
  assert.equal(hoverText({ contents: 'plain' }), 'plain')
  assert.equal(hoverText({ contents: { kind: 'markdown', value: '**type**' } }), '**type**')
  assert.equal(
    hoverText({ contents: [{ language: 'lean', value: '#check Nat' }, 'documentation'] }),
    '#check Nat\n\ndocumentation'
  )
})

test('hoverRange validates LSP source ranges', () => {
  const range = { start: { line: 3, character: 4 }, end: { line: 3, character: 9 } }
  assert.deepEqual(hoverRange({ contents: 'type', range }), range)
  assert.equal(hoverRange({ contents: 'type', range: { start: range.start } }), null)
  assert.equal(hoverRange({ contents: 'type', range: { start: { line: -1, character: 0 }, end: range.end } }), null)
})
