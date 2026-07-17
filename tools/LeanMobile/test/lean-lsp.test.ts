import assert from 'node:assert/strict'
import { test } from 'bun:test'
import {
  highlightRanges,
  hoverRange,
  hoverText,
  plainGoalText,
  plainTermGoal
} from '../src/lean-lsp.ts'

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

test('highlightRanges keeps only valid LSP ranges', () => {
  const range = { start: { line: 2, character: 1 }, end: { line: 2, character: 5 } }
  assert.deepEqual(highlightRanges([{ kind: 1, range }, { range: { start: range.start } }, null]), [range])
  assert.deepEqual(highlightRanges(null), [])
})

test('plain goals normalize Lean-specific goal responses', () => {
  const range = { start: { line: 4, character: 2 }, end: { line: 4, character: 8 } }
  assert.equal(plainGoalText({ rendered: '```lean\n⊢ True\n```', goals: ['⊢ True'] }), '```lean\n⊢ True\n```')
  assert.equal(plainGoalText({ goals: [] }), null)
  assert.deepEqual(plainTermGoal({ goal: '⊢ Nat', range }), { goal: '⊢ Nat', range })
  assert.equal(plainTermGoal({ goal: '⊢ Nat', range: { start: range.start } }), null)
})
