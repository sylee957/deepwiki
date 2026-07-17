import assert from 'node:assert/strict'
import { test } from 'bun:test'
import {
  highlightRanges,
  hoverRange,
  hoverText,
  plainGoalText,
  plainTermGoal,
  semanticTokenLegendFromInitialize
} from '../src/lean-lsp.ts'
import { decodeSemanticTokens, semanticTokensPayload } from '../src/semantic-tokens.ts'

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

test('semantic token legend comes from the Lean initialize response', () => {
  const initializeResult = {
    capabilities: {
      semanticTokensProvider: {
        legend: {
          tokenTypes: ['property', 'keyword'],
          tokenModifiers: ['readonly', 'deprecated']
        },
        full: true
      }
    }
  }
  assert.deepEqual(semanticTokenLegendFromInitialize(initializeResult), {
    tokenTypes: ['property', 'keyword'],
    tokenModifiers: ['readonly', 'deprecated']
  })
  assert.equal(semanticTokenLegendFromInitialize({ capabilities: {} }), null)
  assert.equal(semanticTokenLegendFromInitialize({
    capabilities: { semanticTokensProvider: { legend: { tokenTypes: [1], tokenModifiers: [] } } }
  }), null)
})

test('semantic tokens decode relative UTF-16 positions with the advertised legend', () => {
  const legend = {
    tokenTypes: ['property', 'keyword'],
    tokenModifiers: ['readonly', 'deprecated']
  }
  assert.deepEqual(decodeSemanticTokens([
    0, 2, 4, 1, 2,
    0, 6, 3, 0, 1,
    2, 1, 5, 1, 0
  ], legend), [
    { line: 0, character: 2, length: 4, type: 'keyword', modifiers: ['deprecated'] },
    { line: 0, character: 8, length: 3, type: 'property', modifiers: ['readonly'] },
    { line: 2, character: 1, length: 5, type: 'keyword', modifiers: [] }
  ])
})

test('semantic token payload stays compact and validates Lean data', () => {
  const legend = { tokenTypes: ['keyword'], tokenModifiers: [] }
  assert.deepEqual(semanticTokensPayload({ resultId: 'unused', data: [0, 0, 6, 0, 0] }, legend), {
    legend,
    data: [0, 0, 6, 0, 0]
  })
  assert.deepEqual(semanticTokensPayload(null, legend), { legend, data: [] })

  assert.throws(() => decodeSemanticTokens([0], legend), /data length/)
  assert.throws(() => decodeSemanticTokens([0, -1, 1, 0, 0], legend), /character delta/)
  assert.throws(() => decodeSemanticTokens([0, 0, 1.5, 0, 0], legend), /length/)
  assert.throws(() => decodeSemanticTokens([0, 0, 0, 0, 0], legend), /positive length/)
  assert.throws(() => decodeSemanticTokens([0, 0, 1, 1, 0], legend), /type index/)
  assert.throws(() => decodeSemanticTokens([0, 0, 1, 0, 0x1_0000_0000], legend), /bitset/)
})
