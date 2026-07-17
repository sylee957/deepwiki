export interface SemanticTokenLegend {
  tokenTypes: string[]
  tokenModifiers: string[]
}

export interface SemanticToken {
  line: number
  character: number
  length: number
  type: string
  modifiers: string[]
}

export interface SemanticTokensPayload {
  legend: SemanticTokenLegend
  data: number[]
}

export function semanticTokensPayload(
  result: unknown,
  legend: SemanticTokenLegend
): SemanticTokensPayload {
  const data = semanticTokenData(result)
  decodeSemanticTokens(data, legend)
  return {
    legend: {
      tokenTypes: [...legend.tokenTypes],
      tokenModifiers: [...legend.tokenModifiers]
    },
    data
  }
}

export function decodeSemanticTokens(
  data: unknown,
  legend: SemanticTokenLegend
): SemanticToken[] {
  if (!Array.isArray(data)) throw new Error('Invalid semantic token data from Lean')
  if (data.length % 5 !== 0) throw new Error('Invalid semantic token data length from Lean')

  const tokens: SemanticToken[] = []
  let line = 0
  let character = 0
  for (let index = 0; index < data.length; index += 5) {
    const deltaLine = semanticTokenInteger(data[index], 'line delta')
    const deltaStart = semanticTokenInteger(data[index + 1], 'character delta')
    const length = semanticTokenInteger(data[index + 2], 'length')
    const typeIndex = semanticTokenInteger(data[index + 3], 'type')
    const modifierBits = semanticTokenInteger(data[index + 4], 'modifiers')
    if (length === 0) throw new Error('Semantic tokens must have a positive length')
    if (modifierBits > 0xffff_ffff) throw new Error('Invalid semantic token modifier bitset from Lean')

    line = safeSemanticTokenAdd(line, deltaLine)
    character = deltaLine === 0 ? safeSemanticTokenAdd(character, deltaStart) : deltaStart
    const type = legend.tokenTypes[typeIndex]
    if (type === undefined) throw new Error(`Unknown semantic token type index from Lean: ${typeIndex}`)
    const modifiers = legend.tokenModifiers.slice(0, 32).filter((_, modifierIndex) =>
      Math.floor(modifierBits / 2 ** modifierIndex) % 2 === 1
    )
    tokens.push({ line, character, length, type, modifiers })
  }
  return tokens
}

function semanticTokenData(result: unknown) {
  if (result === null) return []
  if (!isObject(result) || !Array.isArray(result.data)) {
    throw new Error('Invalid semantic token response from Lean')
  }
  return [...result.data]
}

function semanticTokenInteger(value: unknown, field: string) {
  if (!Number.isSafeInteger(value) || Number(value) < 0) {
    throw new Error(`Invalid semantic token ${field} from Lean`)
  }
  return Number(value)
}

function safeSemanticTokenAdd(left: number, right: number) {
  const result = left + right
  if (!Number.isSafeInteger(result)) throw new Error('Semantic token position is too large')
  return result
}

function isObject(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null
}
