import { useLayoutEffect, useRef } from 'react'
import { basicSetup } from 'codemirror'
import {
  EditorSelection,
  EditorState,
  StateEffect,
  StateField,
  type Range as CodeMirrorRange
} from '@codemirror/state'
import { Decoration, EditorView, scrollPastEnd, type DecorationSet } from '@codemirror/view'
import type { SemanticToken } from '../src/semantic-tokens.ts'

export interface SourcePosition {
  line: number
  character: number
}

export interface SourceRange {
  start: SourcePosition
  end: SourcePosition
}

export function SourceViewer(props: {
  documentKey: string
  text: string
  isLean: boolean
  selected: SourcePosition | null
  hoverRange: SourceRange | null
  highlightRanges: SourceRange[]
  semanticTokens: SemanticToken[]
  bottomInset: number
  onSelect(position: SourcePosition): void
}) {
  const parent = useRef<HTMLDivElement>(null)
  const view = useRef<EditorView | null>(null)
  const onSelect = useRef(props.onSelect)
  const isLean = useRef(props.isLean)
  const bottomInset = useRef(props.bottomInset)
  const currentDocumentKey = useRef(props.documentKey)
  onSelect.current = props.onSelect
  isLean.current = props.isLean
  bottomInset.current = props.bottomInset

  useLayoutEffect(() => {
    if (!parent.current) return
    const editor = new EditorView({
      parent: parent.current,
      doc: '',
      extensions: [
        basicSetup,
        scrollPastEnd(),
        EditorView.scrollMargins.of(() => ({ bottom: bottomInset.current })),
        EditorState.readOnly.of(true),
        EditorView.editable.of(false),
        EditorView.contentAttributes.of({
          tabindex: '0',
          autocapitalize: 'off',
          autocomplete: 'off',
          spellcheck: 'false'
        }),
        semanticTokenField,
        lspHoverRangeField,
        lspHighlightRangesField,
        EditorView.domEventHandlers({
          click(event, currentView) {
            if (!isLean.current) return false
            const position = currentView.posAtCoords({ x: event.clientX, y: event.clientY })
            if (position === null) return false
            currentView.dispatch({ selection: EditorSelection.cursor(position) })
            currentView.focus()
            const line = currentView.state.doc.lineAt(position)
            onSelect.current({ line: line.number - 1, character: position - line.from })
            return false
          }
        }),
        editorTheme
      ]
    })
    view.current = editor
    const resizeObserver = new ResizeObserver(() => editor.requestMeasure())
    resizeObserver.observe(parent.current)
    void document.fonts?.ready.then(() => editor.requestMeasure())
    return () => {
      resizeObserver.disconnect()
      view.current = null
      editor.destroy()
    }
  }, [])

  useLayoutEffect(() => {
    const editor = view.current
    if (!editor) return
    const changingDocument = currentDocumentKey.current !== props.documentKey

    if (changingDocument || editor.state.doc.toString() !== props.text) {
      const selection = changingDocument
        ? 0
        : Math.min(editor.state.selection.main.head, props.text.length)
      editor.dispatch({
        changes: { from: 0, to: editor.state.doc.length, insert: props.text },
        selection: EditorSelection.cursor(selection),
        effects: setSemanticTokenDecorations.of([])
      })
      currentDocumentKey.current = props.documentKey
      requestAnimationFrame(() => {
        if (view.current !== editor) return
        if (changingDocument) {
          editor.scrollDOM.scrollTop = 0
          editor.scrollDOM.scrollLeft = 0
        }
        editor.requestMeasure()
      })
    }
  }, [props.documentKey, props.text])

  useLayoutEffect(() => {
    const editor = view.current
    if (!editor || !props.selected) return
    const lineNumber = Math.min(props.selected.line + 1, editor.state.doc.lines)
    const line = editor.state.doc.line(Math.max(1, lineNumber))
    const position = Math.min(line.to, line.from + props.selected.character)
    if (editor.state.selection.main.empty && editor.state.selection.main.head === position) return
    editor.dispatch({
      selection: EditorSelection.cursor(position),
      effects: EditorView.scrollIntoView(position, { y: 'center' })
    })
    editor.focus()
  }, [props.selected])

  useLayoutEffect(() => {
    const editor = view.current
    if (!editor) return
    const start = props.hoverRange ? sourceOffset(editor, props.hoverRange.start) : null
    const end = props.hoverRange ? sourceOffset(editor, props.hoverRange.end) : null
    const range = start !== null && end !== null && start !== end
      ? { from: Math.min(start, end), to: Math.max(start, end) }
      : null
    editor.dispatch({ effects: setLspHoverRange.of(range) })
  }, [props.hoverRange])

  useLayoutEffect(() => {
    const editor = view.current
    if (!editor) return
    const hover = props.hoverRange
    const ranges = props.highlightRanges.flatMap(range => {
      if (hover && sameSourceRange(range, hover)) return []
      const start = sourceOffset(editor, range.start)
      const end = sourceOffset(editor, range.end)
      return start !== end ? [{ from: Math.min(start, end), to: Math.max(start, end) }] : []
    })
    ranges.sort((left, right) => left.from - right.from || left.to - right.to)
    editor.dispatch({ effects: setLspHighlightRanges.of(ranges) })
  }, [props.highlightRanges, props.hoverRange])

  useLayoutEffect(() => {
    const editor = view.current
    if (!editor) return
    const decorations = props.semanticTokens.flatMap(token => {
      const range = semanticTokenRange(editor, token)
      const tokenClass = semanticTokenClass(token.type)
      if (!range || !tokenClass) return []
      const modifierClasses = token.modifiers.flatMap(semanticTokenModifierClass)
      const className = ['cm-semantic-token', tokenClass, ...modifierClasses].join(' ')
      return [Decoration.mark({ class: className }).range(range.from, range.to)]
    })
    decorations.sort((left, right) => left.from - right.from || left.to - right.to)
    editor.dispatch({ effects: setSemanticTokenDecorations.of(decorations) })
  }, [props.documentKey, props.semanticTokens])

  useLayoutEffect(() => {
    const editor = view.current
    if (!editor) return
    editor.requestMeasure()
    if (props.bottomInset <= 0) return
    editor.dispatch({
      effects: EditorView.scrollIntoView(editor.state.selection.main.head, {
        y: 'nearest',
        yMargin: 8
      })
    })
  }, [props.bottomInset])

  return <div id="source" ref={parent} />
}

const editorTheme = EditorView.theme({
  '&': {
    height: '100%',
    backgroundColor: '#0b1020',
    color: '#cdd6f4',
    fontSize: '13px'
  },
  '.cm-scroller': {
    overflow: 'auto',
    fontFamily: 'ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace',
    lineHeight: '1.55',
    WebkitTextSizeAdjust: '100%'
  },
  '.cm-content': {
    padding: '0.75rem 0',
    caretColor: 'transparent',
    color: '#cdd6f4',
    WebkitTextFillColor: '#cdd6f4'
  },
  '.cm-line': {
    padding: '0 2rem 0 0.75rem',
    color: '#cdd6f4',
    WebkitTextFillColor: '#cdd6f4'
  },
  '.cm-gutters': {
    backgroundColor: '#0b1020',
    color: '#53627a',
    border: 'none',
    paddingTop: '0.75rem'
  },
  '.cm-activeLine, .cm-activeLineGutter': {
    backgroundColor: 'transparent'
  },
  '.cm-cursor': {
    borderLeftColor: '#89b4fa',
    borderLeftWidth: '2px'
  },
  '.cm-lsp-hover-range': {
    backgroundColor: 'rgba(137, 180, 250, 0.24)',
    borderBottom: '1px solid rgba(137, 180, 250, 0.85)'
  },
  '.cm-lsp-highlight-range': {
    backgroundColor: 'rgba(249, 226, 175, 0.13)',
    boxShadow: 'inset 0 -1px rgba(249, 226, 175, 0.65)'
  },
  '.cm-semantic-keyword, .cm-semantic-modifier, .cm-semantic-macro': {
    color: '#cba6f7',
    WebkitTextFillColor: '#cba6f7'
  },
  '.cm-semantic-variable, .cm-semantic-parameter, .cm-semantic-type-parameter': {
    color: '#cdd6f4',
    WebkitTextFillColor: '#cdd6f4'
  },
  '.cm-semantic-property, .cm-semantic-enum-member': {
    color: '#89dceb',
    WebkitTextFillColor: '#89dceb'
  },
  '.cm-semantic-function, .cm-semantic-method, .cm-semantic-event': {
    color: '#f9e2af',
    WebkitTextFillColor: '#f9e2af'
  },
  '.cm-semantic-namespace': {
    color: '#94e2d5',
    WebkitTextFillColor: '#94e2d5'
  },
  '.cm-semantic-type, .cm-semantic-class, .cm-semantic-enum, .cm-semantic-interface, .cm-semantic-struct': {
    color: '#94e2d5',
    WebkitTextFillColor: '#94e2d5'
  },
  '.cm-semantic-comment': {
    color: '#7f849c',
    WebkitTextFillColor: '#7f849c'
  },
  '.cm-semantic-string, .cm-semantic-regexp': {
    color: '#a6e3a1',
    WebkitTextFillColor: '#a6e3a1'
  },
  '.cm-semantic-number': {
    color: '#fab387',
    WebkitTextFillColor: '#fab387'
  },
  '.cm-semantic-operator': {
    color: '#cdd6f4',
    WebkitTextFillColor: '#cdd6f4'
  },
  '.cm-semantic-decorator': {
    color: '#f9e2af',
    WebkitTextFillColor: '#f9e2af'
  },
  '.cm-semantic-sorry-like': {
    color: '#f38ba8',
    WebkitTextFillColor: '#f38ba8',
    textDecoration: 'underline wavy rgba(243, 139, 168, 0.8)'
  },
  '.cm-semantic-deprecated': {
    textDecoration: 'line-through'
  },
  '&.cm-focused': {
    outline: 'none'
  }
}, { dark: true })

const setLspHoverRange = StateEffect.define<{ from: number; to: number } | null>()
const setLspHighlightRanges = StateEffect.define<Array<{ from: number; to: number }>>()
const setSemanticTokenDecorations = StateEffect.define<Array<CodeMirrorRange<Decoration>>>()

const semanticTokenField = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update(tokens, transaction) {
    tokens = tokens.map(transaction.changes)
    for (const effect of transaction.effects) {
      if (effect.is(setSemanticTokenDecorations)) return Decoration.set(effect.value, true)
    }
    return tokens
  },
  provide: field => EditorView.decorations.from(field)
})

const lspHoverRangeField = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update(ranges, transaction) {
    ranges = ranges.map(transaction.changes)
    for (const effect of transaction.effects) {
      if (effect.is(setLspHoverRange)) {
        return effect.value
          ? Decoration.set([Decoration.mark({ class: 'cm-lsp-hover-range' }).range(effect.value.from, effect.value.to)])
          : Decoration.none
      }
    }
    return ranges
  },
  provide: field => EditorView.decorations.from(field)
})

const lspHighlightRangesField = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update(ranges, transaction) {
    ranges = ranges.map(transaction.changes)
    for (const effect of transaction.effects) {
      if (effect.is(setLspHighlightRanges)) {
        return Decoration.set(effect.value.map(range =>
          Decoration.mark({ class: 'cm-lsp-highlight-range' }).range(range.from, range.to)
        ), true)
      }
    }
    return ranges
  },
  provide: field => EditorView.decorations.from(field)
})

function sourceOffset(editor: EditorView, position: SourcePosition) {
  const lineNumber = Math.max(1, Math.min(position.line + 1, editor.state.doc.lines))
  const line = editor.state.doc.line(lineNumber)
  return Math.min(line.to, line.from + position.character)
}

function sameSourceRange(left: SourceRange, right: SourceRange) {
  return left.start.line === right.start.line
    && left.start.character === right.start.character
    && left.end.line === right.end.line
    && left.end.character === right.end.character
}

function semanticTokenRange(editor: EditorView, token: SemanticToken) {
  if (!Number.isInteger(token.line) || token.line < 0 || token.line >= editor.state.doc.lines) return null
  if (!Number.isInteger(token.character) || token.character < 0) return null
  if (!Number.isInteger(token.length) || token.length <= 0) return null
  const line = editor.state.doc.line(token.line + 1)
  if (token.character + token.length > line.length) return null
  const from = line.from + token.character
  return { from, to: from + token.length }
}

function semanticTokenClass(type: string) {
  switch (type) {
    case 'keyword': return 'cm-semantic-keyword'
    case 'variable': return 'cm-semantic-variable'
    case 'property': return 'cm-semantic-property'
    case 'function': return 'cm-semantic-function'
    case 'namespace': return 'cm-semantic-namespace'
    case 'type': return 'cm-semantic-type'
    case 'class': return 'cm-semantic-class'
    case 'enum': return 'cm-semantic-enum'
    case 'interface': return 'cm-semantic-interface'
    case 'struct': return 'cm-semantic-struct'
    case 'typeParameter': return 'cm-semantic-type-parameter'
    case 'parameter': return 'cm-semantic-parameter'
    case 'enumMember': return 'cm-semantic-enum-member'
    case 'event': return 'cm-semantic-event'
    case 'method': return 'cm-semantic-method'
    case 'macro': return 'cm-semantic-macro'
    case 'modifier': return 'cm-semantic-modifier'
    case 'comment': return 'cm-semantic-comment'
    case 'string': return 'cm-semantic-string'
    case 'number': return 'cm-semantic-number'
    case 'regexp': return 'cm-semantic-regexp'
    case 'operator': return 'cm-semantic-operator'
    case 'decorator': return 'cm-semantic-decorator'
    case 'leanSorryLike': return 'cm-semantic-sorry-like'
    default: return null
  }
}

function semanticTokenModifierClass(modifier: string): string[] {
  return modifier === 'deprecated' ? ['cm-semantic-deprecated'] : []
}
