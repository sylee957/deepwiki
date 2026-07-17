import { useLayoutEffect, useRef } from 'react'
import { basicSetup } from 'codemirror'
import { EditorSelection, EditorState, StateEffect, StateField } from '@codemirror/state'
import { Decoration, EditorView, scrollPastEnd, type DecorationSet } from '@codemirror/view'

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
        lspHoverRangeField,
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
        selection: EditorSelection.cursor(selection)
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
    color: '#e5e7eb',
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
    color: '#e5e7eb',
    WebkitTextFillColor: '#e5e7eb'
  },
  '.cm-line': {
    padding: '0 2rem 0 0.75rem',
    color: '#e5e7eb',
    WebkitTextFillColor: '#e5e7eb'
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
    borderLeftColor: '#93c5fd',
    borderLeftWidth: '2px'
  },
  '.cm-lsp-hover-range': {
    backgroundColor: 'rgba(96, 165, 250, 0.28)',
    borderBottom: '1px solid rgba(147, 197, 253, 0.9)'
  },
  '&.cm-focused': {
    outline: 'none'
  }
}, { dark: true })

const setLspHoverRange = StateEffect.define<{ from: number; to: number } | null>()

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

function sourceOffset(editor: EditorView, position: SourcePosition) {
  const lineNumber = Math.max(1, Math.min(position.line + 1, editor.state.doc.lines))
  const line = editor.state.doc.line(lineNumber)
  return Math.min(line.to, line.from + position.character)
}
