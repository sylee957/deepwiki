import { StrictMode, useCallback, useEffect, useMemo, useState, type MouseEvent, type ReactNode } from 'react'
import { createRoot } from 'react-dom/client'

interface Position {
  line: number
  character: number
}

interface FileNode {
  name: string
  type: 'file'
  path: string
}

interface DirectoryNode {
  name: string
  type: 'directory'
  children: TreeNode[]
}

type TreeNode = FileNode | DirectoryNode

interface HoverState {
  open: boolean
  loading: boolean
  message: string
  content: string
}

const emptyHover: HoverState = { open: false, loading: false, message: '', content: '' }

function App() {
  const [tree, setTree] = useState<TreeNode[]>([])
  const [treeStatus, setTreeStatus] = useState('Loading files…')
  const [filter, setFilter] = useState('')
  const [sidebarOpen, setSidebarOpen] = useState(false)
  const [path, setPath] = useState<string | null>(null)
  const [source, setSource] = useState<string | null>(null)
  const [sourceStatus, setSourceStatus] = useState('')
  const [selected, setSelected] = useState<Position | null>(null)
  const [hover, setHover] = useState<HoverState>(emptyHover)

  useEffect(() => {
    void api<{ tree: TreeNode[]; count: number }>('/api/tree')
      .then(result => {
        setTree(result.tree)
        setTreeStatus(`${result.count} visible files`)
      })
      .catch((error: Error) => setTreeStatus(error.message))
  }, [])

  const requestHover = useCallback(async (filePath: string, position: Position) => {
    setHover({ open: true, loading: true, message: 'Asking Lean…', content: '' })
    try {
      const result = await api<{ hover: string | null }>('/api/hover', {
        method: 'POST',
        body: JSON.stringify({ path: filePath, position })
      })
      setHover({
        open: true,
        loading: false,
        message: result.hover ? '' : 'No Lean information at this position.',
        content: result.hover ?? ''
      })
    } catch (error) {
      setHover({ open: true, loading: false, message: errorMessage(error), content: '' })
    }
  }, [])

  const openFile = useCallback(async (filePath: string, position?: Position) => {
    setPath(filePath)
    setSource(null)
    setSourceStatus('Loading…')
    setSelected(null)
    setSidebarOpen(false)
    setHover(emptyHover)
    try {
      const result = await api<{ text: string }>(`/api/file?path=${encodeURIComponent(filePath)}`)
      setSource(result.text)
      setSourceStatus('')
      if (position) {
        setSelected(position)
        setTimeout(() => {
          document.querySelector(`[data-line="${position.line}"]`)?.scrollIntoView({ block: 'center' })
        })
        void requestHover(filePath, position)
      }
    } catch (error) {
      setSourceStatus(errorMessage(error))
    }
  }, [requestHover])

  const selectPosition = (position: Position) => {
    if (!path) return
    setSelected(position)
    void requestHover(path, position)
  }

  const goToDefinition = async () => {
    if (!path || !selected) return
    try {
      const result = await api<{ definitions: Array<{ path: string; position: Position }> }>('/api/definition', {
        method: 'POST',
        body: JSON.stringify({ path, position: selected })
      })
      const definition = result.definitions[0]
      if (!definition) {
        setHover(previous => ({ ...previous, open: true, message: 'No repository definition found.' }))
        return
      }
      await openFile(definition.path, definition.position)
    } catch (error) {
      setHover({ open: true, loading: false, message: errorMessage(error), content: '' })
    }
  }

  return <>
    <header>
      <button className="icon-button" id="tree-toggle" aria-label="Show repository files" onClick={() => setSidebarOpen(true)}>☰</button>
      <div className="title-wrap">
        <strong>Lean Mobile</strong>
        <span id="current-path" title={path ?? ''}>{path ?? 'Choose a file'}</span>
      </div>
      <button disabled={!selected} onClick={() => void goToDefinition()}>Definition</button>
    </header>

    <main>
      <aside id="sidebar" className={sidebarOpen ? 'open' : ''} aria-label="Repository files">
        <div className="sidebar-heading">
          <span>Repository</span>
          <button className="icon-button" id="close-sidebar" aria-label="Close repository files" onClick={() => setSidebarOpen(false)}>×</button>
        </div>
        <input
          id="file-filter"
          type="search"
          placeholder="Filter files…"
          autoComplete="off"
          value={filter}
          onChange={event => setFilter(event.target.value)}
        />
        <div className="status">{treeStatus}</div>
        <nav id="file-tree">
          <FileTree nodes={tree} filter={filter} activePath={path} onOpen={filePath => void openFile(filePath)} />
        </nav>
      </aside>

      <section id="viewer" aria-label="Source viewer">
        {!path && <div id="welcome">
          <h1>DeepWiki</h1>
          <p>Browse any repository file. Tap a Lean identifier to request its type and documentation.</p>
        </div>}
        {path && sourceStatus && <div className="status">{sourceStatus}</div>}
        {path && source !== null && <SourceView
          text={source}
          isLean={path.endsWith('.lean')}
          selected={selected}
          onSelect={selectPosition}
        />}
      </section>
    </main>

    {hover.open && <section id="hover-panel" aria-live="polite">
      <div className="panel-heading">
        <strong>Lean hover</strong>
        <button className="icon-button" aria-label="Close hover" onClick={() => setHover(emptyHover)}>×</button>
      </div>
      {(hover.loading || hover.message) && <div className="status">{hover.message}</div>}
      <pre id="hover-content">{hover.content}</pre>
    </section>}
  </>
}

function FileTree(props: {
  nodes: TreeNode[]
  filter: string
  activePath: string | null
  onOpen(path: string): void
}) {
  const filter = props.filter.trim().toLowerCase()
  const rendered = props.nodes.map(node => renderTreeNode(node, filter, props.activePath, props.onOpen))
  return <>{rendered}</>
}

function renderTreeNode(
  node: TreeNode,
  filter: string,
  activePath: string | null,
  onOpen: (path: string) => void
): ReactNode {
  if (node.type === 'file') {
    if (filter && !node.path.toLowerCase().includes(filter)) return null
    return <button
      key={node.path}
      className={`file-button${node.path === activePath ? ' active' : ''}`}
      title={node.path}
      onClick={() => onOpen(node.path)}
    >{node.name}</button>
  }

  const children = node.children
    .map(child => renderTreeNode(child, filter, activePath, onOpen))
    .filter(child => child !== null)
  if (children.length === 0) return null
  return <details key={node.name} open={filter ? true : undefined}>
    <summary>{node.name}</summary>
    {children}
  </details>
}

function SourceView(props: {
  text: string
  isLean: boolean
  selected: Position | null
  onSelect(position: Position): void
}) {
  const lines = useMemo(() => props.text.split('\n'), [props.text])
  return <div id="source">
    {lines.map((line, lineNumber) => <div
      className={`source-line${props.selected?.line === lineNumber ? ' selected' : ''}`}
      data-line={lineNumber}
      key={lineNumber}
      onClick={props.isLean ? event => selectFromPoint(event, lineNumber, props.onSelect) : undefined}
    >
      <span className="line-content">{props.isLean ? highlightLeanLine(line) : line || ' '}</span>
    </div>)}
  </div>
}

function selectFromPoint(event: MouseEvent<HTMLDivElement>, line: number, onSelect: (position: Position) => void) {
  const content = event.currentTarget.querySelector('.line-content')
  if (!content) return
  const selection = caretAtPoint(event.clientX, event.clientY)
  const character = selection ? textOffsetWithin(content, selection.node, selection.offset) : 0
  onSelect({ line, character })
}

function caretAtPoint(x: number, y: number) {
  const extendedDocument = document as Document & {
    caretPositionFromPoint?: (x: number, y: number) => { offsetNode: Node; offset: number } | null
    caretRangeFromPoint?: (x: number, y: number) => Range | null
  }
  const position = extendedDocument.caretPositionFromPoint?.(x, y)
  if (position) return { node: position.offsetNode, offset: position.offset }
  const range = extendedDocument.caretRangeFromPoint?.(x, y)
  return range ? { node: range.startContainer, offset: range.startOffset } : null
}

function textOffsetWithin(root: Element, targetNode: Node, targetOffset: number) {
  const range = document.createRange()
  range.selectNodeContents(root)
  try {
    range.setEnd(targetNode, targetOffset)
    return range.toString().length
  } catch {
    return 0
  }
}

function highlightLeanLine(line: string) {
  const pattern = /(\/\-.*|--.*|"(?:\\.|[^"\\])*"|\b(?:theorem|lemma|def|abbrev|example|instance|structure|class|inductive|namespace|section|variable|open|import|where|by|fun|let|in|if|then|else|match|with|do|return)\b|\b\d+(?:\.\d+)?\b)/g
  const output: ReactNode[] = []
  let offset = 0
  for (const match of line.matchAll(pattern)) {
    output.push(line.slice(offset, match.index))
    output.push(<span className={tokenClass(match[0])} key={`${match.index}-${match[0]}`}>{match[0]}</span>)
    offset = (match.index ?? 0) + match[0].length
  }
  output.push(line.slice(offset) || (line.length === 0 ? ' ' : ''))
  return output
}

function tokenClass(token: string) {
  if (token.startsWith('--') || token.startsWith('/-')) return 'tok-comment'
  if (token.startsWith('"')) return 'tok-string'
  if (/^\d/.test(token)) return 'tok-number'
  return 'tok-keyword'
}

async function api<T>(url: string, options?: RequestInit): Promise<T> {
  const response = await fetch(url, {
    headers: options?.body ? { 'Content-Type': 'application/json' } : undefined,
    ...options
  })
  const result = await response.json() as T & { error?: string }
  if (!response.ok) throw new Error(result.error ?? `Request failed (${response.status})`)
  return result
}

function errorMessage(error: unknown) {
  return error instanceof Error ? error.message : String(error)
}

const root = document.querySelector('#root')
if (!root) throw new Error('Missing React root')
createRoot(root).render(<StrictMode><App /></StrictMode>)
