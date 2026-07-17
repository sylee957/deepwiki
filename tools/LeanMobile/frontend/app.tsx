import { useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState } from 'react'
import { createRoot } from 'react-dom/client'
import { hotkeysCoreFeature, syncDataLoaderFeature, type Updater } from '@headless-tree/core'
import { useTree } from '@headless-tree/react'
import Markdown, { type Components } from 'react-markdown'
import { BrowserRouter, Route, Routes, useNavigate, useParams, useSearchParams } from 'react-router'
import { SourceViewer } from './SourceViewer.tsx'
import {
  decodeSemanticTokens,
  type SemanticToken,
  type SemanticTokensPayload
} from '../src/semantic-tokens.ts'

interface Position {
  line: number
  character: number
}

interface SourceRange {
  start: Position
  end: Position
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
  range: SourceRange | null
  highlights: SourceRange[]
  goals: string
  termGoal: { goal: string; range: SourceRange } | null
  tab: 'hover' | 'goals'
}

type LeanProgressState = 'idle' | 'processing' | 'ready' | 'error' | 'offline'

interface LeanProgressEvent {
  path: string
  state: Exclude<LeanProgressState, 'idle' | 'offline'>
}

interface LeanSemanticRefreshEvent {
  path: string
}

const emptyHover: HoverState = {
  open: false,
  loading: false,
  message: '',
  content: '',
  range: null,
  highlights: [],
  goals: '',
  termGoal: null,
  tab: 'hover'
}

function App() {
  const navigate = useNavigate()
  const routePath = useParams()['*'] ?? null
  const [searchParameters] = useSearchParams()
  const routePosition = sourcePositionFrom(searchParameters)
  const [tree, setTree] = useState<TreeNode[]>([])
  const [treeStatus, setTreeStatus] = useState('Loading files…')
  const [filter, setFilter] = useState('')
  const [sidebarOpen, setSidebarOpen] = useState(false)
  const [path, setPath] = useState<string | null>(null)
  const [sourcePath, setSourcePath] = useState<string | null>(null)
  const [source, setSource] = useState<string | null>(null)
  const [sourceStatus, setSourceStatus] = useState('')
  const [selected, setSelected] = useState<Position | null>(null)
  const [hover, setHover] = useState<HoverState>(emptyHover)
  const [leanProgress, setLeanProgress] = useState<LeanProgressEvent | null>(null)
  const [leanEventsOnline, setLeanEventsOnline] = useState(false)
  const [semanticTokens, setSemanticTokens] = useState<SemanticToken[]>([])
  const [hoverInset, setHoverInset] = useState(0)
  const hoverPanel = useRef<HTMLElement>(null)
  const fileRequest = useRef(0)
  const hoverRequest = useRef(0)
  const hoverAbort = useRef<AbortController | null>(null)
  const definitionAbort = useRef<AbortController | null>(null)
  const semanticAbort = useRef<AbortController | null>(null)
  const semanticRequest = useRef(0)
  const semanticRequestPath = useRef<string | null>(null)
  const semanticTargetPath = useRef<string | null>(null)
  const semanticRefreshQueued = useRef(false)

  useLayoutEffect(() => {
    const panel = hoverPanel.current
    if (!panel) {
      setHoverInset(0)
      return
    }

    const measure = () => {
      const height = Math.ceil(panel.getBoundingClientRect().height)
      setHoverInset(current => current === height ? current : height)
    }
    measure()
    const observer = new ResizeObserver(measure)
    observer.observe(panel)
    return () => observer.disconnect()
  }, [hover.open])

  useEffect(() => {
    void api<{ tree: TreeNode[]; count: number }>('/api/tree')
      .then(result => {
        setTree(result.tree)
        setTreeStatus(`${result.count} visible files`)
      })
      .catch((error: Error) => setTreeStatus(error.message))
  }, [])

  const cancelSemanticTokens = useCallback(() => {
    semanticRequest.current += 1
    semanticRefreshQueued.current = false
    semanticTargetPath.current = null
    semanticRequestPath.current = null
    semanticAbort.current?.abort()
    semanticAbort.current = null
    setSemanticTokens([])
  }, [])

  const requestSemanticTokens = useCallback((filePath: string) => {
    const run = () => {
      if (semanticTargetPath.current !== filePath) return
      if (semanticAbort.current) {
        if (semanticRequestPath.current === filePath) semanticRefreshQueued.current = true
        return
      }

      const controller = new AbortController()
      const requestId = ++semanticRequest.current
      semanticAbort.current = controller
      semanticRequestPath.current = filePath
      void api<SemanticTokensPayload & { path: string }>('/api/semantic-tokens', {
        method: 'POST',
        body: JSON.stringify({ path: filePath }),
        signal: controller.signal
      }).then(result => {
        if (controller.signal.aborted || requestId !== semanticRequest.current) return
        if (semanticTargetPath.current !== filePath || result.path !== filePath) return
        setSemanticTokens(decodeSemanticTokens(result.data, result.legend))
      }).catch(error => {
        if (!isAbortError(error) && requestId === semanticRequest.current) {
          console.error('Semantic highlighting failed', error)
        }
      }).finally(() => {
        if (semanticAbort.current !== controller) return
        semanticAbort.current = null
        semanticRequestPath.current = null
        const repeat = semanticRefreshQueued.current && semanticTargetPath.current === filePath
        semanticRefreshQueued.current = false
        if (repeat) queueMicrotask(run)
      })
    }
    run()
  }, [])

  useEffect(() => {
    const events = new EventSource('/api/events')
    const receiveProgress = (event: MessageEvent<string>) => {
      try {
        const value: unknown = JSON.parse(event.data)
        if (!isLeanProgressEvent(value)) return
        setLeanProgress(value)
        if (value.state === 'ready' && semanticTargetPath.current === value.path) {
          requestSemanticTokens(value.path)
        }
      } catch {
        // Ignore malformed event data and keep the last valid state.
      }
    }
    const receiveSemanticRefresh = (event: MessageEvent<string>) => {
      try {
        const value: unknown = JSON.parse(event.data)
        if (!isLeanSemanticRefreshEvent(value)) return
        if (semanticTargetPath.current === value.path) requestSemanticTokens(value.path)
      } catch {
        // Ignore malformed refresh events; progress-ready and reconnect also retry.
      }
    }
    events.addEventListener('lean-progress', receiveProgress as EventListener)
    events.addEventListener('lean-semantic-refresh', receiveSemanticRefresh as EventListener)
    events.onopen = () => {
      setLeanEventsOnline(true)
      const filePath = semanticTargetPath.current
      if (filePath) requestSemanticTokens(filePath)
    }
    events.onerror = () => setLeanEventsOnline(false)
    return () => {
      events.removeEventListener('lean-progress', receiveProgress as EventListener)
      events.removeEventListener('lean-semantic-refresh', receiveSemanticRefresh as EventListener)
      events.close()
    }
  }, [requestSemanticTokens])

  const requestHover = useCallback(async (filePath: string, position: Position) => {
    hoverAbort.current?.abort()
    definitionAbort.current?.abort()
    const controller = new AbortController()
    hoverAbort.current = controller
    const requestId = ++hoverRequest.current
    setHover({ ...emptyHover, open: true, loading: true, message: 'Asking Lean…' })
    try {
      const result = await api<{
        hover: string | null
        range: SourceRange | null
        highlights: SourceRange[]
        goals: string | null
        termGoal: { goal: string; range: SourceRange } | null
      }>('/api/hover', {
        method: 'POST',
        body: JSON.stringify({ path: filePath, position }),
        signal: controller.signal
      })
      if (requestId !== hoverRequest.current) return
      const hasGoals = Boolean(result.goals || result.termGoal)
      setHover({
        open: true,
        loading: false,
        message: result.hover || hasGoals ? '' : 'No Lean information at this position.',
        content: result.hover ?? '',
        range: result.range,
        highlights: result.highlights,
        goals: result.goals ?? '',
        termGoal: result.termGoal,
        tab: result.hover ? 'hover' : hasGoals ? 'goals' : 'hover'
      })
    } catch (error) {
      if (isAbortError(error)) return
      if (requestId !== hoverRequest.current) return
      setHover({ ...emptyHover, open: true, message: errorMessage(error) })
    } finally {
      if (hoverAbort.current === controller) hoverAbort.current = null
    }
  }, [])

  const loadFile = useCallback(async (filePath: string) => {
    const requestId = ++fileRequest.current
    hoverAbort.current?.abort()
    definitionAbort.current?.abort()
    cancelSemanticTokens()
    hoverRequest.current += 1
    setPath(filePath)
    setSourcePath(filePath)
    setSource('')
    setSourceStatus('Loading…')
    setSelected(null)
    setSidebarOpen(false)
    setHover(emptyHover)
    try {
      const result = await api<{ text: string }>(`/api/file?path=${encodeURIComponent(filePath)}`)
      if (requestId !== fileRequest.current) return
      setSource(result.text)
      setSourceStatus('')
      if (filePath.endsWith('.lean')) {
        semanticTargetPath.current = filePath
        requestSemanticTokens(filePath)
      }
    } catch (error) {
      if (requestId !== fileRequest.current) return
      setSourceStatus(errorMessage(error))
    }
  }, [cancelSemanticTokens, requestSemanticTokens])

  useEffect(() => {
    if (!routePath) {
      hoverAbort.current?.abort()
      definitionAbort.current?.abort()
      cancelSemanticTokens()
      fileRequest.current += 1
      hoverRequest.current += 1
      setPath(null)
      setSourcePath(null)
      setSource('')
      setSourceStatus('')
      setSelected(null)
      setHover(emptyHover)
      return
    }

    if (routePath !== path) {
      void loadFile(routePath)
      return
    }

    if (sourcePath !== routePath || sourceStatus) return
    if (routePosition) {
      setSelected(routePosition)
      void requestHover(routePath, routePosition)
    } else {
      hoverRequest.current += 1
      setSelected(null)
      setHover(emptyHover)
    }
  }, [cancelSemanticTokens, loadFile, path, requestHover, routePath, routePosition?.character, routePosition?.line, sourcePath, sourceStatus])

  const openFile = useCallback((filePath: string, position?: Position) => {
    navigate(viewerLocation(filePath, position), { replace: routePath === filePath })
  }, [navigate, routePath])

  const selectPosition = (position: Position) => {
    if (!path) return
    navigate(viewerLocation(path, position), { replace: true })
  }

  const goToDefinition = async () => {
    if (!path || !selected) return
    definitionAbort.current?.abort()
    const controller = new AbortController()
    definitionAbort.current = controller
    try {
      const result = await api<{ definitions: Array<{ path: string; position: Position }> }>('/api/definition', {
        method: 'POST',
        body: JSON.stringify({ path, position: selected }),
        signal: controller.signal
      })
      const definition = result.definitions[0]
      if (!definition) {
        setHover(previous => ({ ...previous, open: true, message: 'No repository definition found.' }))
        return
      }
      openFile(definition.path, definition.position)
    } catch (error) {
      if (isAbortError(error)) return
      setHover({ ...emptyHover, open: true, message: errorMessage(error) })
    } finally {
      if (definitionAbort.current === controller) definitionAbort.current = null
    }
  }

  const closeHover = () => {
    hoverAbort.current?.abort()
    definitionAbort.current?.abort()
    hoverRequest.current += 1
    setHover(emptyHover)
  }

  useEffect(() => () => {
    hoverAbort.current?.abort()
    definitionAbort.current?.abort()
    semanticRequest.current += 1
    semanticTargetPath.current = null
    semanticAbort.current?.abort()
  }, [])

  const progressState: LeanProgressState = path?.endsWith('.lean')
    ? !leanEventsOnline ? 'offline' : leanProgress?.path === path ? leanProgress.state : 'idle'
    : 'idle'

  return <>
    <header>
      <button className="icon-button" id="tree-toggle" aria-label="Show repository files" onClick={() => setSidebarOpen(true)}>☰</button>
      <div className="title-wrap">
        <strong>Lean Mobile</strong>
        <span id="current-path" title={path ?? ''}>{path ?? 'Choose a file'}</span>
      </div>
      {path?.endsWith('.lean') && <LeanProgress state={progressState} />}
      <button disabled={!selected} onClick={() => void goToDefinition()}>Definition</button>
    </header>

    <main>
      {sidebarOpen && <button
        className="sidebar-backdrop"
        aria-label="Close repository files"
        onClick={() => setSidebarOpen(false)}
      />}
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
        {path && sourceStatus && <div className="status viewer-status">{sourceStatus}</div>}
        <SourceViewer
          documentKey={sourcePath ?? ''}
          text={source ?? ''}
          isLean={sourcePath?.endsWith('.lean') ?? false}
          selected={selected}
          hoverRange={hover.range}
          highlightRanges={hover.highlights}
          semanticTokens={semanticTokens}
          bottomInset={hoverInset}
          onSelect={selectPosition}
        />
      </section>
    </main>

    {hover.open && <section id="hover-panel" ref={hoverPanel} aria-live="polite">
      <div className="panel-heading">
        <div className="lean-panel-tabs" role="tablist" aria-label="Lean information">
          <button
            role="tab"
            aria-selected={hover.tab === 'hover'}
            className={hover.tab === 'hover' ? 'active' : ''}
            onClick={() => setHover(previous => ({ ...previous, tab: 'hover' }))}
          >Hover</button>
          <button
            role="tab"
            aria-selected={hover.tab === 'goals'}
            className={hover.tab === 'goals' ? 'active' : ''}
            onClick={() => setHover(previous => ({ ...previous, tab: 'goals' }))}
          >Goals</button>
        </div>
        <button className="icon-button" aria-label="Close hover" onClick={closeHover}>×</button>
      </div>
      {(hover.loading || hover.message) && <div className="status">{hover.message}</div>}
      {!hover.loading && !hover.message && hover.tab === 'hover' && <div id="hover-content" role="tabpanel">
        {hover.content
          ? <Markdown components={markdownComponents}>{hover.content}</Markdown>
          : <div className="status">No hover information at this position.</div>}
      </div>}
      {!hover.loading && !hover.message && hover.tab === 'goals' && <div id="goal-content" role="tabpanel">
        {hover.goals && <section>
          <h3>Tactic goals</h3>
          <Markdown components={markdownComponents}>{hover.goals}</Markdown>
        </section>}
        {hover.termGoal && <section>
          <h3>Expected type</h3>
          <pre><code>{hover.termGoal.goal}</code></pre>
        </section>}
        {!hover.goals && !hover.termGoal && <div className="status">No proof or term goal at this position.</div>}
      </div>}
    </section>}
  </>
}

function LeanProgress(props: { state: LeanProgressState }) {
  const labels: Record<LeanProgressState, string> = {
    idle: 'Lean idle',
    processing: 'Lean…',
    ready: 'Lean ready',
    error: 'Lean error',
    offline: 'Lean offline'
  }
  return <span className={`lean-progress ${props.state}`} role="status" title={labels[props.state]}>
    <span className="lean-progress-dot" aria-hidden="true" />
    <span className="lean-progress-label">{labels[props.state]}</span>
  </span>
}

function FileTree(props: {
  nodes: TreeNode[]
  filter: string
  activePath: string | null
  onOpen(path: string): void
}) {
  const filter = props.filter.trim().toLowerCase()
  const visibleNodes = useMemo(() => filterNodes(props.nodes, filter), [props.nodes, filter])
  return <HeadlessFileTree
    key={filter}
    nodes={visibleNodes}
    expandAll={Boolean(filter)}
    activePath={props.activePath}
    onOpen={props.onOpen}
  />
}

interface TreeItemData {
  name: string
  type: 'file' | 'directory'
  path?: string
  children: string[]
}

function HeadlessFileTree(props: {
  nodes: TreeNode[]
  expandAll: boolean
  activePath: string | null
  onOpen(path: string): void
}) {
  const items = useMemo(() => flattenTree(props.nodes), [props.nodes])
  const [expandedItems, setExpandedItems] = useState<string[]>(() => props.expandAll
    ? [...items.entries()].filter(([, item]) => item.type === 'directory').map(([id]) => id)
    : [])
  const [focusedItem, setFocusedItem] = useState<string | null>(null)
  const [, forceRender] = useState(0)
  const tree = useTree<TreeItemData>({
    rootItemId: '__root__',
    state: { expandedItems, focusedItem },
    setExpandedItems: updater => {
      setExpandedItems(current => applyUpdater(updater, current))
    },
    setFocusedItem: updater => {
      setFocusedItem(current => applyUpdater(updater, current))
    },
    getItemName: item => item.getItemData().name,
    isItemFolder: item => item.getItemData().type === 'directory',
    dataLoader: {
      getItem: itemId => items.get(itemId) ?? missingTreeItem(itemId),
      getChildren: itemId => items.get(itemId)?.children ?? []
    },
    onPrimaryAction: item => {
      const data = item.getItemData()
      if (data.type === 'file' && data.path) props.onOpen(data.path)
    },
    features: [syncDataLoaderFeature, hotkeysCoreFeature]
  })

  useEffect(() => {
    tree.rebuildTree()
    forceRender(revision => revision + 1)
  }, [items, tree])

  return <div {...tree.getContainerProps('Repository files')} className="tree-root">
    {tree.getItems().map(item => {
      const data = item.getItemData()
      const level = item.getItemMeta().level
      return <button
        key={item.getKey()}
        {...item.getProps()}
        className={`tree-item${data.path === props.activePath ? ' active' : ''}`}
        style={{ paddingInlineStart: `${0.35 + level * 1.15}rem` }}
        title={data.path ?? data.name}
      >
        <span className="tree-chevron" aria-hidden="true">
          {item.isFolder() ? (item.isExpanded() ? '▾' : '▸') : ''}
        </span>
        <span className="tree-name">{data.name}</span>
      </button>
    })}
  </div>
}

function filterNodes(nodes: TreeNode[], filter: string): TreeNode[] {
  if (!filter) return nodes
  return nodes.flatMap<TreeNode>(node => {
    if (node.type === 'file') return node.path.toLowerCase().includes(filter) ? [node] : []
    const children = filterNodes(node.children, filter)
    return children.length > 0 ? [{ ...node, children }] : []
  })
}

function flattenTree(nodes: TreeNode[]) {
  const items = new Map<string, TreeItemData>()
  const rootChildren: string[] = []
  items.set('__root__', { name: 'Repository', type: 'directory', children: rootChildren })

  const visit = (node: TreeNode, parentPath: string, parentChildren: string[]) => {
    const nodePath = parentPath ? `${parentPath}/${node.name}` : node.name
    const id = `${node.type}:${nodePath}`
    parentChildren.push(id)
    if (node.type === 'file') {
      items.set(id, { name: node.name, type: 'file', path: node.path, children: [] })
      return
    }

    const children: string[] = []
    items.set(id, { name: node.name, type: 'directory', path: nodePath, children })
    for (const child of node.children) visit(child, nodePath, children)
  }

  for (const node of nodes) visit(node, '', rootChildren)
  return items
}

function missingTreeItem(id: string): TreeItemData {
  return { name: id, type: 'file', children: [] }
}

function applyUpdater<T>(updater: Updater<T>, current: T) {
  return typeof updater === 'function' ? (updater as (value: T) => T)(current) : updater
}

const markdownComponents: Components = {
  a: ({ node: _node, ...props }) => <a {...props} target="_blank" rel="noreferrer" />
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

function isAbortError(error: unknown) {
  return error instanceof DOMException && error.name === 'AbortError'
}

function isLeanProgressEvent(value: unknown): value is LeanProgressEvent {
  if (typeof value !== 'object' || value === null) return false
  const event = value as Partial<LeanProgressEvent>
  return typeof event.path === 'string'
    && (event.state === 'processing' || event.state === 'ready' || event.state === 'error')
}

function isLeanSemanticRefreshEvent(value: unknown): value is LeanSemanticRefreshEvent {
  if (typeof value !== 'object' || value === null) return false
  return typeof (value as Partial<LeanSemanticRefreshEvent>).path === 'string'
}

function viewerLocation(path: string, position?: Position) {
  const pathname = `/file/${path.split('/').map(encodeURIComponent).join('/')}`
  const search = new URLSearchParams()
  if (position) {
    search.set('line', String(position.line))
    search.set('character', String(position.character))
  }
  return { pathname, search: search.size ? `?${search}` : '' }
}

function sourcePositionFrom(parameters: URLSearchParams): Position | null {
  const line = routeInteger(parameters.get('line'))
  const character = routeInteger(parameters.get('character'))
  return line === null || character === null ? null : { line, character }
}

function routeInteger(value: string | null) {
  if (value === null || !/^\d+$/.test(value)) return null
  const parsed = Number(value)
  return Number.isSafeInteger(parsed) ? parsed : null
}

const root = document.querySelector('#root')
if (!root) throw new Error('Missing React root')
createRoot(root).render(
  <BrowserRouter>
    <Routes>
      <Route path="/" element={<App />} />
      <Route path="/file/*" element={<App />} />
    </Routes>
  </BrowserRouter>
)
