import { useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState } from 'react'
import { createRoot } from 'react-dom/client'
import { hotkeysCoreFeature, syncDataLoaderFeature, type Updater } from '@headless-tree/core'
import { useTree } from '@headless-tree/react'
import Markdown, { type Components } from 'react-markdown'
import { BrowserRouter, Route, Routes, useNavigate, useParams, useSearchParams } from 'react-router'
import { SourceViewer } from './SourceViewer.tsx'

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
}

const emptyHover: HoverState = { open: false, loading: false, message: '', content: '', range: null }

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
  const [hoverInset, setHoverInset] = useState(0)
  const hoverPanel = useRef<HTMLElement>(null)
  const fileRequest = useRef(0)
  const hoverRequest = useRef(0)

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

  const requestHover = useCallback(async (filePath: string, position: Position) => {
    const requestId = ++hoverRequest.current
    setHover({ open: true, loading: true, message: 'Asking Lean…', content: '', range: null })
    try {
      const result = await api<{ hover: string | null; range: SourceRange | null }>('/api/hover', {
        method: 'POST',
        body: JSON.stringify({ path: filePath, position })
      })
      if (requestId !== hoverRequest.current) return
      setHover({
        open: true,
        loading: false,
        message: result.hover ? '' : 'No Lean information at this position.',
        content: result.hover ?? '',
        range: result.range
      })
    } catch (error) {
      if (requestId !== hoverRequest.current) return
      setHover({ open: true, loading: false, message: errorMessage(error), content: '', range: null })
    }
  }, [])

  const loadFile = useCallback(async (filePath: string) => {
    const requestId = ++fileRequest.current
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
    } catch (error) {
      if (requestId !== fileRequest.current) return
      setSourceStatus(errorMessage(error))
    }
  }, [])

  useEffect(() => {
    if (!routePath) {
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
  }, [loadFile, path, requestHover, routePath, routePosition?.character, routePosition?.line, sourcePath, sourceStatus])

  const openFile = useCallback((filePath: string, position?: Position) => {
    navigate(viewerLocation(filePath, position), { replace: routePath === filePath })
  }, [navigate, routePath])

  const selectPosition = (position: Position) => {
    if (!path) return
    navigate(viewerLocation(path, position), { replace: true })
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
      openFile(definition.path, definition.position)
    } catch (error) {
      setHover({ open: true, loading: false, message: errorMessage(error), content: '', range: null })
    }
  }

  const closeHover = () => {
    hoverRequest.current += 1
    setHover(emptyHover)
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
          bottomInset={hoverInset}
          onSelect={selectPosition}
        />
      </section>
    </main>

    {hover.open && <section id="hover-panel" ref={hoverPanel} aria-live="polite">
      <div className="panel-heading">
        <strong>Lean hover</strong>
        <button className="icon-button" aria-label="Close hover" onClick={closeHover}>×</button>
      </div>
      {(hover.loading || hover.message) && <div className="status">{hover.message}</div>}
      {hover.content && <div id="hover-content"><Markdown components={markdownComponents}>{hover.content}</Markdown></div>}
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
