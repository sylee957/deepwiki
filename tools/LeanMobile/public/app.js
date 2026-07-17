const state = {
  tree: [],
  path: null,
  text: '',
  selectedPosition: null,
  selectedLine: null
}

const elements = {
  sidebar: document.querySelector('#sidebar'),
  tree: document.querySelector('#file-tree'),
  treeStatus: document.querySelector('#tree-status'),
  filter: document.querySelector('#file-filter'),
  source: document.querySelector('#source'),
  welcome: document.querySelector('#welcome'),
  currentPath: document.querySelector('#current-path'),
  hoverPanel: document.querySelector('#hover-panel'),
  hoverStatus: document.querySelector('#hover-status'),
  hoverContent: document.querySelector('#hover-content'),
  definitionButton: document.querySelector('#definition-button')
}

document.querySelector('#tree-toggle').addEventListener('click', () => elements.sidebar.classList.add('open'))
document.querySelector('#close-sidebar').addEventListener('click', () => elements.sidebar.classList.remove('open'))
document.querySelector('#close-hover').addEventListener('click', closeHover)
elements.filter.addEventListener('input', renderTree)
elements.definitionButton.addEventListener('click', goToDefinition)

loadTree()

async function loadTree() {
  try {
    const result = await api('/api/tree')
    state.tree = result.tree
    elements.treeStatus.textContent = `${result.count} visible files`
    renderTree()
  } catch (error) {
    elements.treeStatus.textContent = error.message
  }
}

function renderTree() {
  const filter = elements.filter.value.trim().toLowerCase()
  elements.tree.replaceChildren(...renderNodes(state.tree, filter))
}

function renderNodes(nodes, filter) {
  const rendered = []
  for (const node of nodes) {
    if (node.type === 'file') {
      if (filter && !node.path.toLowerCase().includes(filter)) continue
      const button = document.createElement('button')
      button.className = `file-button${node.path === state.path ? ' active' : ''}`
      button.textContent = node.name
      button.title = node.path
      button.addEventListener('click', () => openFile(node.path))
      rendered.push(button)
      continue
    }

    const children = renderNodes(node.children, filter)
    if (children.length === 0) continue
    const details = document.createElement('details')
    details.open = Boolean(filter)
    const summary = document.createElement('summary')
    summary.textContent = node.name
    details.append(summary, ...children)
    rendered.push(details)
  }
  return rendered
}

async function openFile(path, position = null) {
  closeHover()
  elements.currentPath.textContent = path
  elements.currentPath.title = path
  elements.welcome.hidden = true
  elements.source.hidden = false
  elements.source.replaceChildren(statusLine('Loading…'))
  elements.sidebar.classList.remove('open')

  try {
    const result = await api(`/api/file?path=${encodeURIComponent(path)}`)
    state.path = path
    state.text = result.text
    state.selectedPosition = null
    state.selectedLine = null
    elements.definitionButton.disabled = true
    renderSource(result.text, path.endsWith('.lean'))
    renderTree()
    if (position) selectPosition(position)
  } catch (error) {
    elements.source.replaceChildren(statusLine(error.message))
  }
}

function renderSource(text, isLean) {
  const fragment = document.createDocumentFragment()
  const lines = text.split('\n')
  lines.forEach((line, index) => {
    const row = document.createElement('div')
    row.className = 'source-line'
    row.dataset.line = String(index)
    const content = document.createElement('span')
    content.className = 'line-content'
    if (isLean) highlightLeanLine(content, line)
    else content.textContent = line || ' '
    row.append(content)
    if (isLean) row.addEventListener('click', event => selectLeanPosition(event, row, content))
    fragment.append(row)
  })
  elements.source.replaceChildren(fragment)
}

function highlightLeanLine(container, line) {
  const pattern = /(\/\-.*|--.*|"(?:\\.|[^"\\])*"|\b(?:theorem|lemma|def|abbrev|example|instance|structure|class|inductive|namespace|section|variable|open|import|where|by|fun|let|in|if|then|else|match|with|do|return)\b|\b\d+(?:\.\d+)?\b)/g
  let offset = 0
  for (const match of line.matchAll(pattern)) {
    container.append(document.createTextNode(line.slice(offset, match.index)))
    const span = document.createElement('span')
    span.textContent = match[0]
    span.className = tokenClass(match[0])
    container.append(span)
    offset = match.index + match[0].length
  }
  container.append(document.createTextNode(line.slice(offset) || (line.length === 0 ? ' ' : '')))
}

function tokenClass(token) {
  if (token.startsWith('--') || token.startsWith('/-')) return 'tok-comment'
  if (token.startsWith('"')) return 'tok-string'
  if (/^\d/.test(token)) return 'tok-number'
  return 'tok-keyword'
}

function selectLeanPosition(event, row, content) {
  const range = document.caretRangeFromPoint?.(event.clientX, event.clientY)
  const position = document.caretPositionFromPoint?.(event.clientX, event.clientY)
  const node = position?.offsetNode ?? range?.startContainer
  const offset = position?.offset ?? range?.startOffset
  const character = node ? textOffsetWithin(content, node, offset) : 0
  setSelectedPosition({ line: Number(row.dataset.line), character }, row)
  requestHover()
}

function textOffsetWithin(root, targetNode, targetOffset) {
  const range = document.createRange()
  range.selectNodeContents(root)
  try {
    range.setEnd(targetNode, targetOffset)
    return range.toString().length
  } catch {
    return 0
  }
}

function setSelectedPosition(position, row) {
  state.selectedLine?.classList.remove('selected')
  state.selectedPosition = position
  state.selectedLine = row
  row?.classList.add('selected')
  elements.definitionButton.disabled = false
}

function selectPosition(position) {
  const row = elements.source.querySelector(`[data-line="${position.line}"]`)
  setSelectedPosition(position, row)
  row?.scrollIntoView({ block: 'center' })
  requestHover()
}

async function requestHover() {
  elements.hoverPanel.hidden = false
  elements.hoverStatus.textContent = 'Asking Lean…'
  elements.hoverContent.textContent = ''
  try {
    const result = await api('/api/hover', {
      method: 'POST',
      body: JSON.stringify({ path: state.path, position: state.selectedPosition })
    })
    elements.hoverStatus.textContent = result.hover ? '' : 'No Lean information at this position.'
    elements.hoverContent.textContent = result.hover ?? ''
  } catch (error) {
    elements.hoverStatus.textContent = error.message
  }
}

async function goToDefinition() {
  if (!state.path || !state.selectedPosition) return
  elements.definitionButton.disabled = true
  try {
    const result = await api('/api/definition', {
      method: 'POST',
      body: JSON.stringify({ path: state.path, position: state.selectedPosition })
    })
    const definition = result.definitions[0]
    if (!definition) {
      elements.hoverPanel.hidden = false
      elements.hoverStatus.textContent = 'No repository definition found.'
      return
    }
    await openFile(definition.path, definition.position)
  } catch (error) {
    elements.hoverPanel.hidden = false
    elements.hoverStatus.textContent = error.message
  } finally {
    elements.definitionButton.disabled = false
  }
}

function closeHover() {
  elements.hoverPanel.hidden = true
  elements.hoverStatus.textContent = ''
  elements.hoverContent.textContent = ''
}

function statusLine(text) {
  const element = document.createElement('div')
  element.className = 'status'
  element.textContent = text
  return element
}

async function api(url, options) {
  const response = await fetch(url, {
    headers: options?.body ? { 'Content-Type': 'application/json' } : undefined,
    ...options
  })
  const result = await response.json()
  if (!response.ok) throw new Error(result.error ?? `Request failed (${response.status})`)
  return result
}
