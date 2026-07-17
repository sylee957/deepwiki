import { isVisibleRepositoryPath } from './path-policy.ts'

export interface FileNode {
  name: string
  type: 'file'
  path: string
}

export interface DirectoryNode {
  name: string
  type: 'directory'
  children: TreeNode[]
}

export type TreeNode = FileNode | DirectoryNode

export async function listRepositoryFiles(root: string) {
  const process = Bun.spawn(
    ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'],
    { cwd: root, stdout: 'pipe', stderr: 'pipe' }
  )
  const [exitCode, stdout, stderr] = await Promise.all([
    process.exited,
    new Response(process.stdout).arrayBuffer(),
    new Response(process.stderr).text()
  ])
  if (exitCode !== 0) throw new Error(`Unable to list repository files: ${stderr.trim()}`)

  return new TextDecoder()
    .decode(stdout)
    .split('\0')
    .filter(isVisibleRepositoryPath)
    .sort((left, right) => left.localeCompare(right))
}

export function buildFileTree(files: string[]): TreeNode[] {
  const root: DirectoryNode = { name: '', type: 'directory', children: [] }

  for (const file of files) {
    const segments = file.split('/')
    let node = root
    for (let index = 0; index < segments.length; index += 1) {
      const name = segments[index]
      if (name === undefined) continue
      const isFile = index === segments.length - 1
      let child = node.children.find(item => item.name === name)
      if (!child) {
        child = isFile
          ? { name, type: 'file', path: file }
          : { name, type: 'directory', children: [] }
        node.children.push(child)
      }
      if (child.type === 'directory') node = child
    }
  }

  sortTree(root)
  return root.children
}

function sortTree(node: DirectoryNode) {
  node.children.sort((left, right) => {
    if (left.type !== right.type) return left.type === 'directory' ? -1 : 1
    return left.name.localeCompare(right.name)
  })
  for (const child of node.children) {
    if (child.type === 'directory') sortTree(child)
  }
}
