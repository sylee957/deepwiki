import { execFile } from 'node:child_process'
import { promisify } from 'node:util'
import { isVisibleRepositoryPath } from './path-policy.mjs'

const execFileAsync = promisify(execFile)

export async function listRepositoryFiles(root) {
  const { stdout } = await execFileAsync(
    'git',
    ['ls-files', '--cached', '--others', '--exclude-standard', '-z'],
    { cwd: root, encoding: 'buffer', maxBuffer: 32 * 1024 * 1024 }
  )

  return stdout
    .toString('utf8')
    .split('\0')
    .filter(isVisibleRepositoryPath)
    .sort((a, b) => a.localeCompare(b))
}

export function buildFileTree(files) {
  const root = { name: '', type: 'directory', children: [] }

  for (const file of files) {
    const segments = file.split('/')
    let node = root
    for (let index = 0; index < segments.length; index += 1) {
      const name = segments[index]
      const isFile = index === segments.length - 1
      let child = node.children.find(item => item.name === name)
      if (!child) {
        child = isFile
          ? { name, type: 'file', path: file }
          : { name, type: 'directory', children: [] }
        node.children.push(child)
      }
      node = child
    }
  }

  sortTree(root)
  return root.children
}

function sortTree(node) {
  if (!node.children) return
  node.children.sort((left, right) => {
    if (left.type !== right.type) return left.type === 'directory' ? -1 : 1
    return left.name.localeCompare(right.name)
  })
  for (const child of node.children) sortTree(child)
}
