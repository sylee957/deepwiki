import { lstat, realpath, readFile } from 'node:fs/promises'
import path from 'node:path'

export const MAX_FILE_BYTES = 5 * 1024 * 1024

export const HIDDEN_SEGMENTS = new Set([
  '.git',
  '.lake',
  '.wiki',
  '.tlts',
  'build',
  'lake-packages',
  'node_modules',
  'references',
  '_out',
  '_site'
])

export function isVisibleRepositoryPath(relativePath) {
  if (typeof relativePath !== 'string' || relativePath.length === 0) return false
  if (relativePath.includes('\0') || path.isAbsolute(relativePath)) return false

  const normalized = relativePath.replaceAll('\\', '/')
  const segments = normalized.split('/')
  if (segments.some(segment => segment === '' || segment === '.' || segment === '..')) return false
  return !segments.some(segment => HIDDEN_SEGMENTS.has(segment))
}

export async function resolveRepositoryFile(root, relativePath) {
  if (!isVisibleRepositoryPath(relativePath)) {
    throw new FileAccessError('Path is outside the visible repository', 403)
  }

  const rootReal = await realpath(root)
  const candidate = path.resolve(rootReal, relativePath)
  const candidateReal = await realpath(candidate)
  const relativeReal = path.relative(rootReal, candidateReal)

  if (relativeReal.startsWith(`..${path.sep}`) || relativeReal === '..' || path.isAbsolute(relativeReal)) {
    throw new FileAccessError('Symbolic link escapes the repository', 403)
  }

  const stat = await lstat(candidateReal)
  if (!stat.isFile()) throw new FileAccessError('Path is not a file', 400)
  if (stat.size > MAX_FILE_BYTES) throw new FileAccessError('File is too large to display', 413)

  return { absolutePath: candidateReal, size: stat.size }
}

export async function readRepositoryTextFile(root, relativePath) {
  const resolved = await resolveRepositoryFile(root, relativePath)
  const content = await readFile(resolved.absolutePath)
  if (content.subarray(0, Math.min(content.length, 8192)).includes(0)) {
    throw new FileAccessError('Binary files cannot be displayed', 415)
  }
  return { ...resolved, text: content.toString('utf8') }
}

export class FileAccessError extends Error {
  constructor(message, statusCode) {
    super(message)
    this.name = 'FileAccessError'
    this.statusCode = statusCode
  }
}
