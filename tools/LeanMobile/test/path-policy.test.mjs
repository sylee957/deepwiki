import assert from 'node:assert/strict'
import { mkdtemp, mkdir, symlink, writeFile } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import path from 'node:path'
import test from 'node:test'
import {
  FileAccessError,
  isVisibleRepositoryPath,
  readRepositoryTextFile,
  resolveRepositoryFile
} from '../src/path-policy.mjs'
import { buildFileTree } from '../src/repository.mjs'

test('visible paths allow repository files and reject private or escaping paths', () => {
  assert.equal(isVisibleRepositoryPath('DeepWiki/NetworkCalculus.lean'), true)
  assert.equal(isVisibleRepositoryPath('tools/LeanMobile/README.md'), true)
  assert.equal(isVisibleRepositoryPath('../secret'), false)
  assert.equal(isVisibleRepositoryPath('/etc/passwd'), false)
  assert.equal(isVisibleRepositoryPath('.git/config'), false)
  assert.equal(isVisibleRepositoryPath('references/book.pdf'), false)
  assert.equal(isVisibleRepositoryPath('.lake/build/lib.olean'), false)
})

test('file resolver blocks symlinks that escape the repository', async () => {
  const root = await mkdtemp(path.join(tmpdir(), 'lean-mobile-root-'))
  const outside = await mkdtemp(path.join(tmpdir(), 'lean-mobile-outside-'))
  await writeFile(path.join(outside, 'secret.txt'), 'secret')
  await symlink(path.join(outside, 'secret.txt'), path.join(root, 'escape.txt'))

  await assert.rejects(
    resolveRepositoryFile(root, 'escape.txt'),
    error => error instanceof FileAccessError && error.statusCode === 403
  )
})

test('text reader rejects binary files', async () => {
  const root = await mkdtemp(path.join(tmpdir(), 'lean-mobile-binary-'))
  await writeFile(path.join(root, 'binary.dat'), Buffer.from([1, 0, 2]))
  await assert.rejects(
    readRepositoryTextFile(root, 'binary.dat'),
    error => error instanceof FileAccessError && error.statusCode === 415
  )
})

test('file tree groups directories before files', () => {
  const tree = buildFileTree(['README.md', 'DeepWiki/Z.lean', 'DeepWiki/A.lean'])
  assert.equal(tree[0].name, 'DeepWiki')
  assert.deepEqual(tree[0].children.map(node => node.name), ['A.lean', 'Z.lean'])
  assert.equal(tree[1].name, 'README.md')
})
