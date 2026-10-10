#!/usr/bin/env node
// 抽取 docs/**/*.md 中的 Lean / Rust 代码块并编译校验。
//
//   node scripts/check-code.mjs                 # 校验全部
//   node scripts/check-code.mjs docs/part1/01-category.md docs/preface.md
//   node scripts/check-code.mjs --lean-only / --rust-only
//
// 每个 md 里所有（非 no-check 的）lean 块按顺序拼接成一个文件编译；报错行号映射回 md。
// 生成的文件在 build/lean/ 下，可以直接用编辑器打开调试。
import fs from 'node:fs'
import path from 'node:path'
import os from 'node:os'
import { spawn } from 'node:child_process'
import MarkdownIt from 'markdown-it'
import { classifyFence } from '../docs/.vitepress/fences.mjs'

const root = path.resolve(path.dirname(new URL(import.meta.url).pathname), '..')
const docs = path.join(root, 'docs')
const outDir = path.join(root, 'build')
const args = process.argv.slice(2)
const leanOnly = args.includes('--lean-only')
const rustOnly = args.includes('--rust-only')
const fileArgs = args.filter((a) => !a.startsWith('--'))

function walk(dir) {
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap((e) => {
    if (e.name.startsWith('.') || e.name === 'public') return []
    const p = path.join(dir, e.name)
    return e.isDirectory() ? walk(p) : p.endsWith('.md') ? [p] : []
  })
}

const files = fileArgs.length ? fileArgs.map((f) => path.resolve(f)) : walk(docs)
const md = new MarkdownIt({ html: true })

const elan = path.join(os.homedir(), '.elan', 'bin')
const env = { ...process.env, PATH: `${elan}:${process.env.PATH}` }

function run(cmd, argv, opts = {}) {
  return new Promise((resolve) => {
    const p = spawn(cmd, argv, { env, ...opts })
    let out = ''
    p.stdout.on('data', (d) => (out += d))
    p.stderr.on('data', (d) => (out += d))
    p.on('close', (code) => resolve({ code, out }))
    p.on('error', (e) => resolve({ code: -1, out: String(e) }))
  })
}

const jobs = []
for (const file of files) {
  const src = fs.readFileSync(file, 'utf8')
  const tokens = md.parse(src, {})
  const rel = path.relative(root, file)
  const slug = path.relative(docs, file).replace(/\.md$/, '').replace(/[\\/]/g, '__')
  const lean = { lines: [], map: [] }
  let rustIdx = 0
  for (const t of tokens) {
    if (t.type !== 'fence') continue
    const f = classifyFence(t.info)
    if (f.noCheck) continue
    const startLine = t.map[0] + 2 // 围栏内容第一行（1-based）
    if ((f.lang === 'lean' || f.lang === 'lean4') && !rustOnly) {
      const body = t.content.replace(/\n$/, '').split('\n')
      body.forEach((l, i) => {
        lean.lines.push(l)
        lean.map.push(startLine + i)
      })
      lean.lines.push('')
      lean.map.push(startLine + body.length)
    } else if (f.lang === 'rust' && !leanOnly) {
      const i = ++rustIdx
      jobs.push({ kind: 'rust', rel, slug: `${slug}__${i}`, content: t.content, startLine })
    }
  }
  if (lean.lines.length) jobs.push({ kind: 'lean', rel, slug, ...lean })
}

if (!fileArgs.length && !rustOnly) {
  const prelude = fs.readFileSync(path.join(root, 'lean', 'Prelude.lean'), 'utf8').split('\n')
  jobs.push({ kind: 'lean', rel: 'lean/Prelude.lean', slug: '_Prelude', lines: prelude, map: prelude.map((_, i) => i + 1) })
}

fs.mkdirSync(path.join(outDir, 'lean'), { recursive: true })
fs.mkdirSync(path.join(outDir, 'rust'), { recursive: true })

const RUST_PRELUDE = '#![allow(dead_code, unused_variables, unused_imports, unused_mut, non_snake_case)]\n'

async function check(job) {
  if (job.kind === 'lean') {
    const gen = path.join(outDir, 'lean', `${job.slug}.lean`)
    fs.writeFileSync(gen, job.lines.join('\n') + '\n')
    const { code, out } = await run('lean', [gen], { cwd: path.join(outDir, 'lean') })
    const mapped = out.replace(new RegExp(`${gen.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}:(\\d+):(\\d+)`, 'g'),
      (_, l, c) => `${job.rel}:${job.map[Number(l) - 1] ?? '?'}:${c}`)
    const hasSorry = /declaration uses `?'?sorry/.test(out)
    const ok = code === 0 && !hasSorry
    return { ok, label: `${job.rel} [lean]`, out: mapped + (hasSorry ? '\n(检查失败：已校验代码块中不允许出现 sorry；练习骨架请用 `lean no-check`)\n' : '') }
  }
  const gen = path.join(outDir, 'rust', `${job.slug}.rs`)
  fs.writeFileSync(gen, RUST_PRELUDE + job.content)
  const { code, out } = await run('rustc', ['--edition', '2021', '--crate-type', 'lib', '--emit=metadata',
    '-o', path.join(outDir, 'rust', `${job.slug}.rmeta`), gen])
  const mapped = out.replace(/(-->\s*)\S+\.rs:(\d+):(\d+)/g,
    (_, p, l, c) => `${p}${job.rel}:${job.startLine + Number(l) - 2}:${c}`)
  return { ok: code === 0, label: `${job.rel}:${job.startLine} [rust]`, out: mapped }
}

const limit = Math.max(2, os.cpus().length)
const results = []
let next = 0
await Promise.all(Array.from({ length: limit }, async () => {
  while (next < jobs.length) {
    const job = jobs[next++]
    const r = await check(job)
    results.push(r)
    const msg = r.out.trim()
    console.log(`${r.ok ? 'OK  ' : 'FAIL'} ${r.label}`)
    if (msg && (!r.ok || process.env.VERBOSE)) console.log(msg.replace(/^/gm, '    '))
  }
}))

const failed = results.filter((r) => !r.ok)
console.log(`\n${results.length - failed.length}/${results.length} 通过`)
process.exit(failed.length ? 1 : 0)
