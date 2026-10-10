<script setup>
import { ref, computed } from 'vue'
import CatDiagram from '../CatDiagram.vue'

// 为了能把每个元素都列出来，演示中的 Int 只取 0、1、2 三个值。
const INT = [0, 1, 2]
const BOOL = [false, true]

const fmtB = (b) => (b ? 'true' : 'false')
const fmtTuple = (xs) => '(' + xs.map((x) => (typeof x === 'boolean' ? fmtB(x) : String(x))).join(', ') + ')'

const CANDS = [
  {
    id: 'int',
    name: 'Int',
    tex: '\\mathtt{Int}',
    elems: INT.map((x) => x),
    fmt: (x) => String(x),
    p: (x) => x,
    q: () => true,
    pDef: 'p x = x',
    qDef: 'q _ = true',
    blurb: '太小：Bool 那一维被压成了常数',
  },
  {
    id: 'triple',
    name: 'Int × Int × Bool',
    tex: '\\mathtt{Int \\times Int \\times Bool}',
    elems: INT.flatMap((x) => INT.flatMap((y) => BOOL.map((b) => [x, y, b]))),
    fmt: fmtTuple,
    p: (t) => t[0],
    q: (t) => t[2],
    pDef: 'p (x, _, _) = x',
    qDef: 'q (_, _, b) = b',
    blurb: '太大：多出来的中间分量是“冗余信息”',
  },
  {
    id: 'prod',
    name: 'Int × Bool',
    tex: '\\mathtt{Int \\times Bool}',
    elems: INT.flatMap((x) => BOOL.map((b) => [x, b])),
    fmt: fmtTuple,
    p: (t) => t[0],
    q: (t) => t[1],
    pDef: 'p = Prod.fst',
    qDef: 'q = Prod.snd',
    blurb: '标准的积',
  },
  {
    id: 'swap',
    name: 'Bool × Int',
    tex: '\\mathtt{Bool \\times Int}',
    elems: BOOL.flatMap((b) => INT.map((x) => [b, x])),
    fmt: fmtTuple,
    p: (t) => t[1],
    q: (t) => t[0],
    pDef: 'p = Prod.snd',
    qDef: 'q = Prod.fst',
    blurb: '分量顺序反了，投影也跟着对调',
  },
  {
    id: 'unit',
    name: 'Unit',
    tex: '\\mathtt{Unit}',
    elems: ['()'],
    fmt: () => '()',
    p: () => 2,
    q: () => true,
    pDef: 'p () = 2',
    qDef: 'q () = true',
    blurb: '只挑出了一个元素 (2, true)',
  },
  {
    id: 'bool',
    name: 'Bool',
    tex: '\\mathtt{Bool}',
    elems: BOOL.map((b) => b),
    fmt: fmtB,
    p: (b) => (b ? 1 : 0),
    q: (b) => b,
    pDef: 'p b = if b then 1 else 0',
    qDef: 'q b = b',
    blurb: 'Int 那一维只用到了 0 和 1',
  },
]

const byId = Object.fromEntries(CANDS.map((c) => [c.id, c]))
const key = (v) => JSON.stringify(v)

// 对每个 x ∈ c'，找出所有满足 p(y) = p'(x) 且 q(y) = q'(x) 的 y ∈ c。
function analyze(src, tgt) {
  const rows = src.elems.map((x) => {
    const pa = src.p(x), qb = src.q(x)
    const ys = tgt.elems.filter((y) => key(tgt.p(y)) === key(pa) && key(tgt.q(y)) === key(qb))
    return { x, pa, qb, ys }
  })
  const bad = rows.find((r) => r.ys.length === 0)
  let count = 1
  for (const r of rows) count *= r.ys.length
  const verdict = bad ? 'none' : count === 1 ? 'unique' : 'many'
  return { rows, verdict, bad, count }
}

const srcId = ref('int')
const tgtId = ref('prod')
const src = computed(() => byId[srcId.value])
const tgt = computed(() => byId[tgtId.value])
const result = computed(() => analyze(src.value, tgt.value))

const FORMULAS = {
  prod: (s) => `m x = (p' x, q' x)`,
  swap: (s) => `m x = (q' x, p' x)`,
}
const formula = computed(() => {
  if (result.value.verdict !== 'unique') return null
  if (srcId.value === tgtId.value) return 'm = id'
  const f = FORMULAS[tgtId.value]
  if (f) return f(src.value)
  return null
})

const matrix = computed(() =>
  CANDS.map((s) => ({ s, cells: CANDS.map((t) => ({ t, r: analyze(s, t) })) })),
)
const champions = computed(() =>
  CANDS.filter((t) => CANDS.every((s) => analyze(s, t).verdict === 'unique')).map((c) => c.name),
)

function pick(s, t) {
  srcId.value = s
  tgtId.value = t
}

const spec = computed(() => {
  const r = result.value
  const mLine =
    r.verdict === 'none'
      ? `m: C2 -> C "m\\ ?" dashed side=left color=red`
      : r.verdict === 'many'
        ? `m: C2 -> C "m" dashed side=left color=orange`
        : `m: C2 -> C "m" dashed side=left color=green`
  const lines = [
    `C2: (1.3, 0) "${src.value.tex}"`,
    `C: (1.3, 1.25) "${tgt.value.tex}"`,
    `A: (0, 2.5) "\\mathtt{Int}"`,
    `B: (2.6, 2.5) "\\mathtt{Bool}"`,
    `p2: C2 -> A "p'" bend=-40 side=right`,
    `q2: C2 -> B "q'" bend=40 side=left`,
    mLine,
    `p: C -> A "p" side=left`,
    `q: C -> B "q" side=right`,
  ]
  if (r.verdict !== 'none') {
    lines.push(`path "走 p′": p2 color=orange`, `path "走 p ∘ m": m p color=brand`)
    lines.push(`path "走 q′": q2 color=orange`, `path "走 q ∘ m": m q color=brand`)
  }
  return lines.join('\n')
})

const VERDICT_TEXT = {
  unique: '存在唯一的 m',
  many: '存在 m，但不唯一',
  none: '不存在 m',
}
const cellMark = (r) => (r.verdict === 'unique' ? '✓' : r.verdict === 'many' ? (r.count > 999 ? '多' : r.count) : '✗')
</script>

<template>
  <div class="ctfp-widget pr">
    <div class="ctfp-widget-title">积的泛构造：候选者排名（Int 与 Bool 的积）</div>
    <p class="pr-hint">
      先选一个“挑战者” c′，再选一个“被比较者” c。组件会找出所有满足
      <code>p′ = p ∘ m</code>、<code>q′ = q ∘ m</code> 的 <code>m : c′ → c</code>。
      若存在<b>唯一</b>的 m，就说 c 比 c′ 更好。（为了能把元素逐个列出，演示中 Int 只取 0、1、2。）
    </p>

    <div class="pr-pickers">
      <div class="pr-picker">
        <div class="pr-picker-label">挑战者 c′（m 的起点）</div>
        <div class="pr-chips">
          <button v-for="c in CANDS" :key="c.id" :class="['pr-chip', { on: srcId === c.id }]" @click="srcId = c.id">
            {{ c.name }}
          </button>
        </div>
      </div>
      <div class="pr-picker">
        <div class="pr-picker-label">被比较者 c（m 的终点）</div>
        <div class="pr-chips">
          <button v-for="c in CANDS" :key="c.id" :class="['pr-chip', { on: tgtId === c.id }]" @click="tgtId = c.id">
            {{ c.name }}
          </button>
        </div>
      </div>
    </div>

    <div class="pr-main">
      <div class="pr-diagram">
        <CatDiagram :key="spec" :spec="spec" />
      </div>
      <div class="pr-info">
        <div class="pr-defs">
          <div><span class="pr-tag">c′ = {{ src.name }}</span><code>p′</code>: <code>{{ src.pDef }}</code>，<code>q′</code>: <code>{{ src.qDef }}</code></div>
          <div class="pr-blurb">{{ src.blurb }}</div>
          <div><span class="pr-tag">c = {{ tgt.name }}</span><code>p</code>: <code>{{ tgt.pDef }}</code>，<code>q</code>: <code>{{ tgt.qDef }}</code></div>
          <div class="pr-blurb">{{ tgt.blurb }}</div>
        </div>
        <div :class="['pr-verdict', result.verdict]">
          <b>{{ VERDICT_TEXT[result.verdict] }}</b>
          <template v-if="result.verdict === 'unique'">
            ：c = {{ tgt.name }} 比 c′ = {{ src.name }} 更好（或一样好）。
            <div v-if="formula" class="pr-formula">公式：<code>{{ formula }}</code></div>
          </template>
          <template v-else-if="result.verdict === 'many'">
            ：在这个小模型里共有 {{ result.count }} 个不同的 m 都能让图交换。m 不唯一，c 只是“可以模仿” c′，算不上更好。
          </template>
          <template v-else>
            ：反例——元素 <code>{{ src.fmt(result.bad.x) }}</code> 要求 m 把它送到一个满足
            <code>p = {{ result.bad.pa }}</code>、<code>q = {{ fmtB(result.bad.qb) }}</code> 的元素，但 {{ tgt.name }} 里没有这样的元素。
          </template>
        </div>
        <div class="pr-table-wrap">
          <table class="pr-table">
            <thead>
              <tr><th>x ∈ c′</th><th>(p′ x, q′ x)</th><th>m x 可以是</th></tr>
            </thead>
            <tbody>
              <tr v-for="(r, i) in result.rows" :key="i" :class="{ bad: r.ys.length === 0, amb: r.ys.length > 1 }">
                <td><code>{{ src.fmt(r.x) }}</code></td>
                <td><code>({{ r.pa }}, {{ fmtB(r.qb) }})</code></td>
                <td>
                  <span v-if="!r.ys.length" class="pr-none">无解</span>
                  <span v-else><code v-for="(y, k) in r.ys" :key="k" class="pr-y">{{ tgt.fmt(y) }}</code></span>
                </td>
              </tr>
            </tbody>
          </table>
        </div>
      </div>
    </div>

    <div class="pr-rank">
      <div class="pr-picker-label">排行榜：行 = 挑战者 c′，列 = 被比较者 c。✓ 表示唯一的 m 存在；数字表示（小模型里）有多少个 m，“多”表示超过一千个；✗ 表示不存在。点击格子查看详情。</div>
      <div class="pr-matrix-wrap">
        <table class="pr-matrix">
          <thead>
            <tr>
              <th>c′ \ c</th>
              <th v-for="c in CANDS" :key="c.id" :class="{ champ: champions.includes(c.name) }">{{ c.name }}</th>
            </tr>
          </thead>
          <tbody>
            <tr v-for="row in matrix" :key="row.s.id">
              <th>{{ row.s.name }}</th>
              <td
                v-for="cell in row.cells" :key="cell.t.id"
                :class="[cell.r.verdict, { sel: srcId === row.s.id && tgtId === cell.t.id, champ: champions.includes(cell.t.name) }]"
                @click="pick(row.s.id, cell.t.id)"
              >{{ cellMark(cell.r) }}</td>
            </tr>
          </tbody>
        </table>
      </div>
      <p class="pr-conclusion">
        整列都是 ✓ 的候选者，能被<b>每一个</b>候选者唯一地分解进来：<b>{{ champions.join('、') }}</b>。
        它们就是积。两者之间互有唯一的 m，而且互逆——积只在同构意义下唯一。
      </p>
    </div>
  </div>
</template>

<style scoped>
.pr { max-width: 100%; overflow: hidden; }
.pr-hint { font-size: 13px; color: var(--vp-c-text-2); line-height: 1.6; margin: 4px 0 10px; }
.pr-pickers { display: flex; flex-direction: column; gap: 8px; margin-bottom: 8px; }
.pr-picker-label { font-size: 12px; color: var(--vp-c-text-3); margin-bottom: 4px; line-height: 1.5; }
.pr-chips { display: flex; flex-wrap: wrap; gap: 6px; }
.pr-chip {
  font-family: var(--vp-font-family-mono); font-size: 12px; padding: 3px 10px; border-radius: 999px;
  border: 1px solid var(--vp-c-divider); background: var(--vp-c-bg); color: var(--vp-c-text-1); cursor: pointer;
}
.pr-chip:hover { border-color: var(--vp-c-brand-1); }
.pr-chip.on { border-color: var(--vp-c-brand-1); background: var(--vp-c-brand-soft); color: var(--vp-c-brand-1); font-weight: 600; }
.pr-main { display: flex; flex-wrap: wrap; gap: 12px; align-items: flex-start; }
.pr-diagram { flex: 1 1 300px; min-width: 0; max-width: 420px; }
.pr-diagram :deep(.cat-diagram) { margin: 0; }
.pr-info { flex: 1 1 300px; min-width: 0; }
.pr-defs { font-size: 12.5px; line-height: 1.7; margin-bottom: 8px; }
.pr-tag {
  display: inline-block; font-family: var(--vp-font-family-mono); font-size: 11.5px; padding: 0 6px; margin-right: 6px;
  border-radius: 4px; background: var(--vp-c-default-soft); color: var(--vp-c-text-1);
}
.pr-blurb { font-size: 12px; color: var(--vp-c-text-3); margin: 0 0 4px 2px; }
.pr-verdict { font-size: 13px; line-height: 1.6; padding: 8px 12px; border-radius: 8px; margin-bottom: 8px; border: 1px solid var(--vp-c-divider); background: var(--vp-c-bg); }
.pr-verdict.unique { border-color: var(--vp-c-success-1, #18794e); }
.pr-verdict.unique b { color: var(--vp-c-success-1, #18794e); }
.pr-verdict.many { border-color: var(--vp-c-warning-1); }
.pr-verdict.many b { color: var(--vp-c-warning-1); }
.pr-verdict.none { border-color: var(--vp-c-danger-1); }
.pr-verdict.none b { color: var(--vp-c-danger-1); }
.pr-formula { margin-top: 4px; }
.pr-table-wrap { max-height: 230px; overflow: auto; border: 1px solid var(--vp-c-divider); border-radius: 8px; }
.pr-table, .pr-matrix { border-collapse: collapse; margin: 0; font-size: 12px; display: table; width: 100%; }
.pr-table th, .pr-table td { padding: 3px 8px; border: none; border-bottom: 1px solid var(--vp-c-divider); text-align: left; white-space: nowrap; }
.pr-table th { position: sticky; top: 0; background: var(--vp-c-bg-soft); font-weight: 600; }
.pr-table tr.bad td { background: var(--vp-c-danger-soft); }
.pr-table tr.amb td { background: var(--vp-c-warning-soft); }
.pr-table tr:nth-child(2n) { background: transparent; }
.pr-y { margin-right: 6px; }
.pr-none { color: var(--vp-c-danger-1); font-weight: 600; }
.pr-rank { margin-top: 14px; }
.pr-matrix-wrap { overflow-x: auto; }
.pr-matrix th, .pr-matrix td { padding: 4px 6px; border: 1px solid var(--vp-c-divider); text-align: center; font-family: var(--vp-font-family-mono); font-size: 11.5px; white-space: nowrap; }
.pr-matrix thead th { background: var(--vp-c-bg); }
.pr-matrix thead th.champ { color: var(--vp-c-success-1, #18794e); }
.pr-matrix tbody th { text-align: right; background: var(--vp-c-bg); font-weight: 500; }
.pr-matrix td { cursor: pointer; background: var(--vp-c-bg); }
.pr-matrix td.unique { color: var(--vp-c-success-1, #18794e); font-weight: 700; }
.pr-matrix td.many { color: var(--vp-c-warning-1); }
.pr-matrix td.none { color: var(--vp-c-danger-1); }
.pr-matrix td.champ { background: var(--vp-c-success-soft, rgba(24, 121, 78, 0.08)); }
.pr-matrix td.sel { outline: 2px solid var(--vp-c-brand-1); outline-offset: -2px; }
.pr-matrix tr:nth-child(2n) { background: transparent; }
.pr-conclusion { font-size: 13px; color: var(--vp-c-text-2); line-height: 1.6; margin: 8px 0 0; }
</style>
