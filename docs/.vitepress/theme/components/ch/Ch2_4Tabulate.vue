<script setup>
import { ref, computed, watch } from 'vue'

const tab = ref('memo')

// ---------- 制表与查表 ----------
const functors = {
  stream: {
    name: 'Stream',
    rep: 'Nat',
    keys: Array.from({ length: 12 }, (_, i) => i),
    keyLabel: (k) => String(k),
    fns: [
      { id: 'sq', label: 'n ↦ n * n', f: (n) => n * n },
      { id: 'pow', label: 'n ↦ 2 ^ n', f: (n) => 2 ** n },
      { id: 'fib', label: 'n ↦ fib n', f: (n) => { let a = 0, b = 1; for (let i = 0; i < n; i++) [a, b] = [b, a + b]; return a } },
      { id: 'm3', label: 'n ↦ n % 3 == 0', f: (n) => String(n % 3 === 0) },
    ],
  },
  pair: {
    name: 'Pair',
    rep: 'Bool',
    keys: [false, true],
    keyLabel: (k) => String(k),
    fns: [
      { id: 'yn', label: 'b ↦ if b then "是" else "否"', f: (b) => (b ? '"是"' : '"否"') },
      { id: 'not', label: 'b ↦ !b', f: (b) => String(!b) },
      { id: 'num', label: 'b ↦ if b then 1 else 0', f: (b) => (b ? 1 : 0) },
    ],
  },
}

const fname = ref('stream')
const fnId = ref('sq')
const F = computed(() => functors[fname.value])
const fn = computed(() => F.value.fns.find((x) => x.id === fnId.value) || F.value.fns[0])

const callsFn = ref(0)
const callsMemo = ref(0)
const memo = ref({})
const last = ref(null)
const log = ref([])

function resetMemo() {
  callsFn.value = 0
  callsMemo.value = 0
  memo.value = {}
  last.value = null
  log.value = []
}
watch(fname, () => {
  fnId.value = F.value.fns[0].id
  resetMemo()
})
watch(fnId, resetMemo)

function query(k) {
  const key = String(k)
  callsFn.value++
  const v = fn.value.f(k)
  let fresh = false
  if (!(key in memo.value)) {
    memo.value = { ...memo.value, [key]: v }
    callsMemo.value++
    fresh = true
  }
  last.value = key
  log.value = [
    `index (tabulate h) ${F.value.keyLabel(k)} = ${memo.value[key]}  ${fresh ? '（第一次访问：计算并存入表格）' : '（已在表中：直接读出）'}   h ${F.value.keyLabel(k)} = ${v}  ✓`,
    ...log.value,
  ].slice(0, 4)
}

function fillAll() {
  const m = { ...memo.value }
  for (const k of F.value.keys) {
    const key = String(k)
    if (!(key in m)) {
      m[key] = fn.value.f(k)
      callsMemo.value++
    }
  }
  memo.value = m
  log.value = [`严格制表：一次性算好全部 ${F.value.keys.length} 个格子${fname.value === 'stream' ? '（真正的流有无穷多格，这里只演示前 12 格）' : ''}`, ...log.value].slice(0, 4)
}

// ---------- 对数计算器 ----------
const INF = Infinity
const cands = [
  { id: 'id', name: 'Id x = x', counts: (n) => n, rep: 'Unit', why: '|F x| = x¹，表示对象有 1 个元素' },
  { id: 'pair', name: 'Pair x = x × x', counts: (n) => n * n, rep: 'Bool', why: '|F x| = x²，表示对象有 2 个元素' },
  { id: 'triple', name: 'x × x × x', counts: (n) => n ** 3, rep: 'Fin 3', why: '|F x| = x³，表示对象有 3 个元素' },
  { id: 'reader', name: 'Reader Bool x = Bool → x', counts: (n) => n * n, rep: 'Bool', why: 'Bool → x 有 x² 个值' },
  { id: 'const', name: 'F x = Unit（常函子）', counts: () => 1, rep: 'Empty', why: '|F x| = 1 = x⁰，表示对象是空类型！' },
  { id: 'stream', name: 'Stream x（≅ Nat → x）', counts: (n) => (n === 0 ? 0 : n === 1 ? 1 : INF), rep: 'Nat', why: 'Stream x ≅ x × Stream x，log 满足 R = 1 + R' },
  { id: 'option', name: 'Option x = 1 + x', counts: (n) => n + 1, rep: null, why: '|F Unit| = 2，但任何 R 都有 |R → Unit| = 1' },
  { id: 'list', name: 'List x = 1 + x + x² + …', counts: (n) => (n === 0 ? 1 : INF), rep: null, why: '|F Unit| = ∞，但任何 R 都有 |R → Unit| = 1' },
  { id: 'either', name: 'Bool ⊕ x = 2 + x', counts: (n) => n + 2, rep: null, why: '|F Empty| = 2，但 |R → Empty| 只能是 0 或 1' },
]
const candId = ref('pair')
const cand = computed(() => cands.find((c) => c.id === candId.value))
const show = (n) => (n === INF ? '∞' : String(n))
const sizes = [0, 1, 2, 3]
const sizeName = ['Empty', 'Unit', 'Bool', 'Fin 3']
</script>

<template>
  <div class="ctfp-widget t24">
    <div class="ctfp-widget-title">可表函子：同一份内容，两种实现</div>
    <div class="tabs">
      <button class="ctfp-btn" :class="{ on: tab === 'memo' }" @click="tab = 'memo'">制表与查表</button>
      <button class="ctfp-btn" :class="{ on: tab === 'log' }" @click="tab = 'log'">对数计算器：猜出 Rep</button>
    </div>

    <template v-if="tab === 'memo'">
      <p class="hint">选一个函子和一个函数 <code>h : Rep → x</code>，然后点击下方的键进行查询。比较两边“调用 h 的次数”。</p>
      <div class="row">
        <span class="lbl">函子：</span>
        <button v-for="(v, k) in functors" :key="k" class="ctfp-btn" :class="{ on: fname === k }" @click="fname = k">
          {{ v.name }}（Rep = {{ v.rep }}）
        </button>
      </div>
      <div class="row">
        <span class="lbl">函数 h：</span>
        <button v-for="x in F.fns" :key="x.id" class="ctfp-btn" :class="{ on: fnId === x.id }" @click="fnId = x.id">
          <code>{{ x.label }}</code>
        </button>
      </div>
      <div class="row">
        <span class="lbl">查询键：</span>
        <button v-for="k in F.keys" :key="String(k)" class="ctfp-btn key" @click="query(k)">{{ F.keyLabel(k) }}</button>
      </div>

      <div class="panes">
        <div class="pane">
          <div class="pane-title">函数视角：<code>h : {{ F.rep }} → x</code></div>
          <div class="big">{{ callsFn }}</div>
          <div class="sub">次调用 h（每次查询都要重新计算）</div>
        </div>
        <div class="pane">
          <div class="pane-title">数据视角：<code>tabulate h : {{ F.name }} x</code></div>
          <div class="tape">
            <div v-for="k in F.keys" :key="String(k)" class="cell" :class="{ filled: String(k) in memo, hit: last === String(k) }" @click="query(k)">
              <div class="ck">{{ F.keyLabel(k) }}</div>
              <div class="cv">{{ String(k) in memo ? memo[String(k)] : '?' }}</div>
            </div>
            <div v-if="fname === 'stream'" class="cell more">…</div>
          </div>
          <div class="sub"><b>{{ callsMemo }}</b> 次调用 h（每格只在第一次访问时计算）</div>
          <div class="row small">
            <button class="ctfp-btn" @click="fillAll">严格制表（一次填满）</button>
            <button class="ctfp-btn" @click="resetMemo">重置</button>
          </div>
        </div>
      </div>
      <pre class="log" v-if="log.length">{{ log.join('\n') }}</pre>
      <p class="hint">两边永远给出相同的值——这就是 <code>index ∘ tabulate = id</code>。它们只是性能不同：一个现算，一个查表。</p>
    </template>

    <template v-else>
      <p class="hint">把类型看成它的元素个数。可表函子必须满足 <code>|F x| = |x|^|Rep|</code>。选一个函子，看看它能不能写成某个“幂”。</p>
      <div class="row wrap">
        <button v-for="c in cands" :key="c.id" class="ctfp-btn" :class="{ on: candId === c.id }" @click="candId = c.id">{{ c.name }}</button>
      </div>
      <table class="logt">
        <thead>
          <tr><th>x</th><th v-for="n in sizes" :key="n"><code>{{ sizeName[n] }}</code>（{{ n }}）</th></tr>
        </thead>
        <tbody>
          <tr>
            <td>|F x|</td>
            <td v-for="n in sizes" :key="n" :class="{ bad: !cand.rep && ((n === 1 && cand.counts(1) !== 1) || (n === 0 && cand.counts(0) > 1)) }">{{ show(cand.counts(n)) }}</td>
          </tr>
          <tr v-if="cand.rep">
            <td>|Rep → x|</td>
            <td v-for="n in sizes" :key="n">{{ cand.rep === 'Nat' ? (n === 0 ? '0' : n === 1 ? '1' : '∞') : show(n ** ({ Empty: 0, Unit: 1, Bool: 2, 'Fin 3': 3 }[cand.rep])) }}</td>
          </tr>
        </tbody>
      </table>
      <div class="verdict" :class="cand.rep ? 'ok' : 'no'">
        <template v-if="cand.rep">可表：<code>Rep = {{ cand.rep }}</code>。{{ cand.why }}。</template>
        <template v-else>不可表：{{ cand.why }}。</template>
      </div>
    </template>
  </div>
</template>

<style scoped>
.t24 { max-width: 100%; overflow-x: auto; }
.tabs { display: flex; gap: 8px; margin-bottom: 10px; flex-wrap: wrap; }
.row { display: flex; gap: 6px; align-items: center; flex-wrap: wrap; margin: 6px 0; }
.row.small { margin-top: 8px; }
.lbl { font-size: 13px; color: var(--vp-c-text-2); min-width: 4.5em; }
.hint { font-size: 13px; color: var(--vp-c-text-2); margin: 6px 0; }
.key { min-width: 2.6em; font-variant-numeric: tabular-nums; }
.panes { display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 2fr); gap: 12px; margin-top: 10px; }
@media (max-width: 640px) { .panes { grid-template-columns: minmax(0, 1fr); } }
.pane { border: 1px solid var(--vp-c-divider); border-radius: 10px; padding: 10px 12px; background: var(--vp-c-bg); min-width: 0; }
.pane-title { font-size: 13px; font-weight: 600; margin-bottom: 6px; }
.big { font-size: 34px; font-weight: 700; color: var(--vp-c-brand-1); font-variant-numeric: tabular-nums; }
.sub { font-size: 12px; color: var(--vp-c-text-2); margin-top: 4px; }
.tape { display: flex; flex-wrap: wrap; gap: 4px; }
.cell { border: 1px solid var(--vp-c-divider); border-radius: 6px; min-width: 46px; padding: 2px 4px; text-align: center; cursor: pointer; transition: all 0.2s; }
.cell .ck { font-size: 10px; color: var(--vp-c-text-3); }
.cell .cv { font-size: 13px; font-family: var(--vp-font-family-mono); color: var(--vp-c-text-3); }
.cell.filled { border-color: var(--vp-c-brand-1); }
.cell.filled .cv { color: var(--vp-c-text-1); }
.cell.hit { background: var(--vp-c-brand-soft); }
.cell.more { border-style: dashed; cursor: default; display: flex; align-items: center; justify-content: center; }
.log { font-size: 12px; background: var(--vp-c-bg); border-radius: 8px; padding: 8px 10px; margin-top: 10px; white-space: pre-wrap; word-break: break-all; }
.logt { border-collapse: collapse; margin: 10px 0; font-size: 13px; display: table; }
.logt th, .logt td { border: 1px solid var(--vp-c-divider); padding: 4px 10px; text-align: center; }
.logt td.bad { color: var(--vp-c-danger-1); font-weight: 700; }
.verdict { padding: 8px 12px; border-radius: 8px; font-size: 14px; }
.verdict.ok { background: var(--vp-c-green-soft, rgba(16, 185, 129, 0.14)); }
.verdict.no { background: var(--vp-c-danger-soft, rgba(244, 63, 94, 0.14)); }
.wrap { flex-wrap: wrap; }
</style>
