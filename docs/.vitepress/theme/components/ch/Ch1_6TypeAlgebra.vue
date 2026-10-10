<script setup>
import { computed, ref } from 'vue'

const TYPES = {
  Empty: { name: 'Empty', n: 0, elems: [] },
  Unit: { name: 'Unit', n: 1, elems: ['()'] },
  Bool: { name: 'Bool', n: 2, elems: ['false', 'true'] },
  Fin3: { name: 'Fin 3', n: 3, elems: ['0', '1', '2'] },
}
const TYPE_KEYS = Object.keys(TYPES)

const OPS = {
  prod: { sym: '×', name: '积', math: '×' },
  sum: { sym: '⊕', name: '和', math: '+' },
  fun: { sym: '→', name: '函数', math: '^' },
}

const PRESETS = [
  { label: '2 × 3 = 6', a: 'Bool', op: 'prod', b: 'Fin3' },
  { label: '2 + 3 = 5', a: 'Bool', op: 'sum', b: 'Fin3' },
  { label: '3² = 9', a: 'Bool', op: 'fun', b: 'Fin3' },
  { label: '2³ = 8', a: 'Fin3', op: 'fun', b: 'Bool' },
  { label: 'a × 1 = a', a: 'Fin3', op: 'prod', b: 'Unit' },
  { label: 'a × 0 = 0', a: 'Fin3', op: 'prod', b: 'Empty' },
  { label: 'a + 0 = a', a: 'Fin3', op: 'sum', b: 'Empty' },
  { label: '1 + 1 = 2', a: 'Unit', op: 'sum', b: 'Unit' },
  { label: 'a⁰ = 1', a: 'Empty', op: 'fun', b: 'Fin3' },
  { label: '0² = 0', a: 'Bool', op: 'fun', b: 'Empty' },
]

const a = ref('Bool')
const b = ref('Fin3')
const op = ref('prod')
const hoverRow = ref(null)

function choose(p) {
  a.value = p.a
  b.value = p.b
  op.value = p.op
}
const isPreset = (p) => p.a === a.value && p.b === b.value && p.op === op.value

const A = computed(() => TYPES[a.value])
const B = computed(() => TYPES[b.value])

const typeExpr = computed(() => `${A.value.name} ${OPS[op.value].sym} ${B.value.name}`)

const count = computed(() => {
  const m = A.value.n, n = B.value.n
  if (op.value === 'prod') return m * n
  if (op.value === 'sum') return m + n
  return n ** m
})

const formula = computed(() => {
  const m = A.value.n, n = B.value.n
  if (op.value === 'prod') return `${m} × ${n} = ${count.value}`
  if (op.value === 'sum') return `${m} + ${n} = ${count.value}`
  return `${n}^${m} = ${count.value}`
})

// 所有从 A 到 B 的函数，每个函数用“A 的每个元素选哪个 B 元素”的表来表示
const functions = computed(() => {
  const dom = A.value.elems, cod = B.value.elems
  let tables = [[]]
  for (let i = 0; i < dom.length; i++) {
    const next = []
    for (const t of tables) for (const y of cod) next.push([...t, y])
    tables = next
  }
  return tables.map((t) => dom.map((x, i) => [x, t[i]]))
})

const funLean = (tbl) =>
  tbl.length === 0 ? 'fun x => nomatch x' : 'fun ' + tbl.map(([x, y]) => `| ${x} => ${y}`).join(' ')

const note = computed(() => {
  const m = A.value.n, n = B.value.n
  if (op.value === 'prod') {
    if (m === 0 || n === 0) return '有一边是 Empty，凑不出序对需要的两个值，所以一个元素也没有：a × 0 = 0。'
    if (n === 1) return '每个元素只能和唯一的 () 配对，配对不增加任何信息：a × 1 ≅ a。'
    return '积的元素排成一个矩形：每一行是左边的一个元素，它要和右边的每一个元素各配一次。'
  }
  if (op.value === 'sum') {
    if (n === 0) return 'inr 这一侧需要一个 Empty 的值，造不出来，所以只剩 inl 包着的那些：a + 0 ≅ a。'
    return '和的元素是两堆“打了标签”的元素并排放：左边的都包上 inl，右边的都包上 inr，两堆绝不混淆。'
  }
  if (m === 0) return '定义域是 Empty：不需要对任何输入做选择，恰好有一个函数（空函数）。所以 a⁰ = 1。'
  if (n === 0) return `要为 ${A.value.name} 的每个元素选一个 Empty 的值——第一步就做不到，所以一个函数也没有。`
  return `对 ${A.value.name} 的每个元素（共 ${m} 个），独立地选一个 ${B.value.name} 的元素（${n} 种选法）：${Array(m).fill(n).join(' × ')} = ${count.value}。`
})
</script>

<template>
  <div class="ctfp-widget ta">
    <div class="ctfp-widget-title">类型代数计算器：把类型换成元素个数，× 和 ⊕ 就成了乘法和加法</div>

    <div class="ta-presets">
      <span class="ta-hint">试试：</span>
      <button v-for="p in PRESETS" :key="p.label" class="ctfp-btn" :class="{ on: isPreset(p) }" @click="choose(p)">
        {{ p.label }}
      </button>
    </div>

    <div class="ta-builder">
      <div class="ta-col">
        <div class="ta-lab">左边 α</div>
        <button v-for="k in TYPE_KEYS" :key="'a' + k" class="ctfp-btn" :class="{ on: a === k }" @click="a = k">
          {{ TYPES[k].name }} <small>({{ TYPES[k].n }})</small>
        </button>
      </div>
      <div class="ta-col">
        <div class="ta-lab">构造</div>
        <button v-for="(o, k) in OPS" :key="k" class="ctfp-btn ta-op" :class="{ on: op === k }" @click="op = k">
          {{ o.sym }} <small>{{ o.name }}</small>
        </button>
      </div>
      <div class="ta-col">
        <div class="ta-lab">右边 β</div>
        <button v-for="k in TYPE_KEYS" :key="'b' + k" class="ctfp-btn" :class="{ on: b === k }" @click="b = k">
          {{ TYPES[k].name }} <small>({{ TYPES[k].n }})</small>
        </button>
      </div>
    </div>

    <div class="ta-result">
      <code class="ta-type">{{ typeExpr }}</code>
      <span class="ta-eq">元素个数：<b>{{ formula }}</b></span>
    </div>

    <!-- 积：矩形网格 -->
    <div v-if="op === 'prod'" class="ta-view">
      <table v-if="A.n && B.n" class="ta-grid">
        <tr>
          <th></th>
          <th v-for="y in B.elems" :key="y"><code>{{ y }}</code></th>
        </tr>
        <tr v-for="x in A.elems" :key="x" :class="{ hot: hoverRow === x }" @mouseenter="hoverRow = x" @mouseleave="hoverRow = null">
          <th><code>{{ x }}</code></th>
          <td v-for="y in B.elems" :key="y"><code>({{ x }}, {{ y }})</code></td>
        </tr>
      </table>
      <div v-else class="ta-empty">（没有任何元素）</div>
    </div>

    <!-- 和：两堆带标签的元素 -->
    <div v-else-if="op === 'sum'" class="ta-view ta-sum">
      <div class="ta-pile">
        <div class="ta-pile-h">来自 {{ A.name }}</div>
        <code v-for="x in A.elems" :key="'l' + x" class="ta-chip l">inl {{ x }}</code>
        <span v-if="!A.n" class="ta-empty">（空）</span>
      </div>
      <div class="ta-plus">⊕</div>
      <div class="ta-pile">
        <div class="ta-pile-h">来自 {{ B.name }}</div>
        <code v-for="y in B.elems" :key="'r' + y" class="ta-chip r">inr {{ y }}</code>
        <span v-if="!B.n" class="ta-empty">（空）</span>
      </div>
    </div>

    <!-- 函数：每个函数是一张“输入 ↦ 输出”的表 -->
    <div v-else class="ta-view ta-funs">
      <div v-for="(tbl, i) in functions" :key="i" class="ta-fun" :title="funLean(tbl)">
        <div class="ta-fun-h">f{{ i + 1 }}</div>
        <div v-if="!tbl.length" class="ta-fun-row"><i>空函数</i></div>
        <div v-for="[x, y] in tbl" :key="x" class="ta-fun-row">
          <code>{{ x }}</code> ↦ <code>{{ y }}</code>
        </div>
      </div>
      <div v-if="!functions.length" class="ta-empty">（一个函数也没有）</div>
    </div>

    <p class="ta-note">{{ note }}</p>
  </div>
</template>

<style scoped>
.ta-presets {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
  align-items: center;
  margin-bottom: 14px;
}
.ta-hint,
.ta-lab {
  font-size: 12px;
  color: var(--vp-c-text-2);
}
.ta-builder {
  display: flex;
  flex-wrap: wrap;
  gap: 18px;
  justify-content: center;
  margin-bottom: 14px;
}
.ta-col {
  display: flex;
  flex-direction: column;
  gap: 5px;
  min-width: 104px;
}
.ta-col .ctfp-btn {
  border-radius: 8px;
  text-align: left;
}
.ta-op {
  font-size: 15px !important;
}
.ta-col small {
  color: var(--vp-c-text-3);
}
.ta-result {
  display: flex;
  flex-wrap: wrap;
  gap: 14px;
  align-items: baseline;
  justify-content: center;
  margin: 6px 0 12px;
}
.ta-type {
  font-size: 16px;
  padding: 3px 10px;
}
.ta-eq b {
  color: var(--vp-c-brand-1);
  font-size: 17px;
}
.ta-view {
  max-width: 100%;
  overflow-x: auto;
  display: flex;
  justify-content: center;
  min-height: 60px;
}
.ta-grid {
  border-collapse: collapse;
  margin: 0 !important;
  display: table;
}
.ta-grid th,
.ta-grid td {
  border: 1px solid var(--vp-c-divider);
  padding: 4px 10px;
  text-align: center;
  background: var(--vp-c-bg);
}
.ta-grid th {
  background: var(--vp-c-bg-soft);
}
.ta-grid tr.hot td {
  background: var(--vp-c-brand-soft);
}
.ta-sum {
  align-items: flex-start;
  gap: 14px;
}
.ta-pile {
  display: flex;
  flex-direction: column;
  gap: 5px;
  align-items: center;
  padding: 8px 12px;
  border: 1px dashed var(--vp-c-divider);
  border-radius: 10px;
  min-width: 110px;
}
.ta-pile-h {
  font-size: 12px;
  color: var(--vp-c-text-2);
}
.ta-plus {
  align-self: center;
  font-size: 22px;
  color: var(--vp-c-text-3);
}
.ta-chip.l {
  color: var(--vp-c-brand-1);
}
.ta-chip.r {
  color: var(--vp-c-purple-1, #8e5cd9);
}
.ta-funs {
  flex-wrap: wrap;
  gap: 8px;
  max-height: 320px;
  overflow-y: auto;
}
.ta-fun {
  border: 1px solid var(--vp-c-divider);
  border-radius: 8px;
  padding: 4px 10px 6px;
  background: var(--vp-c-bg);
  font-size: 13px;
  min-width: 92px;
}
.ta-fun-h {
  font-size: 11px;
  color: var(--vp-c-text-3);
}
.ta-fun-row code {
  font-size: 12px;
}
.ta-empty {
  color: var(--vp-c-text-3);
  font-style: italic;
  align-self: center;
}
.ta-note {
  margin: 12px 0 0;
  font-size: 13px;
  color: var(--vp-c-text-2);
  text-align: center;
}
</style>
