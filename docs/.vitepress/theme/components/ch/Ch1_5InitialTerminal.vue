<script setup>
import { ref, computed } from 'vue'
import CatDiagram from '../CatDiagram.vue'

const mode = ref('set')

// ---------- 集合与函数 ----------
const SETS = [
  { id: 'empty', name: 'Empty', tex: '\\varnothing', elems: [] },
  { id: 'unit', name: 'Unit', tex: '\\{()\\}', elems: ['()'] },
  { id: 'bool', name: 'Bool', tex: '\\{F, T\\}', elems: ['false', 'true'] },
  { id: 'three', name: 'Three', tex: '\\{a, b, c\\}', elems: ['a', 'b', 'c'] },
]

// ---------- 偏序集（整除关系） ----------
const POSETS = [
  {
    id: 'd12', name: '12 的因数', nodes: [
      { n: 1, x: 1, y: 3 }, { n: 2, x: 0, y: 2 }, { n: 3, x: 2, y: 2 },
      { n: 4, x: 0, y: 1 }, { n: 6, x: 2, y: 1 }, { n: 12, x: 1, y: 0 },
    ],
  },
  {
    id: 'd236', name: '{2, 3, 6}', nodes: [
      { n: 2, x: 0, y: 1 }, { n: 3, x: 2, y: 1 }, { n: 6, x: 1, y: 0 },
    ],
  },
  {
    id: 'd23', name: '{2, 3}', nodes: [
      { n: 2, x: 0, y: 0 }, { n: 3, x: 1.6, y: 0 },
    ],
  },
]
const posetId = ref('d12')
const poset = computed(() => POSETS.find((p) => p.id === posetId.value))

const objects = computed(() =>
  mode.value === 'set'
    ? SETS.map((s) => ({ id: s.id, name: s.name, label: `${s.name}（${s.elems.length} 个元素）` }))
    : poset.value.nodes.map((v) => ({ id: String(v.n), name: String(v.n), label: String(v.n) })),
)

function homCount(a, b) {
  if (mode.value === 'set') {
    const A = SETS.find((s) => s.id === a), B = SETS.find((s) => s.id === b)
    return Math.pow(B.elems.length, A.elems.length) // 0^0 = 1：空函数
  }
  return Number(b) % Number(a) === 0 ? 1 : 0
}

const selected = ref('empty')
const cell = ref(null) // { a, b }

function selectMode(m) {
  mode.value = m
  selected.value = m === 'set' ? 'empty' : String(poset.value.nodes[0].n)
  cell.value = null
}
function selectPoset(id) {
  posetId.value = id
  selected.value = String(poset.value.nodes[0].n)
  cell.value = null
}

const matrix = computed(() =>
  objects.value.map((a) => ({ a, cells: objects.value.map((b) => ({ b, n: homCount(a.id, b.id) })) })),
)

function verdictFor(id) {
  const out = objects.value.map((b) => homCount(id, b.id))
  const inn = objects.value.map((a) => homCount(a.id, id))
  return {
    initial: out.every((n) => n === 1),
    terminal: inn.every((n) => n === 1),
    outMissing: objects.value.filter((b, i) => out[i] === 0).map((b) => b.name),
    outMany: objects.value.filter((b, i) => out[i] > 1).map((b) => b.name),
    inMissing: objects.value.filter((a, i) => inn[i] === 0).map((a) => a.name),
    inMany: objects.value.filter((a, i) => inn[i] > 1).map((a) => a.name),
  }
}
const verdict = computed(() => verdictFor(selected.value))
const initials = computed(() => objects.value.filter((o) => verdictFor(o.id).initial).map((o) => o.name))
const terminals = computed(() => objects.value.filter((o) => verdictFor(o.id).terminal).map((o) => o.name))
const selName = computed(() => objects.value.find((o) => o.id === selected.value)?.name)

// 列出两个小集合之间的所有函数
const functionList = computed(() => {
  if (!cell.value || mode.value !== 'set') return null
  const A = SETS.find((s) => s.id === cell.value.a), B = SETS.find((s) => s.id === cell.value.b)
  const total = Math.pow(B.elems.length, A.elems.length)
  if (total > 9) return { A, B, total, fns: null }
  let fns = [[]]
  for (let i = 0; i < A.elems.length; i++) fns = fns.flatMap((f) => B.elems.map((y) => [...f, y]))
  if (B.elems.length === 0 && A.elems.length > 0) fns = []
  return { A, B, total, fns }
})

const hasse = computed(() => {
  const p = poset.value
  const ns = p.nodes.map((v) => v.n)
  const covers = []
  for (const a of ns) for (const b of ns) {
    if (a === b || b % a !== 0) continue
    const between = ns.some((c) => c !== a && c !== b && c % a === 0 && b % c === 0)
    if (!between) covers.push([a, b])
  }
  const lines = p.nodes.map((v) => `n${v.n}: (${v.x}, ${v.y}) "${v.n}"`)
  covers.forEach(([a, b]) => lines.push(`e${a}_${b}: n${a} -> n${b} ""`))
  lines.push('caption: 箭头 a → b 表示 a 整除 b（省略了由传递性得到的箭头和恒等箭头）')
  lines.push('size: 0.8')
  return lines.join('\n')
})
</script>

<template>
  <div class="ctfp-widget it">
    <div class="ctfp-widget-title">找一找：谁是始对象，谁是终对象？</div>
    <div class="it-tabs">
      <button :class="['ctfp-btn', { on: mode === 'set' }]" @click="selectMode('set')">集合与函数</button>
      <button :class="['ctfp-btn', { on: mode === 'poset' }]" @click="selectMode('poset')">偏序集（整除）</button>
    </div>
    <p class="it-hint" v-if="mode === 'set'">
      表格第 <i>a</i> 行第 <i>b</i> 列的数字，是从集合 <i>a</i> 到集合 <i>b</i> 的函数个数 |<i>b</i>|<sup>|<i>a</i>|</sup>。
      点击左侧对象名检查它是否为始对象（<b>整行</b>都是 1）或终对象（<b>整列</b>都是 1）；点击格子可以列出那些函数。
    </p>
    <p class="it-hint" v-else>
      偏序集是一个瘦范畴：从 <i>a</i> 到 <i>b</i> 有一个箭头当且仅当 <i>a</i> 整除 <i>b</i>，否则没有。始对象是“最小元”，终对象是“最大元”。换一个偏序集试试，它们可能不存在。
      <span class="it-posets">
        <button v-for="p in POSETS" :key="p.id" :class="['it-chip', { on: posetId === p.id }]" @click="selectPoset(p.id)">{{ p.name }}</button>
      </span>
    </p>

    <div class="it-main">
      <div class="it-matrix-wrap">
        <table class="it-matrix">
          <thead>
            <tr>
              <th>从 \ 到</th>
              <th v-for="o in objects" :key="o.id" :class="{ hl: selected === o.id }">{{ o.name }}</th>
            </tr>
          </thead>
          <tbody>
            <tr v-for="row in matrix" :key="row.a.id">
              <th :class="['it-rowhead', { hl: selected === row.a.id }]" @click="selected = row.a.id; cell = null">{{ row.a.name }}</th>
              <td
                v-for="c in row.cells" :key="c.b.id"
                :class="{
                  row: selected === row.a.id, col: selected === c.b.id,
                  one: c.n === 1, zero: c.n === 0, many: c.n > 1,
                  picked: cell && cell.a === row.a.id && cell.b === c.b.id,
                }"
                @click="cell = { a: row.a.id, b: c.b.id }"
              >{{ c.n }}</td>
            </tr>
          </tbody>
        </table>
      </div>
      <div v-if="mode === 'poset'" class="it-hasse">
        <CatDiagram :key="hasse" :spec="hasse" />
      </div>
    </div>

    <div class="it-verdicts">
      <div :class="['it-v', verdict.initial ? 'yes' : 'no']">
        <b>{{ selName }} {{ verdict.initial ? '是' : '不是' }}始对象。</b>
        <span v-if="!verdict.initial">
          <template v-if="verdict.outMissing.length">到 {{ verdict.outMissing.join('、') }} 一个箭头都没有。</template>
          <template v-if="verdict.outMany.length">到 {{ verdict.outMany.join('、') }} 的箭头不止一个（不唯一）。</template>
        </span>
        <span v-else>到每个对象都恰好有一个箭头。</span>
      </div>
      <div :class="['it-v', verdict.terminal ? 'yes' : 'no']">
        <b>{{ selName }} {{ verdict.terminal ? '是' : '不是' }}终对象。</b>
        <span v-if="!verdict.terminal">
          <template v-if="verdict.inMissing.length">从 {{ verdict.inMissing.join('、') }} 一个箭头都没有。</template>
          <template v-if="verdict.inMany.length">从 {{ verdict.inMany.join('、') }} 出发的箭头不止一个（不唯一）。</template>
        </span>
        <span v-else>从每个对象出发都恰好有一个箭头。</span>
      </div>
      <div class="it-summary">
        这个范畴的始对象：<b>{{ initials.length ? initials.join('、') : '不存在' }}</b>；
        终对象：<b>{{ terminals.length ? terminals.join('、') : '不存在' }}</b>。
      </div>
    </div>

    <div v-if="functionList" class="it-fns">
      <div class="it-fns-title">
        从 {{ functionList.A.name }} 到 {{ functionList.B.name }} 的函数，共 {{ functionList.total }} 个：
      </div>
      <div v-if="functionList.fns === null" class="it-note">太多了，就不一一列出了。</div>
      <div v-else-if="functionList.fns.length === 0" class="it-note">一个都没有：{{ functionList.A.name }} 里有元素，却无处可去。</div>
      <div v-else class="it-fn-list">
        <div v-for="(f, k) in functionList.fns" :key="k" class="it-fn">
          <template v-if="functionList.A.elems.length === 0">空函数（absurd′）：没有任何输入需要安排</template>
          <template v-else>
            <span v-for="(x, i) in functionList.A.elems" :key="i"><code>{{ x }}</code> ↦ <code>{{ f[i] }}</code><span v-if="i < f.length - 1">，</span></span>
          </template>
        </div>
      </div>
    </div>
  </div>
</template>

<style scoped>
.it { max-width: 100%; overflow: hidden; }
.it-tabs { display: flex; gap: 8px; flex-wrap: wrap; margin-bottom: 6px; }
.it-hint { font-size: 13px; color: var(--vp-c-text-2); line-height: 1.6; margin: 6px 0 10px; }
.it-posets { display: inline-flex; gap: 6px; flex-wrap: wrap; margin-left: 4px; }
.it-chip {
  font-size: 12px; padding: 1px 10px; border-radius: 999px; border: 1px solid var(--vp-c-divider);
  background: var(--vp-c-bg); color: var(--vp-c-text-1); cursor: pointer;
}
.it-chip.on { border-color: var(--vp-c-brand-1); color: var(--vp-c-brand-1); font-weight: 600; }
.it-main { display: flex; flex-wrap: wrap; gap: 14px; align-items: flex-start; }
.it-matrix-wrap { overflow-x: auto; max-width: 100%; }
.it-matrix { border-collapse: collapse; margin: 0; font-size: 13px; display: table; }
.it-matrix th, .it-matrix td {
  border: 1px solid var(--vp-c-divider); padding: 5px 10px; text-align: center; white-space: nowrap;
  font-family: var(--vp-font-family-mono); background: var(--vp-c-bg);
}
.it-matrix tr:nth-child(2n) { background: transparent; }
.it-matrix thead th { font-weight: 500; }
.it-matrix th.hl { color: var(--vp-c-brand-1); font-weight: 700; }
.it-rowhead { cursor: pointer; text-align: right !important; }
.it-rowhead:hover { color: var(--vp-c-brand-1); }
.it-matrix td { cursor: pointer; }
.it-matrix td.zero { color: var(--vp-c-text-3); }
.it-matrix td.many { color: var(--vp-c-warning-1); }
.it-matrix td.row, .it-matrix td.col { background: var(--vp-c-brand-soft); }
.it-matrix td.row.one, .it-matrix td.col.one { color: var(--vp-c-success-1, #18794e); font-weight: 700; }
.it-matrix td.picked { outline: 2px solid var(--vp-c-brand-1); outline-offset: -2px; }
.it-hasse { flex: 0 1 260px; min-width: 0; }
.it-hasse :deep(.cat-diagram) { margin: 0; }
.it-verdicts { margin-top: 10px; font-size: 13px; line-height: 1.6; }
.it-v { padding: 4px 10px; border-left: 3px solid var(--vp-c-divider); margin-bottom: 4px; }
.it-v.yes { border-left-color: var(--vp-c-success-1, #18794e); }
.it-v.yes b { color: var(--vp-c-success-1, #18794e); }
.it-v.no { border-left-color: var(--vp-c-danger-1); }
.it-summary { margin-top: 6px; color: var(--vp-c-text-2); }
.it-fns { margin-top: 10px; font-size: 13px; border-top: 1px dashed var(--vp-c-divider); padding-top: 8px; }
.it-fns-title { color: var(--vp-c-text-2); margin-bottom: 4px; }
.it-fn-list { display: flex; flex-direction: column; gap: 2px; }
.it-fn { font-size: 12.5px; }
.it-note { font-size: 12.5px; color: var(--vp-c-text-3); }
</style>
