<script setup>
// 范畴 = Span 中的单子：把一个小范畴摊成 span Ob ← Arr → Ob，
// 列出拉回 T ∘ T 的元素（可复合对），点选后显示 μ（复合）与 η（恒等箭头），并可一键检查单子定律。
import { computed, ref, watch } from 'vue'

function preorder() {
  const ob = ['0', '1', '2']
  const arr = []
  for (let i = 0; i < 3; i++) for (let j = i; j < 3; j++) arr.push({ name: i === j ? `id${'₀₁₂'[i]}` : `${i}≤${j}`, dom: i, cod: j })
  const find = (d, c) => arr.findIndex((a) => a.dom === d && a.cod === c)
  return { ob, arr, id: (o) => find(o, o), comp: (a1, a2) => find(arr[a1].dom, arr[a2].cod) }
}
function z3() {
  const arr = [0, 1, 2].map((k) => ({ name: String(k), dom: 0, cod: 0 }))
  return { ob: ['★'], arr, id: () => 0, comp: (a1, a2) => (a1 + a2) % 3 }
}
function small() {
  const ob = ['A', 'B', 'C']
  const arr = [
    { name: 'idA', dom: 0, cod: 0 }, { name: 'idB', dom: 1, cod: 1 }, { name: 'idC', dom: 2, cod: 2 },
    { name: 'f', dom: 0, cod: 1 }, { name: 'g', dom: 0, cod: 1 }, { name: 'h', dom: 1, cod: 2 },
    { name: 'h∘f', dom: 0, cod: 2 }, { name: 'h∘g', dom: 0, cod: 2 },
  ]
  const idx = (n) => arr.findIndex((a) => a.name === n)
  const table = { 'f,h': 'h∘f', 'g,h': 'h∘g' }
  return {
    ob, arr, id: (o) => o,
    comp: (a1, a2) => {
      if (arr[a1].name.startsWith('id')) return a2
      if (arr[a2].name.startsWith('id')) return a1
      return idx(table[`${arr[a1].name},${arr[a2].name}`])
    },
  }
}
const EXAMPLES = [
  { id: 'pre', name: '预序 0 ≤ 1 ≤ 2', make: preorder },
  { id: 'z3', name: '幺半群 (ℤ/3, +)：单对象范畴', make: z3 },
  { id: 'small', name: 'f, g : A → B，h : B → C', make: small },
]
const exId = ref('small')
const C = computed(() => EXAMPLES.find((e) => e.id === exId.value).make())

const sel = ref(null)
watch(exId, () => { sel.value = null; report.value = null })

const pairs = computed(() => {
  const out = []
  const A = C.value.arr
  A.forEach((a1, i) => A.forEach((a2, j) => { if (a1.cod === a2.dom) out.push([i, j]) }))
  return out
})

const W = 460
const H = computed(() => Math.max(C.value.arr.length, C.value.ob.length) * 34 + 60)
const LX = 60, MX = W / 2, RX = W - 60
const arrY = (i) => 50 + i * ((H.value - 80) / Math.max(1, C.value.arr.length - 1))
const obY = (o) => (C.value.ob.length === 1 ? H.value / 2 + 10 : 50 + o * ((H.value - 80) / (C.value.ob.length - 1)))

const roles = computed(() => {
  const r = {}
  const s = sel.value
  if (!s) return r
  if (s.kind === 'pair') {
    r[s.a1] = 'a1'
    r[s.a2] = s.a2 === s.a1 ? 'a1' : 'a2'
    const a3 = C.value.comp(s.a1, s.a2)
    r[a3] = r[a3] ? r[a3] + ' a3' : 'a3'
  } else if (s.kind === 'ob') {
    r[C.value.id(s.o)] = 'eta'
  }
  return r
})
const obRole = (o) => (sel.value && sel.value.kind === 'ob' && sel.value.o === o ? 'eta' : '')

const info = computed(() => {
  const s = sel.value
  if (!s) return null
  const A = C.value.arr, ob = C.value.ob
  if (s.kind === 'pair') {
    const a1 = A[s.a1], a2 = A[s.a2], a3i = C.value.comp(s.a1, s.a2), a3 = A[a3i]
    return {
      kind: 'pair', a1, a2, a3,
      mid: ob[a1.cod],
      dOk: a3.dom === a1.dom, cOk: a3.cod === a2.cod,
      dom: ob[a3.dom], cod: ob[a3.cod], d1: ob[a1.dom], c2: ob[a2.cod],
    }
  }
  const e = A[C.value.id(s.o)]
  return { kind: 'ob', o: ob[s.o], e, ok: e.dom === s.o && e.cod === s.o }
})

const report = ref(null)
function checkLaws() {
  const { arr, id, comp } = C.value
  let unitN = 0, unitBad = 0, assocN = 0, assocBad = 0
  arr.forEach((a, i) => {
    unitN += 2
    if (comp(id(a.dom), i) !== i) unitBad++
    if (comp(i, id(a.cod)) !== i) unitBad++
  })
  pairs.value.forEach(([i, j]) => {
    arr.forEach((c, k) => {
      if (arr[j].cod !== c.dom) return
      assocN++
      if (comp(comp(i, j), k) !== comp(i, comp(j, k))) assocBad++
    })
  })
  report.value = { unitN, unitBad, assocN, assocBad }
}
</script>

<template>
  <div class="ctfp-widget sm">
    <div class="ctfp-widget-title">范畴 = Span 中的单子：两个集合和四个函数</div>
    <p class="sm-hint">
      中间一列是集合 Arr（“箭头”），两侧是同一个集合 Ob（“对象”）；向左的连线是 dom，向右的是 cod——这就是 span Ob ← Arr → Ob。
      点下方的一个“可复合对”看 μ 如何把它送到一个箭头；点左侧的对象看 η 选出的恒等箭头。
    </p>
    <div class="sm-row">
      <button v-for="e in EXAMPLES" :key="e.id" class="ctfp-btn" :class="{ on: exId === e.id }" @click="exId = e.id">{{ e.name }}</button>
    </div>

    <div class="sm-main">
      <svg :viewBox="`0 0 ${W} ${H}`" :width="W" class="sm-svg">
        <text :x="LX" y="20" text-anchor="middle" class="sm-head">Ob</text>
        <text :x="MX" y="20" text-anchor="middle" class="sm-head">Arr</text>
        <text :x="RX" y="20" text-anchor="middle" class="sm-head">Ob</text>
        <text :x="(LX + MX) / 2" y="34" text-anchor="middle" class="sm-leg">← dom</text>
        <text :x="(MX + RX) / 2" y="34" text-anchor="middle" class="sm-leg">cod →</text>
        <g v-for="(a, i) in C.arr" :key="'l' + i" :class="['sm-legs', roles[i]]">
          <line :x1="MX - 34" :y1="arrY(i)" :x2="LX + 14" :y2="obY(a.dom)" />
          <line :x1="MX + 34" :y1="arrY(i)" :x2="RX - 14" :y2="obY(a.cod)" />
        </g>
        <g v-for="(o, k) in C.ob" :key="'o' + k">
          <g class="sm-ob" :class="obRole(k)" @click="sel = { kind: 'ob', o: k }">
            <circle :cx="LX" :cy="obY(k)" r="13" />
            <text :x="LX" :y="obY(k) + 5" text-anchor="middle">{{ o }}</text>
          </g>
          <g class="sm-ob passive" :class="obRole(k)">
            <circle :cx="RX" :cy="obY(k)" r="13" />
            <text :x="RX" :y="obY(k) + 5" text-anchor="middle">{{ o }}</text>
          </g>
        </g>
        <g v-for="(a, i) in C.arr" :key="'a' + i" :class="['sm-arr', roles[i]]">
          <rect :x="MX - 34" :y="arrY(i) - 12" width="68" height="24" rx="12" />
          <text :x="MX" :y="arrY(i) + 5" text-anchor="middle">{{ a.name }}</text>
        </g>
      </svg>

      <div class="sm-side">
        <div class="sm-sub">拉回 T ∘ T 的顶点 = 可复合对 (a₁, a₂)，cod a₁ = dom a₂：</div>
        <div class="sm-pairs">
          <button v-for="[i, j] in pairs" :key="i + '-' + j" class="sm-pair"
                  :class="{ on: sel && sel.kind === 'pair' && sel.a1 === i && sel.a2 === j }"
                  @click="sel = { kind: 'pair', a1: i, a2: j }">
            ({{ C.arr[i].name }}, {{ C.arr[j].name }})
          </button>
        </div>
        <div class="sm-count">共 {{ pairs.length }} 对；而 Arr × Arr 有 {{ C.arr.length ** 2 }} 对——拉回只留下了能接上的那些。</div>
        <div v-if="info && info.kind === 'pair'" class="sm-info">
          <div><span class="c1">a₁ = {{ info.a1.name }}</span>，<span class="c2">a₂ = {{ info.a2.name }}</span>：cod a₁ = {{ info.mid }} = dom a₂</div>
          <div>μ(a₁, a₂) = <span class="c3">{{ info.a3.name }}</span>（先 a₁ 再 a₂）</div>
          <div>2-胞腔条件：dom μ = {{ info.dom }} = dom a₁ {{ info.dOk ? '✓' : '✗' }}；cod μ = {{ info.cod }} = cod a₂ {{ info.cOk ? '✓' : '✗' }}</div>
        </div>
        <div v-else-if="info && info.kind === 'ob'" class="sm-info">
          <div>η({{ info.o }}) = <span class="c3">{{ info.e.name }}</span></div>
          <div>2-胞腔条件：dom ∘ η = id，cod ∘ η = id：dom = cod = {{ info.o }} {{ info.ok ? '✓' : '✗' }}</div>
        </div>
        <div v-else class="sm-info muted">还没有选中任何东西。</div>
        <button class="ctfp-btn" @click="checkLaws">检查单子定律（= 范畴定律）</button>
        <div v-if="report" class="sm-info">
          单位律：检查 {{ report.unitN }} 个等式，{{ report.unitBad ? `失败 ${report.unitBad} 个` : '全部成立' }}；
          结合律：检查 {{ report.assocN }} 个可复合三元组，{{ report.assocBad ? `失败 ${report.assocBad} 个` : '全部成立' }}。
        </div>
      </div>
    </div>
  </div>
</template>

<style scoped>
.sm-hint { font-size: 13px; color: var(--vp-c-text-2); margin: 0 0 10px; line-height: 1.7; }
.sm-row { display: flex; flex-wrap: wrap; gap: 6px; margin-bottom: 8px; }
.sm-main { display: flex; flex-wrap: wrap; gap: 14px; align-items: flex-start; }
.sm-svg { flex: 0 1 460px; max-width: 100%; height: auto; }
.sm-head { font-size: 14px; font-weight: 600; fill: var(--vp-c-text-1); font-style: italic; }
.sm-leg { font-size: 11px; fill: var(--vp-c-text-3); }
.sm-legs line { stroke: var(--vp-c-text-3); stroke-width: 1.1; opacity: 0.6; transition: all 0.2s; }
.sm-legs.a1 line { stroke: var(--vp-c-brand-1); stroke-width: 2.4; opacity: 1; }
.sm-legs.a2 line { stroke: var(--vp-c-success-1, #18794e); stroke-width: 2.4; opacity: 1; }
.sm-legs.a3 line, .sm-legs.eta line { stroke: var(--vp-c-purple-1, #8e5cd9); stroke-width: 2.4; opacity: 1; stroke-dasharray: 5 3; }
.sm-arr rect { fill: var(--vp-c-bg); stroke: var(--vp-c-text-2); stroke-width: 1.2; transition: all 0.2s; }
.sm-arr text { font-size: 13px; fill: var(--vp-c-text-1); font-family: var(--vp-font-family-mono); }
.sm-arr.a1 rect { stroke: var(--vp-c-brand-1); stroke-width: 2.4; }
.sm-arr.a2 rect { stroke: var(--vp-c-success-1, #18794e); stroke-width: 2.4; }
.sm-arr.a3 rect, .sm-arr.eta rect { fill: var(--vp-c-purple-soft, rgba(142, 92, 217, 0.16)); stroke: var(--vp-c-purple-1, #8e5cd9); stroke-width: 2.4; }
.sm-ob { cursor: pointer; }
.sm-ob.passive { cursor: default; }
.sm-ob circle { fill: var(--vp-c-bg-soft); stroke: var(--vp-c-text-1); stroke-width: 1.4; }
.sm-ob text { font-size: 13px; fill: var(--vp-c-text-1); font-weight: 600; }
.sm-ob.eta circle { stroke: var(--vp-c-purple-1, #8e5cd9); stroke-width: 2.6; }
.sm-ob:not(.passive):hover circle { stroke-width: 2.6; }
.sm-side { flex: 1 1 240px; min-width: 0; display: flex; flex-direction: column; gap: 8px; }
.sm-sub { font-size: 13px; color: var(--vp-c-text-2); }
.sm-pairs { display: flex; flex-wrap: wrap; gap: 5px; }
.sm-pair {
  font-family: var(--vp-font-family-mono); font-size: 12px; padding: 2px 8px; border-radius: 999px;
  border: 1px solid var(--vp-c-divider); background: var(--vp-c-bg); color: var(--vp-c-text-1); cursor: pointer;
}
.sm-pair:hover, .sm-pair.on { border-color: var(--vp-c-brand-1); color: var(--vp-c-brand-1); }
.sm-count { font-size: 12px; color: var(--vp-c-text-3); }
.sm-info { font-size: 13px; line-height: 1.8; padding: 6px 10px; border-radius: 8px; border: 1px solid var(--vp-c-divider); background: var(--vp-c-bg); }
.sm-info.muted { color: var(--vp-c-text-3); }
.c1 { color: var(--vp-c-brand-1); font-weight: 600; }
.c2 { color: var(--vp-c-success-1, #18794e); font-weight: 600; }
.c3 { color: var(--vp-c-purple-1, #8e5cd9); font-weight: 600; }
</style>
