<script setup>
import { computed, ref, watch } from 'vue'

// 小范畴：两个对象 A、B，一个非恒等态射 f : A → B。
// 一个“集合值”函子 S：S(A) = {0, 1}，S(B) = {0, 1, 2}，S(f) 可选。
const SF_OPTIONS = [
  { label: 'x ↦ x', map: [0, 1] },
  { label: 'x ↦ x + 1', map: [1, 2] },
  { label: 'x ↦ 0（常值）', map: [0, 0] },
  { label: 'x ↦ 2 − x', map: [2, 1] },
]

const SA = [0, 1]
const SB = [0, 1, 2]
const BOOL = ['假', '真']

const PRESETS = {
  hom: {
    name: 'p(x, y) = S(x) → S(y)',
    domA: { labels: SA, name: 'S(A)' }, codA: { labels: SA, name: 'S(A)' },
    domB: { labels: SB, name: 'S(B)' }, codB: { labels: SB, name: 'S(B)' },
    domAB: { labels: SA, name: 'S(A)' }, codAB: { labels: SB, name: 'S(B)' },
    left: (a, sf) => a.map((v) => sf[v]),
    right: (b, sf) => sf.map((v) => b[v]),
    leftName: 'S(f) ∘ α_A',
    rightName: 'α_B ∘ S(f)',
    explain:
      '楔条件读作 S(f) ∘ α_A = α_B ∘ S(f)——这正是自然性方块！所以这个剖函子的端就是自然变换 S ⟹ S 的集合：∫_c (S c → S c) = Nat(S, S)。',
  },
  fiber: {
    name: 'p(x, y) = S(y)（忽略第一个参数）',
    domA: { labels: ['★'], name: '{★}' }, codA: { labels: SA, name: 'S(A)' },
    domB: { labels: ['★'], name: '{★}' }, codB: { labels: SB, name: 'S(B)' },
    domAB: { labels: ['★'], name: '{★}' }, codAB: { labels: SB, name: 'S(B)' },
    left: (a, sf) => [sf[a[0]]],
    right: (b) => [b[0]],
    leftName: 'S(f)(α_A)',
    rightName: 'α_B',
    explain:
      '剖函子不看第一个参数，它其实就是函子 S。楔条件变成 S(f)(α_A) = α_B——这正是锥的条件。所以端就是 S 的极限；在这个范畴里，α_A 一旦选定，α_B 就被决定了，端 ≅ S(A)。（“集合中的一个元素”被画成“从单点集 {★} 出发的函数”。）',
  },
  pred: {
    name: 'p(x, y) = S(x) → 布尔（忽略第二个参数）',
    domA: { labels: SA, name: 'S(A)' }, codA: { labels: BOOL, name: '布尔' },
    domB: { labels: SB, name: 'S(B)' }, codB: { labels: BOOL, name: '布尔' },
    domAB: { labels: SA, name: 'S(A)' }, codAB: { labels: BOOL, name: '布尔' },
    left: (a) => a.slice(),
    right: (b, sf) => sf.map((v) => b[v]),
    leftName: 'α_A',
    rightName: 'α_B ∘ S(f)',
    explain:
      '剖函子只看第一个（逆变的）参数。楔条件变成 α_A = α_B ∘ S(f)：α_A 完全由 α_B 决定。所以端 ≅ (S(B) → 布尔)，一共 8 个元素。',
  },
}

const presetKey = ref('hom')
const sfIdx = ref(0)
const preset = computed(() => PRESETS[presetKey.value])
const sf = computed(() => SF_OPTIONS[sfIdx.value].map)

const alphaA = ref([0, 1])
const alphaB = ref([0, 1, 2])

function resetAlphas() {
  const P = preset.value
  alphaA.value = P.domA.labels.map((_, i) => Math.min(i, P.codA.labels.length - 1))
  alphaB.value = P.domB.labels.map((_, i) => Math.min(i, P.codB.labels.length - 1))
}
watch(presetKey, resetAlphas)

function cycle(which, i) {
  const P = preset.value
  if (which === 'A') {
    const n = P.codA.labels.length
    const a = alphaA.value.slice()
    a[i] = (a[i] + 1) % n
    alphaA.value = a
  } else {
    const n = P.codB.labels.length
    const b = alphaB.value.slice()
    b[i] = (b[i] + 1) % n
    alphaB.value = b
  }
}

const leftLeg = computed(() => preset.value.left(alphaA.value, sf.value))
const rightLeg = computed(() => preset.value.right(alphaB.value, sf.value))
const holds = computed(() => leftLeg.value.every((v, i) => v === rightLeg.value[i]))

function allFunctions(m, n) {
  const out = []
  const total = n ** m
  for (let k = 0; k < total; k++) {
    const f = []
    let r = k
    for (let i = 0; i < m; i++) {
      f.push(r % n)
      r = Math.floor(r / n)
    }
    out.push(f)
  }
  return out
}

const enumeration = computed(() => {
  const P = preset.value
  const As = allFunctions(P.domA.labels.length, P.codA.labels.length)
  const Bs = allFunctions(P.domB.labels.length, P.codB.labels.length)
  const wedges = []
  for (const a of As)
    for (const b of Bs) {
      const l = P.left(a, sf.value)
      const r = P.right(b, sf.value)
      if (l.every((v, i) => v === r[i])) wedges.push([a, b])
    }
  return { total: As.length * Bs.length, wedges }
})

let wedgeCursor = -1
function nextWedge() {
  const ws = enumeration.value.wedges
  if (!ws.length) return
  wedgeCursor = (wedgeCursor + 1) % ws.length
  alphaA.value = ws[wedgeCursor][0].slice()
  alphaB.value = ws[wedgeCursor][1].slice()
}
function randomFamily() {
  const P = preset.value
  alphaA.value = P.domA.labels.map(() => Math.floor(Math.random() * P.codA.labels.length))
  alphaB.value = P.domB.labels.map(() => Math.floor(Math.random() * P.codB.labels.length))
}

// ---------- 几何 ----------
const W = 660
const H = 470
const SP = 30
const boxes = {
  A: { x: 30, y: 120, w: 230, h: 150 },
  B: { x: 400, y: 120, w: 230, h: 150 },
  AB: { x: 200, y: 310, w: 260, h: 140 },
}
const apex = { x: W / 2, y: 52 }

function columnYs(n, box) {
  const top = box.y + 44 + ((box.h - 52) - (n - 1) * SP) / 2
  return Array.from({ length: n }, (_, i) => top + i * SP)
}

function layout(box, dom, cod) {
  const cx = box.x + box.w / 2
  const dx = cx - 50
  const cxx = cx + 50
  return {
    dx, cx: cxx,
    dys: columnYs(dom.labels.length, box),
    cys: columnYs(cod.labels.length, box),
  }
}

const geoA = computed(() => layout(boxes.A, preset.value.domA, preset.value.codA))
const geoB = computed(() => layout(boxes.B, preset.value.domB, preset.value.codB))
const geoAB = computed(() => layout(boxes.AB, preset.value.domAB, preset.value.codAB))

function seg(g, i, j, off = 0) {
  return { x1: g.dx + 8, y1: g.dys[i] + off, x2: g.cx - 11, y2: g.cys[j] + off }
}

const abLines = computed(() => {
  const g = geoAB.value
  const out = []
  leftLeg.value.forEach((l, i) => {
    const r = rightLeg.value[i]
    if (l === r) out.push({ ...seg(g, i, l), kind: 'same' })
    else {
      out.push({ ...seg(g, i, l, -2), kind: 'left' })
      out.push({ ...seg(g, i, r, 2), kind: 'right' })
    }
  })
  return out
})
const badDom = computed(() => leftLeg.value.map((l, i) => l !== rightLeg.value[i]))

const arrows = computed(() => [
  { d: `M${apex.x - 12},${apex.y + 14} Q${boxes.A.x + 150},${apex.y + 30} ${boxes.A.x + boxes.A.w / 2},${boxes.A.y - 4}`, lx: 205, ly: 78, label: 'α', sub: 'A', color: 'var(--vp-c-text-2)' },
  { d: `M${apex.x + 12},${apex.y + 14} Q${boxes.B.x + 80},${apex.y + 30} ${boxes.B.x + boxes.B.w / 2},${boxes.B.y - 4}`, lx: 455, ly: 78, label: 'α', sub: 'B', color: 'var(--vp-c-text-2)' },
  { d: `M${boxes.A.x + boxes.A.w / 2},${boxes.A.y + boxes.A.h + 2} Q${boxes.A.x + boxes.A.w / 2 + 10},${boxes.AB.y + 40} ${boxes.AB.x - 4},${boxes.AB.y + 50}`, lx: 70, ly: 318, label: 'p(id', sub: 'A', tail: ', f)', color: 'var(--vp-c-brand-1)' },
  { d: `M${boxes.B.x + boxes.B.w / 2},${boxes.B.y + boxes.B.h + 2} Q${boxes.B.x + boxes.B.w / 2 - 10},${boxes.AB.y + 40} ${boxes.AB.x + boxes.AB.w + 4},${boxes.AB.y + 50}`, lx: 548, ly: 318, label: 'p(f, id', sub: 'B', tail: ')', color: 'var(--vp-c-warning-1)' },
])
</script>

<template>
  <div class="ctfp-widget wedge-explorer">
    <div class="ctfp-widget-title">楔与端：亲手挑一族 α，看楔条件是否成立</div>
    <div class="row">
      <span class="lab">剖函子：</span>
      <button v-for="(P, k) in PRESETS" :key="k" class="ctfp-btn" :class="{ on: presetKey === k }" @click="presetKey = k">{{ P.name }}</button>
    </div>
    <div class="row">
      <span class="lab">态射 f : A → B 被 S 映成：</span>
      <button v-for="(o, i) in SF_OPTIONS" :key="i" class="ctfp-btn" :class="{ on: sfIdx === i }" @click="sfIdx = i">{{ o.label }}</button>
    </div>

    <svg :viewBox="`0 0 ${W} ${H}`" class="canvas" role="img" aria-label="楔的示意图">
      <defs>
        <marker id="ch310w-ah" viewBox="0 0 10 10" refX="8.5" refY="5" markerWidth="8" markerHeight="8" orient="auto-start-reverse" markerUnits="userSpaceOnUse">
          <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
        </marker>
      </defs>

      <!-- 顶点 -->
      <circle :cx="apex.x" :cy="apex.y" r="15" class="apex" />
      <text :x="apex.x" :y="apex.y + 5" text-anchor="middle" class="apex-t">★</text>
      <text :x="apex.x" :y="apex.y - 24" text-anchor="middle" class="small">楔的顶点：单点集 {★}</text>

      <!-- 箭头 -->
      <g v-for="(a, i) in arrows" :key="i">
        <path :d="a.d" fill="none" :stroke="a.color" stroke-width="1.8" marker-end="url(#ch310w-ah)" />
        <text :x="a.lx" :y="a.ly" text-anchor="middle" class="arrow-t" :fill="a.color">{{ a.label }}<tspan baseline-shift="sub" font-size="11">{{ a.sub }}</tspan><tspan v-if="a.tail">{{ a.tail }}</tspan></text>
      </g>

      <!-- p(A,A) -->
      <rect :x="boxes.A.x" :y="boxes.A.y" :width="boxes.A.w" :height="boxes.A.h" rx="10" class="box" />
      <text :x="boxes.A.x + 12" :y="boxes.A.y + 22" class="box-t">p(A, A) 中的 α<tspan baseline-shift="sub" font-size="10">A</tspan></text>
      <text :x="geoA.dx" :y="boxes.A.y + 40" text-anchor="middle" class="col-t">{{ preset.domA.name }}</text>
      <text :x="geoA.cx" :y="boxes.A.y + 40" text-anchor="middle" class="col-t">{{ preset.codA.name }}</text>
      <line v-for="(v, i) in alphaA" :key="'la' + i" v-bind="seg(geoA, i, v)" class="fn-line" marker-end="url(#ch310w-ah)" />
      <g v-for="(l, i) in preset.domA.labels" :key="'da' + i" class="clickable" @click="cycle('A', i)">
        <circle :cx="geoA.dx" :cy="geoA.dys[i]" r="8" class="dom-dot" />
        <text :x="geoA.dx - 14" :y="geoA.dys[i] + 4" text-anchor="end" class="dot-t">{{ l }}</text>
      </g>
      <g v-for="(l, j) in preset.codA.labels" :key="'ca' + j">
        <circle :cx="geoA.cx" :cy="geoA.cys[j]" r="6" class="cod-dot" />
        <text :x="geoA.cx + 12" :y="geoA.cys[j] + 4" class="dot-t">{{ l }}</text>
      </g>

      <!-- p(B,B) -->
      <rect :x="boxes.B.x" :y="boxes.B.y" :width="boxes.B.w" :height="boxes.B.h" rx="10" class="box" />
      <text :x="boxes.B.x + 12" :y="boxes.B.y + 22" class="box-t">p(B, B) 中的 α<tspan baseline-shift="sub" font-size="10">B</tspan></text>
      <text :x="geoB.dx" :y="boxes.B.y + 40" text-anchor="middle" class="col-t">{{ preset.domB.name }}</text>
      <text :x="geoB.cx" :y="boxes.B.y + 40" text-anchor="middle" class="col-t">{{ preset.codB.name }}</text>
      <line v-for="(v, i) in alphaB" :key="'lb' + i" v-bind="seg(geoB, i, v)" class="fn-line" marker-end="url(#ch310w-ah)" />
      <g v-for="(l, i) in preset.domB.labels" :key="'db' + i" class="clickable" @click="cycle('B', i)">
        <circle :cx="geoB.dx" :cy="geoB.dys[i]" r="8" class="dom-dot" />
        <text :x="geoB.dx - 14" :y="geoB.dys[i] + 4" text-anchor="end" class="dot-t">{{ l }}</text>
      </g>
      <g v-for="(l, j) in preset.codB.labels" :key="'cb' + j">
        <circle :cx="geoB.cx" :cy="geoB.cys[j]" r="6" class="cod-dot" />
        <text :x="geoB.cx + 12" :y="geoB.cys[j] + 4" class="dot-t">{{ l }}</text>
      </g>

      <!-- p(A,B) -->
      <rect :x="boxes.AB.x" :y="boxes.AB.y" :width="boxes.AB.w" :height="boxes.AB.h" rx="10" class="box" :class="holds ? 'ok' : 'bad'" />
      <text :x="boxes.AB.x + 12" :y="boxes.AB.y + 22" class="box-t">p(A, B)：两条路在此会师？</text>
      <text :x="geoAB.dx" :y="boxes.AB.y + 40" text-anchor="middle" class="col-t">{{ preset.domAB.name }}</text>
      <text :x="geoAB.cx" :y="boxes.AB.y + 40" text-anchor="middle" class="col-t">{{ preset.codAB.name }}</text>
      <line v-for="(s, k) in abLines" :key="'ab' + k" :x1="s.x1" :y1="s.y1" :x2="s.x2" :y2="s.y2" :class="['ab-line', s.kind]" marker-end="url(#ch310w-ah)" />
      <g v-for="(l, i) in preset.domAB.labels" :key="'dab' + i">
        <circle :cx="geoAB.dx" :cy="geoAB.dys[i]" r="7" :class="['ab-dot', { bad: badDom[i] }]" />
        <text :x="geoAB.dx - 13" :y="geoAB.dys[i] + 4" text-anchor="end" class="dot-t">{{ l }}</text>
      </g>
      <g v-for="(l, j) in preset.codAB.labels" :key="'cab' + j">
        <circle :cx="geoAB.cx" :cy="geoAB.cys[j]" r="6" class="cod-dot" />
        <text :x="geoAB.cx + 12" :y="geoAB.cys[j] + 4" class="dot-t">{{ l }}</text>
      </g>
    </svg>

    <div class="legend">
      <span><i class="sw brand" />左路：{{ preset.leftName }}</span>
      <span><i class="sw orange" />右路：{{ preset.rightName }}</span>
      <span><i class="sw green" />两路重合</span>
    </div>

    <div class="status" :class="holds ? 'ok' : 'bad'">
      <template v-if="holds">楔条件成立：两条路径落在 p(A, B) 的同一个元素上——这一族 (α_A, α_B) 是一个楔，也就是端的一个元素。</template>
      <template v-else>楔条件不成立：红色的点上，两条路径去了不同的地方。这一族只是对角线乘积中的一个元素，不在端里。</template>
    </div>

    <div class="row">
      <button class="ctfp-btn" @click="nextWedge">下一个楔</button>
      <button class="ctfp-btn" @click="randomFamily">随机挑一族</button>
      <span class="count">对角线乘积 p(A,A) × p(B,B) 共有 <b>{{ enumeration.total }}</b> 族，其中满足楔条件的有 <b>{{ enumeration.wedges.length }}</b> 族——端 ∫<sub>c</sub> p(c, c) 恰好有 {{ enumeration.wedges.length }} 个元素。</span>
    </div>
    <p class="explain">{{ preset.explain }}</p>
    <p class="hint">操作：点击方框左列的圆点，切换它被 α 映到哪里；换一个剖函子或换一个 S(f)，看看端的大小如何变化。</p>
  </div>
</template>

<style scoped>
.wedge-explorer .row {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 6px;
  margin: 6px 0;
}
.lab {
  font-size: 13px;
  color: var(--vp-c-text-2);
}
.canvas {
  width: 100%;
  max-width: 660px;
  height: auto;
  display: block;
  margin: 8px auto 0;
}
.apex {
  fill: var(--vp-c-bg);
  stroke: var(--vp-c-text-2);
  stroke-width: 1.5;
}
.apex-t {
  font-size: 15px;
  fill: var(--vp-c-text-1);
}
.small {
  font-size: 12px;
  fill: var(--vp-c-text-2);
}
.arrow-t {
  font-size: 14px;
  font-style: italic;
}
.box {
  fill: var(--vp-c-bg);
  stroke: var(--vp-c-divider);
  stroke-width: 1.5;
}
.box.ok {
  stroke: var(--vp-c-success-1, #18794e);
  stroke-width: 2.5;
}
.box.bad {
  stroke: var(--vp-c-danger-1);
  stroke-width: 2.5;
}
.box-t {
  font-size: 13px;
  font-weight: 600;
  fill: var(--vp-c-text-1);
}
.col-t {
  font-size: 11px;
  fill: var(--vp-c-text-3);
}
.dot-t {
  font-size: 12px;
  fill: var(--vp-c-text-2);
}
.dom-dot {
  fill: var(--vp-c-brand-soft, rgba(59, 111, 216, 0.15));
  stroke: var(--vp-c-brand-1);
  stroke-width: 2;
}
.clickable {
  cursor: pointer;
}
.clickable:hover .dom-dot {
  fill: var(--vp-c-brand-1);
}
.cod-dot {
  fill: var(--vp-c-text-2);
}
.fn-line {
  stroke: var(--vp-c-text-1);
  stroke-width: 1.6;
}
.ab-dot {
  fill: var(--vp-c-text-2);
}
.ab-dot.bad {
  fill: var(--vp-c-danger-1);
}
.ab-line {
  stroke-width: 2;
}
.ab-line.same {
  stroke: var(--vp-c-success-1, #18794e);
  stroke-width: 3;
}
.ab-line.left {
  stroke: var(--vp-c-brand-1);
}
.ab-line.right {
  stroke: var(--vp-c-warning-1);
  stroke-dasharray: 5 4;
}
.legend {
  display: flex;
  flex-wrap: wrap;
  gap: 14px;
  justify-content: center;
  font-size: 12px;
  color: var(--vp-c-text-2);
}
.sw {
  display: inline-block;
  width: 18px;
  height: 3px;
  margin-right: 5px;
  vertical-align: middle;
}
.sw.brand {
  background: var(--vp-c-brand-1);
}
.sw.orange {
  background: var(--vp-c-warning-1);
}
.sw.green {
  background: var(--vp-c-success-1, #18794e);
}
.status {
  margin: 10px 0 4px;
  padding: 8px 12px;
  border-radius: 8px;
  font-size: 14px;
  border-left: 4px solid;
}
.status.ok {
  border-color: var(--vp-c-success-1, #18794e);
  background: var(--vp-c-success-soft, rgba(24, 121, 78, 0.08));
}
.status.bad {
  border-color: var(--vp-c-danger-1);
  background: var(--vp-c-danger-soft, rgba(200, 50, 50, 0.08));
}
.count {
  font-size: 13px;
  color: var(--vp-c-text-2);
}
.explain {
  font-size: 14px;
  margin: 8px 0 4px;
}
.hint {
  font-size: 12px;
  color: var(--vp-c-text-3);
  margin: 4px 0 0;
}
</style>
