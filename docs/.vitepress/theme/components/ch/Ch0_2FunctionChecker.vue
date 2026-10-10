<script setup>
import { ref, computed } from 'vue'

const A_NAMES = ['1', '2', '3', '4', '5']
const B_NAMES = ['a', 'b', 'c', 'd', 'e']
const MAX = 5

const nA = ref(3)
const nB = ref(3)
const edges = ref(new Set(['0-1', '1-0', '2-1']))
const selected = ref(null)

const ROW = 54
const TOP = 42
const LX = 80
const RX = 300
const W = 380
const H = computed(() => TOP * 2 + (Math.max(nA.value, nB.value) - 1) * ROW + 10)
const offA = computed(() => ((Math.max(nA.value, nB.value) - nA.value) * ROW) / 2)
const offB = computed(() => ((Math.max(nA.value, nB.value) - nB.value) * ROW) / 2)
const ya = (i) => TOP + offA.value + i * ROW
const yb = (j) => TOP + offB.value + j * ROW

const edgeList = computed(() =>
  [...edges.value]
    .map((k) => k.split('-').map(Number))
    .filter(([i, j]) => i < nA.value && j < nB.value),
)
const outs = computed(() => {
  const o = Array.from({ length: nA.value }, () => [])
  for (const [i, j] of edgeList.value) o[i].push(j)
  return o
})
const ins = computed(() => {
  const o = Array.from({ length: nB.value }, () => [])
  for (const [i, j] of edgeList.value) o[j].push(i)
  return o
})

const missing = computed(() => outs.value.map((o, i) => (o.length === 0 ? i : -1)).filter((i) => i >= 0))
const multi = computed(() => outs.value.map((o, i) => (o.length > 1 ? i : -1)).filter((i) => i >= 0))
const wellDefined = computed(() => !missing.value.length && !multi.value.length)
const collisions = computed(() => ins.value.map((o, j) => (o.length > 1 ? j : -1)).filter((j) => j >= 0))
const unhit = computed(() => ins.value.map((o, j) => (o.length === 0 ? j : -1)).filter((j) => j >= 0))
const injective = computed(() => wellDefined.value && !collisions.value.length)
const surjective = computed(() => wellDefined.value && !unhit.value.length)
const bijective = computed(() => injective.value && surjective.value)

const nameList = (arr, names) => arr.map((k) => names[k]).join('、')

function edgeClass(i, j) {
  if (outs.value[i].length > 1) return 'bad'
  if (wellDefined.value && ins.value[j].length > 1) return 'clash'
  return 'ok'
}

function clickA(i) {
  selected.value = selected.value === i ? null : i
}
function clickB(j) {
  if (selected.value === null) return
  const k = `${selected.value}-${j}`
  const s = new Set(edges.value)
  s.has(k) ? s.delete(k) : s.add(k)
  edges.value = s
  selected.value = null
}
function removeEdge(i, j) {
  const s = new Set(edges.value)
  s.delete(`${i}-${j}`)
  edges.value = s
}

function setFunction(f) {
  edges.value = new Set(f.map((j, i) => `${i}-${j}`))
  selected.value = null
}
function resize(which, d) {
  const r = which === 'A' ? nA : nB
  r.value = Math.min(MAX, Math.max(1, r.value + d))
  selected.value = null
}
function clearAll() {
  edges.value = new Set()
  selected.value = null
}
function randomFn() {
  setFunction(Array.from({ length: nA.value }, () => Math.floor(Math.random() * nB.value)))
}

// 第 k 个函数：把 k 写成 |B| 进制，第 i 位就是 f(第 i 个元素)
function fnOfIndex(k) {
  const f = []
  for (let i = 0; i < nA.value; i++) {
    f.push(k % nB.value)
    k = Math.floor(k / nB.value)
  }
  return f
}
const total = computed(() => nB.value ** nA.value)
const currentIndex = computed(() => {
  if (!wellDefined.value) return -1
  let k = 0
  for (let i = nA.value - 1; i >= 0; i--) k = k * nB.value + outs.value[i][0]
  return k
})
function step(d) {
  const k = currentIndex.value < 0 ? 0 : (currentIndex.value + d + total.value) % total.value
  setFunction(fnOfIndex(k))
}

const stats = computed(() => {
  let inj = 0, sur = 0, bij = 0
  for (let k = 0; k < total.value; k++) {
    const f = fnOfIndex(k)
    const hit = new Set(f)
    const isInj = hit.size === f.length
    const isSur = hit.size === nB.value
    if (isInj) inj++
    if (isSur) sur++
    if (isInj && isSur) bij++
  }
  return { inj, sur, bij }
})

function preset(kind) {
  const n = nA.value, m = nB.value
  if (kind === 'inj') {
    if (n > m) return flash(`单射需要 |A| ≤ |B|，当前 |A| = ${n} > |B| = ${m}，不存在单射。`)
    setFunction(Array.from({ length: n }, (_, i) => i))
  } else if (kind === 'sur') {
    if (n < m) return flash(`满射需要 |A| ≥ |B|，当前 |A| = ${n} < |B| = ${m}，不存在满射。`)
    setFunction(Array.from({ length: n }, (_, i) => Math.min(i, m - 1)))
  } else if (kind === 'bij') {
    if (n !== m) return flash(`双射需要 |A| = |B|，当前 ${n} ≠ ${m}，不存在双射。`)
    setFunction(Array.from({ length: n }, (_, i) => (i + 1) % m))
  }
  msg.value = ''
}
const msg = ref('')
function flash(s) {
  msg.value = s
}

const formula = computed(() =>
  wellDefined.value ? outs.value.map((o, i) => `f(${A_NAMES[i]}) = ${B_NAMES[o[0]]}`).join('，') : '',
)
const inverse = computed(() =>
  bijective.value ? ins.value.map((o, j) => `f⁻¹(${B_NAMES[j]}) = ${A_NAMES[o[0]]}`).join('，') : '',
)

function arrowPath(i, j) {
  const x1 = LX + 15, y1 = ya(i), x2 = RX - 17, y2 = yb(j)
  return `M${x1},${y1} L${x2},${y2}`
}
</script>

<template>
  <div class="ctfp-widget fc">
    <div class="ctfp-widget-title">函数性质检查器：连线定义一个从 A 到 B 的“函数”</div>
    <div class="hint">操作：先点左边 A 中的一个元素，再点右边 B 中的一个元素，就连上（或擦掉）一条箭头；点击箭头本身也可以擦掉它。</div>
    <div class="layout">
      <div class="canvas">
        <svg :viewBox="`0 0 ${W} ${H}`" :style="{ maxWidth: W + 'px' }" role="img" aria-label="两个集合之间的箭头图">
          <defs>
            <marker id="fc-ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" orient="auto-start-reverse">
              <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
            </marker>
          </defs>
          <rect :x="LX - 40" y="8" width="80" :height="H - 16" rx="40" class="set" />
          <rect :x="RX - 40" y="8" width="80" :height="H - 16" rx="40" class="set" />
          <text :x="LX" y="0" dy="-2" class="setname" text-anchor="middle">A</text>
          <text :x="RX" y="0" dy="-2" class="setname" text-anchor="middle">B</text>
          <g v-for="[i, j] in edgeList" :key="`${i}-${j}`" class="edge" :class="edgeClass(i, j)" @click="removeEdge(i, j)">
            <path :d="arrowPath(i, j)" class="hit" />
            <path :d="arrowPath(i, j)" class="line" marker-end="url(#fc-ah)" />
          </g>
          <g v-for="i in nA" :key="'a' + i" class="node" :class="{ sel: selected === i - 1, warn: outs[i - 1].length !== 1 }" @click="clickA(i - 1)">
            <circle :cx="LX" :cy="ya(i - 1)" r="15" />
            <text :x="LX" :y="ya(i - 1)" dy="5" text-anchor="middle">{{ A_NAMES[i - 1] }}</text>
          </g>
          <g v-for="j in nB" :key="'b' + j" class="node right" :class="{ target: selected !== null, unhit: wellDefined && ins[j - 1].length === 0 }" @click="clickB(j - 1)">
            <circle :cx="RX" :cy="yb(j - 1)" r="15" />
            <text :x="RX" :y="yb(j - 1)" dy="5" text-anchor="middle">{{ B_NAMES[j - 1] }}</text>
          </g>
        </svg>
        <div class="sizes">
          <span>|A| = {{ nA }}</span>
          <button class="ctfp-btn sm" @click="resize('A', -1)">−</button>
          <button class="ctfp-btn sm" @click="resize('A', 1)">+</button>
          <span class="gap">|B| = {{ nB }}</span>
          <button class="ctfp-btn sm" @click="resize('B', -1)">−</button>
          <button class="ctfp-btn sm" @click="resize('B', 1)">+</button>
        </div>
      </div>
      <div class="panel">
        <div class="row" :class="wellDefined ? 'yes' : 'no'">
          <span class="badge">{{ wellDefined ? '是' : '否' }}</span>
          <div>
            <b>良定义的函数</b>（A 的每个元素恰好一条箭头）
            <div v-if="missing.length" class="why">{{ nameList(missing, A_NAMES) }} 没有箭头：函数必须对每个输入都有输出。</div>
            <div v-if="multi.length" class="why">{{ nameList(multi, A_NAMES) }} 有多条箭头：函数的输出必须唯一。</div>
            <div v-if="wellDefined" class="why mono">{{ formula }}</div>
          </div>
        </div>
        <template v-if="wellDefined">
          <div class="row" :class="injective ? 'yes' : 'no'">
            <span class="badge">{{ injective ? '是' : '否' }}</span>
            <div>
              <b>单射</b>（没有两条箭头撞到同一点）
              <div v-for="j in collisions" :key="j" class="why">{{ nameList(ins[j], A_NAMES) }} 都映到了 {{ B_NAMES[j] }}（橙色箭头）。</div>
            </div>
          </div>
          <div class="row" :class="surjective ? 'yes' : 'no'">
            <span class="badge">{{ surjective ? '是' : '否' }}</span>
            <div>
              <b>满射</b>（B 的每个元素都被指到）
              <div v-if="unhit.length" class="why">{{ nameList(unhit, B_NAMES) }} 没有被任何箭头指到（虚线圆圈）。</div>
            </div>
          </div>
          <div class="row" :class="bijective ? 'yes' : 'no'">
            <span class="badge">{{ bijective ? '是' : '否' }}</span>
            <div>
              <b>双射</b>（既单又满：完美配对）
              <div v-if="bijective" class="why mono">反函数：{{ inverse }}</div>
            </div>
          </div>
        </template>
        <div v-else class="why muted">先让它成为一个函数，才谈得上单射、满射。</div>
      </div>
    </div>
    <div class="controls">
      <button class="ctfp-btn" @click="preset('inj')">单射示例</button>
      <button class="ctfp-btn" @click="preset('sur')">满射示例</button>
      <button class="ctfp-btn" @click="preset('bij')">双射示例</button>
      <button class="ctfp-btn" @click="randomFn">随机函数</button>
      <button class="ctfp-btn" @click="clearAll">清空</button>
    </div>
    <div v-if="msg" class="msg">{{ msg }}</div>
    <div class="count">
      <div>
        从 A 到 B 一共有 <b>{{ nB }}<sup>{{ nA }}</sup> = {{ total }}</b> 个函数，其中单射 <b>{{ stats.inj }}</b> 个，满射 <b>{{ stats.sur }}</b> 个，双射 <b>{{ stats.bij }}</b> 个。
      </div>
      <div class="enum">
        <button class="ctfp-btn sm" @click="step(-1)">◀</button>
        <span>{{ currentIndex >= 0 ? `当前是第 ${currentIndex + 1} / ${total} 个函数` : '逐个浏览全部函数' }}</span>
        <button class="ctfp-btn sm" @click="step(1)">▶</button>
      </div>
    </div>
  </div>
</template>

<style scoped>
.hint {
  font-size: 13px;
  color: var(--vp-c-text-2);
  margin-bottom: 10px;
  line-height: 1.6;
}
.layout {
  display: grid;
  grid-template-columns: minmax(0, 1fr) minmax(0, 1fr);
  gap: 16px;
  align-items: start;
}
@media (max-width: 720px) {
  .layout {
    grid-template-columns: minmax(0, 1fr);
  }
}
.canvas {
  display: flex;
  flex-direction: column;
  align-items: center;
  min-width: 0;
}
svg {
  width: 100%;
  height: auto;
  overflow: visible;
  margin-top: 14px;
}
.set {
  fill: var(--vp-c-bg);
  stroke: var(--vp-c-divider);
}
.setname {
  font-size: 15px;
  font-weight: 600;
  fill: var(--vp-c-text-2);
}
.node {
  cursor: pointer;
}
.node circle {
  fill: var(--vp-c-bg-soft);
  stroke: var(--vp-c-text-2);
  stroke-width: 1.5;
  transition: all 0.2s;
}
.node text {
  font-size: 14px;
  fill: var(--vp-c-text-1);
  pointer-events: none;
  font-family: var(--vp-font-family-mono);
}
.node:hover circle {
  stroke: var(--vp-c-brand-1);
}
.node.warn circle {
  stroke: var(--vp-c-danger-1);
}
.node.sel circle {
  fill: var(--vp-c-brand-1);
  stroke: var(--vp-c-brand-1);
}
.node.sel text {
  fill: var(--vp-c-white, #fff);
}
.node.right.target circle {
  stroke: var(--vp-c-brand-1);
  stroke-dasharray: 3 2;
}
.node.right.unhit circle {
  stroke-dasharray: 4 3;
  stroke: var(--vp-c-warning-1);
}
.edge {
  cursor: pointer;
}
.edge .hit {
  stroke: transparent;
  stroke-width: 12;
}
.edge .line {
  stroke-width: 2;
  fill: none;
  transition: stroke 0.2s;
}
.edge.ok .line {
  stroke: var(--vp-c-brand-1);
}
.edge.clash .line {
  stroke: var(--vp-c-warning-1);
}
.edge.bad .line {
  stroke: var(--vp-c-danger-1);
}
.edge:hover .line {
  stroke-width: 3;
}
.sizes {
  display: flex;
  align-items: center;
  gap: 6px;
  font-size: 13px;
  color: var(--vp-c-text-2);
  margin-top: 8px;
  flex-wrap: wrap;
  justify-content: center;
}
.sizes .gap {
  margin-left: 14px;
}
.ctfp-btn.sm {
  padding: 1px 10px;
}
.panel {
  display: flex;
  flex-direction: column;
  gap: 10px;
  min-width: 0;
}
.row {
  display: flex;
  gap: 10px;
  align-items: flex-start;
  font-size: 14px;
  line-height: 1.6;
  padding: 8px 10px;
  border-radius: 8px;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
}
.badge {
  flex: none;
  font-size: 12px;
  font-weight: 600;
  padding: 1px 8px;
  border-radius: 999px;
  margin-top: 2px;
}
.row.yes .badge {
  background: color-mix(in srgb, var(--vp-c-green-1, #18794e) 18%, transparent);
  color: var(--vp-c-green-1, #18794e);
}
.row.no .badge {
  background: color-mix(in srgb, var(--vp-c-danger-1) 15%, transparent);
  color: var(--vp-c-danger-1);
}
.why {
  font-size: 13px;
  color: var(--vp-c-text-2);
}
.why.mono {
  font-family: var(--vp-font-family-mono);
  font-size: 12.5px;
  word-break: break-word;
}
.why.muted {
  padding: 4px 10px;
}
.controls {
  display: flex;
  flex-wrap: wrap;
  gap: 8px;
  margin-top: 14px;
}
.msg {
  margin-top: 8px;
  font-size: 13px;
  color: var(--vp-c-warning-1);
}
.count {
  margin-top: 12px;
  padding-top: 10px;
  border-top: 1px dashed var(--vp-c-divider);
  font-size: 14px;
  line-height: 1.7;
}
.enum {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-top: 6px;
  font-size: 13px;
  color: var(--vp-c-text-2);
  flex-wrap: wrap;
}
</style>
