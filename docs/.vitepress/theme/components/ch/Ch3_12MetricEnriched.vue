<script setup>
import { ref, reactive, computed } from 'vue'

const W = 520
const H = 320
const UNIT = 40

const names = ['A', 'B', 'C', 'D']
const pts = reactive([
  { x: 90, y: 250 },
  { x: 250, y: 90 },
  { x: 430, y: 230 },
  { x: 300, y: 270 },
])

const modes = [
  { id: 'euclid', label: '直线距离（对称）' },
  { id: 'uphill', label: '登山距离（上坡加价）' },
  { id: 'square', label: '距离的平方（反例）' },
]
const mode = ref('euclid')

const sel = reactive({ a: 0, b: 1, c: 2 })
const roles = [
  { key: 'a', label: 'a', color: 'var(--vp-c-brand-1)' },
  { key: 'b', label: 'b', color: 'var(--vp-c-warning-1)' },
  { key: 'c', label: 'c', color: 'var(--vp-c-success-1, #18794e)' },
]

function euclid(p, q) {
  return Math.hypot(p.x - q.x, p.y - q.y) / UNIT
}
// 海拔 = 越靠上越高；上坡每单位海拔额外付 1.5 份代价，下坡不额外付费
function height(p) {
  return (H - p.y) / UNIT
}
function dist(i, j) {
  const p = pts[i], q = pts[j]
  if (i === j) return 0
  if (mode.value === 'euclid') return euclid(p, q)
  if (mode.value === 'uphill') return euclid(p, q) + 1.5 * Math.max(0, height(q) - height(p))
  const d = euclid(p, q)
  return d * d
}

const fmt = (x) => (Math.round(x * 10) / 10).toFixed(1)
const EPS = 1e-9

const matrix = computed(() => names.map((_, i) => names.map((_, j) => dist(i, j))))

const check = computed(() => {
  const { a, b, c } = sel
  const ab = matrix.value[a][b]
  const bc = matrix.value[b][c]
  const ac = matrix.value[a][c]
  return { ab, bc, ac, sum: ab + bc, ok: ab + bc + EPS >= ac }
})

const failures = computed(() => {
  const out = []
  const n = names.length
  for (let a = 0; a < n; a++)
    for (let b = 0; b < n; b++)
      for (let c = 0; c < n; c++) {
        const m = matrix.value
        if (m[a][b] + m[b][c] + EPS < m[a][c]) out.push(`${names[a]}→${names[b]}→${names[c]}`)
      }
  return out
})

function pick(role, i) {
  sel[role] = i
}

// 拖拽
const svgEl = ref(null)
const dragging = ref(-1)
function toLocal(evt) {
  const svg = svgEl.value
  const r = svg.getBoundingClientRect()
  return {
    x: Math.min(W - 16, Math.max(16, ((evt.clientX - r.left) / r.width) * W)),
    y: Math.min(H - 16, Math.max(16, ((evt.clientY - r.top) / r.height) * H)),
  }
}
function down(i, evt) {
  dragging.value = i
  evt.target.setPointerCapture?.(evt.pointerId)
}
function move(evt) {
  if (dragging.value < 0) return
  const p = toLocal(evt)
  pts[dragging.value].x = p.x
  pts[dragging.value].y = p.y
}
function up() {
  dragging.value = -1
}

function seg(i, j, shrink = 18) {
  const p = pts[i], q = pts[j]
  const dx = q.x - p.x, dy = q.y - p.y
  const L = Math.hypot(dx, dy) || 1
  const ux = dx / L, uy = dy / L
  return {
    x1: p.x + ux * shrink, y1: p.y + uy * shrink,
    x2: q.x - ux * (shrink + 4), y2: q.y - uy * (shrink + 4),
    mx: (p.x + q.x) / 2 - uy * 14, my: (p.y + q.y) / 2 + ux * 14,
  }
}
const segAB = computed(() => seg(sel.a, sel.b))
const segBC = computed(() => seg(sel.b, sel.c))
const segAC = computed(() => seg(sel.a, sel.c))
const degenerate = computed(() => sel.a === sel.b || sel.b === sel.c || sel.a === sel.c)

function roleOf(i) {
  return roles.filter((r) => sel[r.key] === i)
}
</script>

<template>
  <div class="ctfp-widget metric">
    <div class="ctfp-widget-title">度量空间即富集范畴：复合 = 三角不等式</div>
    <div class="hint">拖动平面上的点；在下方为 a、b、c 选择对象。hom-对象 C(x, y) 就是从 x 到 y 的距离。</div>

    <div class="modes">
      <button v-for="m in modes" :key="m.id" class="ctfp-btn" :class="{ on: mode === m.id }" @click="mode = m.id">
        {{ m.label }}
      </button>
    </div>

    <svg
      ref="svgEl"
      :viewBox="`0 0 ${W} ${H}`"
      class="plane"
      @pointermove="move"
      @pointerup="up"
      @pointerleave="up"
    >
      <defs>
        <marker id="ch312-ah" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="8" markerHeight="8" orient="auto-start-reverse">
          <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
        </marker>
      </defs>
      <g v-if="mode === 'uphill'" class="contours">
        <line v-for="k in 7" :key="k" x1="0" :x2="W" :y1="k * UNIT" :y2="k * UNIT" />
        <text x="6" y="14">高处</text>
        <text :x="6" :y="H - 6">低处</text>
      </g>
      <template v-if="!degenerate">
        <line :x1="segAC.x1" :y1="segAC.y1" :x2="segAC.x2" :y2="segAC.y2" class="edge direct" :class="{ bad: !check.ok }" marker-end="url(#ch312-ah)" />
        <line :x1="segAB.x1" :y1="segAB.y1" :x2="segAB.x2" :y2="segAB.y2" class="edge leg1" marker-end="url(#ch312-ah)" />
        <line :x1="segBC.x1" :y1="segBC.y1" :x2="segBC.x2" :y2="segBC.y2" class="edge leg2" marker-end="url(#ch312-ah)" />
        <text :x="segAB.mx" :y="segAB.my" class="elabel leg1t">{{ fmt(check.ab) }}</text>
        <text :x="segBC.mx" :y="segBC.my" class="elabel leg2t">{{ fmt(check.bc) }}</text>
        <text :x="segAC.mx" :y="segAC.my" class="elabel directt" :class="{ bad: !check.ok }">{{ fmt(check.ac) }}</text>
      </template>
      <g v-for="(p, i) in pts" :key="i" class="pt" :class="{ drag: dragging === i }" @pointerdown="down(i, $event)">
        <circle :cx="p.x" :cy="p.y" r="16" />
        <text :x="p.x" :y="p.y + 5" class="pname">{{ names[i] }}</text>
        <text v-for="(r, k) in roleOf(i)" :key="r.key" :x="p.x - 30 - k * 12" :y="p.y - 16" class="role" :style="{ fill: r.color }">{{ r.label }}</text>
      </g>
    </svg>

    <div class="pickers">
      <div v-for="r in roles" :key="r.key" class="picker">
        <span class="rname" :style="{ color: r.color }">{{ r.label }} =</span>
        <button v-for="(n, i) in names" :key="n" class="ctfp-btn small" :class="{ on: sel[r.key] === i }" @click="pick(r.key, i)">{{ n }}</button>
      </div>
    </div>

    <div class="verdict" :class="check.ok ? 'ok' : 'bad'">
      <div class="formula">
        <span class="leg2c">C(b, c)</span> ⊗ <span class="leg1c">C(a, b)</span>
        = {{ fmt(check.bc) }} + {{ fmt(check.ab) }} = <b>{{ fmt(check.sum) }}</b>
        <span class="rel">{{ check.ok ? '≥' : '<' }}</span>
        <b>{{ fmt(check.ac) }}</b> = <span class="directc">C(a, c)</span>
      </div>
      <div v-if="check.ok" class="msg">✓ V 中存在态射 {{ fmt(check.sum) }} → {{ fmt(check.ac) }}，复合 ∘ : C(b,c) ⊗ C(a,b) → C(a,c) 有定义。</div>
      <div v-else class="msg">✗ {{ fmt(check.sum) }} &lt; {{ fmt(check.ac) }}：V 中没有这样的态射，复合无从定义——这不是一个富集范畴。</div>
      <div class="msg small">恒等：j_a : 0 → C(a, a)，即 0 ≥ C(a, a) = {{ fmt(matrix[sel.a][sel.a]) }} ✓</div>
    </div>

    <div class="tablewrap">
      <table class="dm">
        <thead>
          <tr><th>C(行, 列)</th><th v-for="n in names" :key="n">{{ n }}</th></tr>
        </thead>
        <tbody>
          <tr v-for="(row, i) in matrix" :key="i">
            <th>{{ names[i] }}</th>
            <td
              v-for="(v, j) in row"
              :key="j"
              :class="{
                hab: i === sel.a && j === sel.b,
                hbc: i === sel.b && j === sel.c,
                hac: i === sel.a && j === sel.c,
              }"
            >{{ fmt(v) }}</td>
          </tr>
        </tbody>
      </table>
      <div class="summary" :class="failures.length ? 'bad' : 'ok'">
        <template v-if="!failures.length">全部 64 个三元组 (a, b, c) 都满足三角不等式：这是一个在 ([0,∞], ≥, +) 上富集的范畴。</template>
        <template v-else>有 {{ failures.length }} 个三元组的复合不存在，例如 {{ failures.slice(0, 4).join('，') }}{{ failures.length > 4 ? '……' : '' }}</template>
      </div>
      <div v-if="mode === 'uphill'" class="note">登山距离不对称：表格里 C(x, y) 与 C(y, x) 一般不同（往上走更贵）。它仍满足三角不等式。</div>
      <div v-if="mode === 'square'" class="note">提示：把 b 拖到 a 与 c 之间的连线附近，两段各自的平方之和会远小于整段的平方。</div>
    </div>
  </div>
</template>

<style scoped>
.metric { max-width: 100%; }
.hint { font-size: 13px; color: var(--vp-c-text-2); margin-bottom: 8px; }
.modes { display: flex; flex-wrap: wrap; gap: 6px; margin-bottom: 8px; }
.plane {
  width: 100%;
  max-width: 520px;
  display: block;
  margin: 0 auto;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
  border-radius: 10px;
  touch-action: none;
  user-select: none;
}
.contours line { stroke: var(--vp-c-divider); stroke-dasharray: 3 5; }
.contours text { font-size: 11px; fill: var(--vp-c-text-3); }
.edge { stroke-width: 2.5; }
.leg1 { stroke: var(--vp-c-warning-1); }
.leg2 { stroke: var(--vp-c-success-1, #18794e); }
.direct { stroke: var(--vp-c-brand-1); stroke-dasharray: 7 5; }
.direct.bad { stroke: var(--vp-c-danger-1); stroke-width: 3.5; }
.elabel { font-size: 13px; font-weight: 600; text-anchor: middle; paint-order: stroke; stroke: var(--vp-c-bg); stroke-width: 4px; }
.leg1t { fill: var(--vp-c-warning-1); }
.leg2t { fill: var(--vp-c-success-1, #18794e); }
.directt { fill: var(--vp-c-brand-1); }
.directt.bad { fill: var(--vp-c-danger-1); }
.pt { cursor: grab; }
.pt.drag { cursor: grabbing; }
.pt circle { fill: var(--vp-c-bg-soft); stroke: var(--vp-c-text-1); stroke-width: 1.6; }
.pt.drag circle { stroke: var(--vp-c-brand-1); stroke-width: 2.5; }
.pname { font-size: 14px; font-weight: 700; text-anchor: middle; fill: var(--vp-c-text-1); pointer-events: none; }
.role { font-size: 13px; font-weight: 700; font-style: italic; pointer-events: none; }
.pickers { display: flex; flex-wrap: wrap; gap: 6px 18px; justify-content: center; margin: 10px 0; }
.picker { display: flex; align-items: center; gap: 4px; }
.rname { font-style: italic; font-weight: 700; margin-right: 2px; }
.ctfp-btn.small { padding: 2px 9px; }
.verdict { border-radius: 8px; padding: 8px 12px; margin: 6px 0 10px; border: 1px solid var(--vp-c-divider); background: var(--vp-c-bg); }
.verdict.ok { border-color: var(--vp-c-success-1, #18794e); }
.verdict.bad { border-color: var(--vp-c-danger-1); }
.formula { font-size: 15px; text-align: center; font-family: var(--vp-font-family-mono); flex-wrap: wrap; }
.rel { font-size: 18px; font-weight: 700; margin: 0 4px; }
.leg1c { color: var(--vp-c-warning-1); }
.leg2c { color: var(--vp-c-success-1, #18794e); }
.directc { color: var(--vp-c-brand-1); }
.msg { font-size: 13px; margin-top: 4px; text-align: center; }
.verdict.ok .msg:first-of-type { color: var(--vp-c-success-1, #18794e); }
.verdict.bad .msg:first-of-type { color: var(--vp-c-danger-1); }
.msg.small { color: var(--vp-c-text-2) !important; font-size: 12px; }
.tablewrap { overflow-x: auto; }
.tablewrap table.dm { margin: 0 auto; border-collapse: collapse; font-size: 13px; display: table; }
th, td { padding: 3px 12px; border: 1px solid var(--vp-c-divider); text-align: center; font-family: var(--vp-font-family-mono); }
td.hab { background: color-mix(in srgb, var(--vp-c-warning-1) 22%, transparent); }
td.hbc { background: color-mix(in srgb, var(--vp-c-success-1, #18794e) 22%, transparent); }
td.hac { background: color-mix(in srgb, var(--vp-c-brand-1) 22%, transparent); }
.summary { font-size: 13px; text-align: center; margin-top: 8px; }
.summary.ok { color: var(--vp-c-success-1, #18794e); }
.summary.bad { color: var(--vp-c-danger-1); }
.note { font-size: 12px; color: var(--vp-c-text-2); text-align: center; margin-top: 4px; }
</style>
