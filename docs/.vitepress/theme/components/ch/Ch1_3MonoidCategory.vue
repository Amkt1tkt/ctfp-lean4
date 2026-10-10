<script setup>
// 幺半群即单对象范畴：一个对象、若干自环箭头；点两条箭头看复合，同时在 hom-集（点）和复合表里高亮。
import { computed, ref } from 'vue'

const monoids = [
  {
    key: 'z3',
    name: '模 3 加法',
    set: 'ℤ₃ = {0, 1, 2}',
    sym: '+',
    elems: [0, 1, 2],
    label: (x) => `+${x}`,
    op: (g, f) => (g + f) % 3,
    unit: 0,
    act: (x, s) => (x + s) % 3,
    carrier: [0, 1, 2],
    show: (s) => String(s),
    note: '每条箭头都有逆：+1 与 +2 复合得到恒等。这是一个群。',
  },
  {
    key: 'and',
    name: 'Bool 与（∧）',
    set: 'Bool = {T, F}',
    sym: '∧',
    elems: [true, false],
    label: (x) => (x ? 'T' : 'F'),
    op: (g, f) => g && f,
    unit: true,
    act: (x, s) => x && s,
    carrier: [true, false],
    show: (s) => (s ? 'T' : 'F'),
    note: 'T 是恒等态射；F 是“一律变成 F”的常函数，和谁复合都得 F。',
  },
  {
    key: 'or',
    name: 'Bool 或（∨）',
    set: 'Bool = {T, F}',
    sym: '∨',
    elems: [false, true],
    label: (x) => (x ? 'T' : 'F'),
    op: (g, f) => g || f,
    unit: false,
    act: (x, s) => x || s,
    carrier: [false, true],
    show: (s) => (s ? 'T' : 'F'),
    note: '这次 F 是恒等态射，T 是“一律变成 T”的常函数。',
  },
  {
    key: 'nat',
    name: 'ℕ 加法（只画 +0…+4）',
    set: 'ℕ = {0, 1, 2, …}',
    sym: '+',
    elems: [0, 1, 2, 3, 4],
    label: (x) => `+${x}`,
    op: (g, f) => g + f,
    unit: 0,
    act: (x, s) => x + s,
    carrier: [0, 1, 2, 3],
    show: (s) => String(s),
    note: 'ℕ 的 hom-集是无限的：+3 与 +4 复合得到 +7，它不在图上，但同样是一条态射。',
  },
]

const mi = ref(0)
const M = computed(() => monoids[mi.value])
const f = ref(null) // 先走的箭头（下标或值）
const g = ref(null) // 后走的箭头

const has = (x) => x !== null
const result = computed(() => (has(f.value) && has(g.value) ? M.value.op(g.value, f.value) : null))
const resultIdx = computed(() => (result.value === null ? -1 : M.value.elems.indexOf(result.value)))

function pick(x) {
  if (!has(f.value) || has(g.value)) {
    f.value = x
    g.value = null
  } else {
    g.value = x
  }
}
function pickCell(gx, fx) {
  f.value = fx
  g.value = gx
}
function choose(i) {
  mi.value = i
  f.value = null
  g.value = null
}
function reset() {
  f.value = null
  g.value = null
}

const W = 320
const H = 300
const CX = W / 2
const CY = H / 2 + 4
const R = 30

const loops = computed(() => {
  const n = M.value.elems.length
  return M.value.elems.map((x, i) => {
    const th = -Math.PI / 2 + (2 * Math.PI * i) / n
    const spread = n > 3 ? 0.22 : 0.3
    const out = n > 3 ? 92 : 104
    const P = (ang, r) => [CX + r * Math.cos(ang), CY + r * Math.sin(ang)]
    const [sx, sy] = P(th - spread, R)
    const [ex, ey] = P(th + spread, R + 4)
    const [c1x, c1y] = P(th - spread * 2.1, R + out)
    const [c2x, c2y] = P(th + spread * 2.1, R + out)
    const [lx, ly] = P(th, R + out * 0.86)
    return { x, d: `M${sx},${sy} C${c1x},${c1y} ${c2x},${c2y} ${ex},${ey}`, lx, ly, isId: x === M.value.unit }
  })
})

function roleOf(x) {
  const r = []
  if (has(f.value) && f.value === x) r.push('f')
  if (has(g.value) && g.value === x) r.push('g')
  if (result.value !== null && result.value === x) r.push('h')
  return r
}
function strokeOf(x) {
  const r = roleOf(x)
  if (r.includes('h') && has(g.value)) return 'var(--vp-c-success-1, #18794e)'
  if (r.includes('g')) return 'var(--vp-c-warning-1)'
  if (r.includes('f')) return 'var(--vp-c-brand-1)'
  return 'var(--vp-c-text-2)'
}
const L = (x) => M.value.label(x)
</script>

<template>
  <div class="ctfp-widget ch13m">
    <div class="ctfp-widget-title">幺半群 = 只有一个对象的范畴</div>
    <div class="row">
      <button v-for="(m, i) in monoids" :key="m.key" class="ctfp-btn" :class="{ on: i === mi }" @click="choose(i)">{{ m.name }}</button>
    </div>
    <p class="hint">先点一条箭头作为 <b class="cf">f</b>（先走），再点一条作为 <b class="cg">g</b>（后走），看看复合 <b class="ch">g ∘ f</b> 是哪一条。也可以直接点复合表里的格子。</p>

    <div class="panes">
      <svg :viewBox="`0 0 ${W} ${H}`" class="obj" role="img" aria-label="单对象范畴">
        <defs>
          <marker id="ch13m-ah" viewBox="0 0 10 10" refX="8.5" refY="5" markerUnits="userSpaceOnUse" markerWidth="10" markerHeight="10" orient="auto-start-reverse">
            <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
          </marker>
        </defs>
        <g v-for="lp in loops" :key="String(lp.x)" class="loop" @click="pick(lp.x)">
          <path :d="lp.d" fill="none" stroke="transparent" stroke-width="16" />
          <path
            :d="lp.d" fill="none" :stroke="strokeOf(lp.x)"
            :stroke-width="roleOf(lp.x).length ? 3.2 : 1.8"
            :stroke-dasharray="lp.isId ? '5 4' : null"
            marker-end="url(#ch13m-ah)"
          />
          <text :x="lp.lx" :y="lp.ly" text-anchor="middle" dominant-baseline="middle" :fill="strokeOf(lp.x)" class="lbl">{{ L(lp.x) }}</text>
        </g>
        <circle :cx="CX" :cy="CY" :r="R" class="blob" />
        <text :x="CX" :y="CY" text-anchor="middle" dominant-baseline="middle" class="blobtxt">m</text>
      </svg>

      <div class="side">
        <div class="box">
          <div class="boxtitle">hom-集 𝓜(m, m)：把箭头看成点</div>
          <div class="pts">
            <span v-for="x in M.elems" :key="String(x)" class="pt" :class="roleOf(x)" @click="pick(x)">{{ L(x) }}</span>
            <span v-if="M.key === 'nat'" class="pt more">…</span>
          </div>
          <div class="small">恒等态射（单位元）：<b>{{ L(M.unit) }}</b>（虚线）</div>
        </div>
        <div class="box eq">
          <template v-if="has(f) && has(g)">
            <div><b class="cg">{{ L(g) }}</b> ∘ <b class="cf">{{ L(f) }}</b> = <b class="ch">{{ L(result) }}</b></div>
            <div class="small">作为态射：先走 {{ L(f) }}，再走 {{ L(g) }}<br />作为集合元素：{{ M.show(g) }} {{ M.sym }} {{ M.show(f) }} = {{ M.show(result) }}{{ M.key === 'z3' ? '（模 3）' : '' }}</div>
            <div v-if="resultIdx < 0" class="small warn">{{ L(result) }} 不在图上——ℕ 有无穷多条态射</div>
          </template>
          <template v-else-if="has(f)">
            <div>已选 <b class="cf">f = {{ L(f) }}</b>，再选 g</div>
          </template>
          <template v-else>
            <div class="small">还没有选箭头</div>
          </template>
        </div>
        <div v-if="has(f)" class="box">
          <div class="boxtitle">把 {{ L(has(g) ? result : f) }} 看成集合 {{ M.set }} 上的函数（“加法器”）</div>
          <div class="maps">
            <span v-for="s in M.carrier" :key="String(s)" class="map">{{ M.show(s) }} ↦ {{ M.show(M.act(has(g) ? result : f, s)) }}</span>
            <span v-if="M.key === 'nat'" class="map">…</span>
          </div>
        </div>
      </div>
    </div>

    <div class="tablewrap">
      <table class="tbl">
        <thead>
          <tr>
            <th class="corner">g ∘ f</th>
            <th v-for="fx in M.elems" :key="'h' + String(fx)" :class="{ selc: has(f) && f === fx }">f = {{ L(fx) }}</th>
          </tr>
        </thead>
        <tbody>
          <tr v-for="gx in M.elems" :key="'r' + String(gx)">
            <th :class="{ selr: has(g) && g === gx }">g = {{ L(gx) }}</th>
            <td
              v-for="fx in M.elems" :key="String(gx) + String(fx)"
              :class="{ cell: true, hit: has(f) && has(g) && f === fx && g === gx }"
              @click="pickCell(gx, fx)"
            >{{ L(M.op(gx, fx)) }}</td>
          </tr>
        </tbody>
      </table>
    </div>
    <div class="foot">
      <span class="small">{{ M.note }}</span>
      <button class="ctfp-btn" @click="reset">清除选择</button>
    </div>
  </div>
</template>

<style scoped>
.row { display: flex; flex-wrap: wrap; gap: 6px; margin-bottom: 8px; }
.hint { font-size: 13px; color: var(--vp-c-text-2); margin: 4px 0 10px; line-height: 1.6; }
.panes { display: flex; flex-wrap: wrap; gap: 14px; align-items: flex-start; }
.obj { width: 320px; max-width: 100%; flex: 0 0 auto; }
.side { flex: 1 1 240px; min-width: 0; display: flex; flex-direction: column; gap: 8px; }
.box { border: 1px solid var(--vp-c-divider); border-radius: 8px; padding: 8px 10px; background: var(--vp-c-bg); }
.boxtitle { font-size: 12px; color: var(--vp-c-text-2); margin-bottom: 6px; }
.eq { font-size: 15px; min-height: 64px; }
.small { font-size: 12px; color: var(--vp-c-text-2); line-height: 1.6; }
.warn { color: var(--vp-c-warning-1); }
.pts { display: flex; flex-wrap: wrap; gap: 8px; margin-bottom: 6px; }
.pt {
  min-width: 34px; text-align: center; padding: 3px 8px; border-radius: 999px; cursor: pointer;
  border: 1.5px solid var(--vp-c-divider); font-family: var(--vp-font-family-mono); font-size: 13px;
}
.pt.more { cursor: default; border-style: dashed; }
.pt.f { border-color: var(--vp-c-brand-1); color: var(--vp-c-brand-1); }
.pt.g { border-color: var(--vp-c-warning-1); color: var(--vp-c-warning-1); }
.pt.h { background: var(--vp-c-success-soft, rgba(24, 121, 78, 0.14)); border-color: var(--vp-c-success-1, #18794e); }
.maps { display: flex; flex-wrap: wrap; gap: 6px 14px; font-family: var(--vp-font-family-mono); font-size: 13px; }
.cf { color: var(--vp-c-brand-1); }
.cg { color: var(--vp-c-warning-1); }
.ch { color: var(--vp-c-success-1, #18794e); }
.loop { cursor: pointer; }
.lbl { font-size: 14px; font-weight: 600; font-family: var(--vp-font-family-mono); }
.blob { fill: var(--vp-c-brand-soft); stroke: var(--vp-c-brand-1); stroke-width: 2; }
.blobtxt { font-size: 18px; font-style: italic; fill: var(--vp-c-text-1); }
.tablewrap { overflow-x: auto; max-width: 100%; margin-top: 12px; }
.tbl { border-collapse: collapse; margin: 0; font-size: 13px; display: table; }
.tbl th, .tbl td { border: 1px solid var(--vp-c-divider); padding: 4px 10px; text-align: center; font-family: var(--vp-font-family-mono); }
.tbl th { background: var(--vp-c-bg-soft); font-weight: 500; }
.tbl .corner { color: var(--vp-c-text-2); }
.tbl .selc { color: var(--vp-c-brand-1); }
.tbl .selr { color: var(--vp-c-warning-1); }
.tbl td.cell { cursor: pointer; background: var(--vp-c-bg); }
.tbl td.cell:hover { background: var(--vp-c-bg-soft); }
.tbl td.hit { background: var(--vp-c-success-soft, rgba(24, 121, 78, 0.18)); color: var(--vp-c-success-1, #18794e); font-weight: 700; }
.foot { display: flex; flex-wrap: wrap; justify-content: space-between; align-items: center; gap: 8px; margin-top: 10px; }
</style>
