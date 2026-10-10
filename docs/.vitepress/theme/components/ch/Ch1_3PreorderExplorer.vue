<script setup>
// 预序范畴可视化：有限的序，点两个对象查看 hom-集；可切换“只画生成箭头 / 画出全部箭头”。
import { computed, ref } from 'vue'

const subsetLabel = (m) => {
  if (m === 0) return '∅'
  return '{' + ['a', 'b', 'c'].filter((_, i) => m & (1 << i)).join(',') + '}'
}

const examples = [
  {
    key: 'dvd',
    name: '整除：12 的因子',
    desc: 'a → b 表示 a 整除 b',
    nodes: [
      { v: 1, x: 180, y: 325 }, { v: 2, x: 95, y: 232 }, { v: 3, x: 268, y: 232 },
      { v: 4, x: 52, y: 132 }, { v: 6, x: 215, y: 132 }, { v: 12, x: 135, y: 42 },
    ],
    label: (v) => String(v),
    le: (a, b) => b % a === 0,
  },
  {
    key: 'sub',
    name: '子集：{a,b,c} 的子集',
    desc: 'A → B 表示 A ⊆ B',
    nodes: [
      { v: 0, x: 185, y: 328 },
      { v: 1, x: 65, y: 232 }, { v: 2, x: 185, y: 232 }, { v: 4, x: 305, y: 232 },
      { v: 3, x: 65, y: 135 }, { v: 5, x: 185, y: 135 }, { v: 6, x: 305, y: 135 },
      { v: 7, x: 185, y: 40 },
    ],
    label: subsetLabel,
    le: (a, b) => (a & ~b) === 0,
  },
  {
    key: 'len',
    name: '字符串按长度',
    desc: 's → t 表示 s.length ≤ t.length',
    nodes: [
      { v: 'a', x: 100, y: 300 }, { v: 'b', x: 270, y: 300 },
      { v: 'ab', x: 100, y: 185 }, { v: 'cd', x: 270, y: 185 },
      { v: 'xyz', x: 185, y: 55 },
    ],
    label: (v) => `"${v}"`,
    le: (a, b) => a.length <= b.length,
  },
  {
    key: 'tot',
    name: '≤：{1,…,5}',
    desc: 'a → b 表示 a ≤ b',
    nodes: [
      { v: 1, x: 55, y: 320 }, { v: 2, x: 85, y: 205 }, { v: 3, x: 160, y: 118 },
      { v: 4, x: 255, y: 68 }, { v: 5, x: 345, y: 52 },
    ],
    label: (v) => String(v),
    le: (a, b) => a <= b,
  },
]

const ei = ref(0)
const showAll = ref(false)
const selA = ref(null)
const selB = ref(null)
const E = computed(() => examples[ei.value])

function choose(i) {
  ei.value = i
  selA.value = null
  selB.value = null
}
function clickNode(i) {
  if (selA.value === null || selB.value !== null) {
    selA.value = i
    selB.value = null
  } else {
    selB.value = i
  }
}

const N = computed(() => E.value.nodes.length)
const le = (i, j) => E.value.le(E.value.nodes[i].v, E.value.nodes[j].v)
const equiv = (i, j) => le(i, j) && le(j, i)
const L = (i) => E.value.label(E.value.nodes[i].v)

const isGen = (i, j) => {
  if (i === j || !le(i, j)) return false
  if (le(j, i)) return true
  for (let k = 0; k < N.value; k++) {
    if (k === i || k === j || equiv(k, i) || equiv(k, j)) continue
    if (le(i, k) && le(k, j)) return false
  }
  return true
}

const props4 = computed(() => {
  const n = N.value
  let anti = null
  let total = null
  for (let i = 0; i < n; i++)
    for (let j = 0; j < n; j++) {
      if (i < j && equiv(i, j) && !anti) anti = [i, j]
      if (i < j && !le(i, j) && !le(j, i) && !total) total = [i, j]
    }
  let kind = '全序'
  if (anti) kind = '预序（不是偏序）'
  else if (total) kind = '偏序（不是全序）'
  return { anti, total, kind }
})

const counts = computed(() => {
  let all = 0
  let gen = 0
  for (let i = 0; i < N.value; i++)
    for (let j = 0; j < N.value; j++) {
      if (le(i, j)) all++
      if (isGen(i, j)) gen++
    }
  return { all, gen }
})

const nodeW = (i) => Math.max(34, 12 + L(i).length * 8.5)
const NODE_H = 28

function distToSeg(px, py, ax, ay, bx, by) {
  const dx = bx - ax, dy = by - ay
  const t = Math.max(0, Math.min(1, ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy || 1)))
  return Math.hypot(px - (ax + t * dx), py - (ay + t * dy))
}

function boxExit(i, ux, uy) {
  const hw = nodeW(i) / 2 + 3, hh = NODE_H / 2 + 3
  const tx = Math.abs(ux) > 1e-6 ? hw / Math.abs(ux) : Infinity
  const ty = Math.abs(uy) > 1e-6 ? hh / Math.abs(uy) : Infinity
  return Math.min(tx, ty)
}

function arrowPath(i, j, extraBend = 0) {
  const A = E.value.nodes[i], B = E.value.nodes[j]
  let bend = extraBend
  if (le(j, i)) bend += 16
  if (!bend) {
    for (let k = 0; k < N.value; k++) {
      if (k === i || k === j) continue
      const C = E.value.nodes[k]
      if (distToSeg(C.x, C.y, A.x, A.y, B.x, B.y) < 24) { bend = 34; break }
    }
  }
  const dx = B.x - A.x, dy = B.y - A.y
  const len = Math.hypot(dx, dy) || 1
  const ux = dx / len, uy = dy / len
  const nx = uy, ny = -ux
  const mx = (A.x + B.x) / 2 + nx * bend, my = (A.y + B.y) / 2 + ny * bend
  const ang = Math.atan2(bend, len / 2)
  const rot = (vx, vy, t) => [vx * Math.cos(t) - vy * Math.sin(t), vx * Math.sin(t) + vy * Math.cos(t)]
  const [sx, sy] = rot(ux, uy, -ang)
  const [ex, ey] = rot(-ux, -uy, ang)
  const rs = boxExit(i, sx, sy), re = boxExit(j, ex, ey) + 2
  const s = { x: A.x + sx * rs, y: A.y + sy * rs }
  const e = { x: B.x + ex * re, y: B.y + ey * re }
  const cx = mx * 2 - (s.x + e.x) / 2, cy = my * 2 - (s.y + e.y) / 2
  return `M${s.x},${s.y} Q${cx},${cy} ${e.x},${e.y}`
}

function loopPath(i) {
  const A = E.value.nodes[i]
  const hw = nodeW(i) / 2
  const sx = A.x + hw, sy = A.y - 6
  const ex = A.x + hw, ey = A.y + 6
  return `M${sx},${sy} C${sx + 30},${sy - 22} ${ex + 30},${ey + 22} ${ex + 2},${ey}`
}

const selected = (i, j) => selA.value !== null && selB.value !== null && selA.value === i && selB.value === j

const arrows = computed(() => {
  const out = []
  const n = N.value
  for (let i = 0; i < n; i++)
    for (let j = 0; j < n; j++) {
      if (i === j || !le(i, j)) continue
      const gen = isGen(i, j)
      const sel = selected(i, j) || selected(j, i)
      if (!gen && !showAll.value && !sel) continue
      out.push({ key: `${i}-${j}`, i, j, d: arrowPath(i, j), gen, sel: selected(i, j), rev: selected(j, i) })
    }
  return out
})

const loopsShown = computed(() => {
  if (showAll.value) return E.value.nodes.map((_, i) => i)
  if (selA.value !== null && selB.value !== null && selA.value === selB.value) return [selA.value]
  return []
})

const info = computed(() => {
  const a = selA.value, b = selB.value
  if (a === null) return null
  if (b === null) return { only: a }
  const ab = le(a, b), ba = le(b, a)
  const via = []
  if (ab && a !== b)
    for (let k = 0; k < N.value; k++) if (k !== a && k !== b && le(a, k) && le(k, b)) via.push(k)
  return { a, b, ab, ba, via, cycle: a !== b && ab && ba }
})

const W = 390
const H = 370
</script>

<template>
  <div class="ctfp-widget ch13p">
    <div class="ctfp-widget-title">预序就是瘦范畴：任意两点之间至多一条箭头</div>
    <div class="row">
      <button v-for="(ex, i) in examples" :key="ex.key" class="ctfp-btn" :class="{ on: i === ei }" @click="choose(i)">{{ ex.name }}</button>
    </div>
    <div class="row">
      <button class="ctfp-btn" :class="{ on: !showAll }" @click="showAll = false">只画生成箭头</button>
      <button class="ctfp-btn" :class="{ on: showAll }" @click="showAll = true">画出全部箭头（含恒等与复合）</button>
    </div>
    <p class="hint">{{ E.desc }}。依次点两个对象 a、b，查看 hom-集 𝓒(a, b) 与 𝓒(b, a)；同一个对象点两次，查看 𝓒(a, a)。虚线箭头是由复合得到的。</p>

    <div class="panes">
      <svg :viewBox="`0 0 ${W} ${H}`" class="canvas" role="img" aria-label="有限序的箭头图">
        <defs>
          <marker id="ch13p-ah" viewBox="0 0 10 10" refX="8.5" refY="5" markerUnits="userSpaceOnUse" markerWidth="9" markerHeight="9" orient="auto-start-reverse">
            <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
          </marker>
        </defs>
        <path
          v-for="i in loopsShown" :key="'l' + i" :d="loopPath(i)" fill="none"
          stroke="var(--vp-c-text-3)" stroke-width="1.3" marker-end="url(#ch13p-ah)"
        />
        <path
          v-for="a in arrows" :key="a.key" :d="a.d" fill="none"
          :stroke="a.sel ? 'var(--vp-c-success-1, #18794e)' : a.rev ? 'var(--vp-c-warning-1)' : a.gen ? 'var(--vp-c-text-2)' : 'var(--vp-c-text-3)'"
          :stroke-width="a.sel || a.rev ? 3 : a.gen ? 1.7 : 1.1"
          :stroke-dasharray="a.gen ? null : '5 4'"
          marker-end="url(#ch13p-ah)"
        />
        <g v-for="(nd, i) in E.nodes" :key="String(nd.v)" class="node" @click="clickNode(i)">
          <rect
            :x="nd.x - nodeW(i) / 2" :y="nd.y - NODE_H / 2" :width="nodeW(i)" :height="NODE_H" rx="8"
            :class="{ a: selA === i, b: selB === i }"
          />
          <text :x="nd.x" :y="nd.y + 1" text-anchor="middle" dominant-baseline="middle">{{ L(i) }}</text>
        </g>
      </svg>

      <div class="side">
        <div class="box">
          <div class="kind">{{ props4.kind }}</div>
          <ul class="checks">
            <li><span class="ok">✓</span> 自反：每个对象都有恒等箭头</li>
            <li><span class="ok">✓</span> 传递：a → b → c 就有 a → c（复合）</li>
            <li v-if="!props4.anti"><span class="ok">✓</span> 反对称：没有环</li>
            <li v-else><span class="no">✗</span> 反对称：{{ L(props4.anti[0]) }} ⇄ {{ L(props4.anti[1]) }} 构成环，但它们不相等</li>
            <li v-if="!props4.total"><span class="ok">✓</span> 完全：任意两个对象都可比</li>
            <li v-else><span class="no">✗</span> 完全：{{ L(props4.total[0]) }} 与 {{ L(props4.total[1]) }} 之间没有箭头</li>
          </ul>
          <div class="small">{{ N }} 个对象；生成箭头 {{ counts.gen }} 条；补全后共 {{ counts.all }} 条态射（含 {{ N }} 条恒等）。</div>
        </div>

        <div class="box sel">
          <template v-if="!info">
            <div class="small">点一个对象开始。</div>
          </template>
          <template v-else-if="info.only !== undefined">
            <div>已选 a = <b class="ca">{{ L(info.only) }}</b>，再选 b</div>
          </template>
          <template v-else-if="info.a === info.b">
            <div>𝓒({{ L(info.a) }}, {{ L(info.a) }}) = { id }</div>
            <div class="small">在预序里，从一个对象到它自己只有恒等箭头。</div>
          </template>
          <template v-else>
            <div>𝓒(<b class="ca">{{ L(info.a) }}</b>, <b class="cb">{{ L(info.b) }}</b>) = <b :class="info.ab ? 'cs' : ''">{{ info.ab ? '{ ≤ }，恰好一条' : '∅，没有箭头' }}</b></div>
            <div>𝓒(<b class="cb">{{ L(info.b) }}</b>, <b class="ca">{{ L(info.a) }}</b>) = <b :class="info.ba ? 'cr' : ''">{{ info.ba ? '{ ≤ }，恰好一条' : '∅，没有箭头' }}</b></div>
            <div v-if="info.via.length" class="small">
              经过 {{ info.via.map(L).join('、') }} 的路径复合出来，都是同一条箭头 {{ L(info.a) }} → {{ L(info.b) }}：在瘦范畴里任何图都交换。
            </div>
            <div v-if="info.cycle" class="small warn">两个方向都有箭头：这是一个环。偏序不允许这样（反对称会逼出 a = b）。</div>
            <div v-if="!info.ab && !info.ba" class="small">两个方向都没有箭头：这两个对象不可比，所以这不是全序。</div>
          </template>
        </div>
      </div>
    </div>
  </div>
</template>

<style scoped>
.row { display: flex; flex-wrap: wrap; gap: 6px; margin-bottom: 8px; }
.hint { font-size: 13px; color: var(--vp-c-text-2); margin: 4px 0 10px; line-height: 1.6; }
.panes { display: flex; flex-wrap: wrap; gap: 14px; align-items: flex-start; }
.canvas { width: 390px; max-width: 100%; flex: 0 0 auto; }
.side { flex: 1 1 240px; min-width: 0; display: flex; flex-direction: column; gap: 8px; }
.box { border: 1px solid var(--vp-c-divider); border-radius: 8px; padding: 8px 10px; background: var(--vp-c-bg); font-size: 14px; line-height: 1.7; }
.sel { min-height: 90px; }
.kind { font-weight: 600; color: var(--vp-c-brand-1); margin-bottom: 4px; }
.checks { list-style: none; padding: 0; margin: 0 0 6px; font-size: 13px; }
.checks li { margin: 0; }
.ok { color: var(--vp-c-success-1, #18794e); font-weight: 700; margin-right: 4px; }
.no { color: var(--vp-c-danger-1); font-weight: 700; margin-right: 4px; }
.small { font-size: 12px; color: var(--vp-c-text-2); line-height: 1.6; }
.warn { color: var(--vp-c-warning-1); }
.ca { color: var(--vp-c-brand-1); }
.cb { color: var(--vp-c-purple-1, #8e5cd9); }
.cs { color: var(--vp-c-success-1, #18794e); }
.cr { color: var(--vp-c-warning-1); }
.node { cursor: pointer; }
.node rect { fill: var(--vp-c-bg); stroke: var(--vp-c-text-2); stroke-width: 1.4; }
.node rect.a { stroke: var(--vp-c-brand-1); stroke-width: 3; fill: var(--vp-c-brand-soft); }
.node rect.b { stroke: var(--vp-c-purple-1, #8e5cd9); stroke-width: 3; }
.node text { font-family: var(--vp-font-family-mono); font-size: 13px; fill: var(--vp-c-text-1); pointer-events: none; }
</style>
