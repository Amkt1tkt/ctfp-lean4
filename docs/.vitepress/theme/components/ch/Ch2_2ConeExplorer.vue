<script setup>
import { ref, computed, watch, onBeforeUnmount } from 'vue'

const PILL_H = 22
const ROW = 28
const HEAD = 34

const PB = {
  A: ['小明', '小红', '小刚'],
  B: ['烤鸭', '小笼包', '火锅'],
  C: ['北京', '上海', '成都'],
  f: { 小明: '北京', 小红: '上海', 小刚: '北京' },
  g: { 烤鸭: '北京', 小笼包: '上海', 火锅: '成都' },
}
const pbLimit = []
for (const a of PB.A) for (const b of PB.B) if (PB.f[a] === PB.g[b]) pbLimit.push({ id: `(${a}, ${b})`, a, b })

const EQ = {
  A: [0, 1, 2, 3, 4, 5, 6, 7].map(String),
  B: ['0', '1', '2'],
  f: (x) => String(Number(x) % 3),
  g: (x) => String(Number(x) % 2),
}
const eqLimit = EQ.A.filter((x) => EQ.f(x) === EQ.g(x)).map((a) => ({ id: a, a }))

const MODES = {
  pullback: {
    name: '拉回（人 ⋈ 餐馆）',
    intro: '余跨：a = 人 —f（所在城市）→ c = 城市 ←g（所在城市）— b = 餐馆。拉回 P 是所有“同城”的 (人, 餐馆) 对，π₁、π₂ 是两个投影。一个锥是顶点 d 加上两条腿 p : d → a、q : d → b，并且要求 f ∘ p = g ∘ q。',
    limit: pbLimit,
    boxes: {
      D: { x: 12, y: 12, w: 150 },
      L: { x: 240, y: 112, w: 170, label: 'P（拉回）' },
      B: { x: 530, y: 112, w: 150, label: 'b = 餐馆' },
      A: { x: 240, y: 330, w: 170, label: 'a = 人' },
      C: { x: 530, y: 330, w: 150, label: 'c = 城市' },
    },
    elems: { A: PB.A, B: PB.B, C: PB.C },
    candidates: [
      {
        name: '订单表', apex: 'd = 订单',
        desc: '三张订单，每张订单记录了下单人 p 和餐馆 q。注意订单 1 和订单 3 内容一样——h 不必是单射。',
        elems: ['订单1', '订单2', '订单3'],
        p: { 订单1: '小明', 订单2: '小红', 订单3: '小明' },
        q: { 订单1: '烤鸭', 订单2: '小笼包', 订单3: '烤鸭' },
      },
      {
        name: '单点 {★}', apex: 'd = {★}',
        desc: '单点集上的锥，就是拉回中的一个元素：选一个人和一家同城餐馆。',
        elems: ['★'], p: { '★': '小刚' }, q: { '★': '烤鸭' },
      },
      {
        name: '给每人推荐一家', apex: 'd = 人',
        desc: '顶点就是 a 本身：p = id，q 给每个人推荐一家同城餐馆。',
        elems: ['小明 ', '小红 ', '小刚 '],
        p: { '小明 ': '小明', '小红 ': '小红', '小刚 ': '小刚' },
        q: { '小明 ': '烤鸭', '小红 ': '小笼包', '小刚 ': '烤鸭' },
      },
      {
        name: '拉回自己', apex: 'd = P',
        desc: '极限锥自己也是一个候选者，它经由恒等态射分解到自己。',
        elems: pbLimit.map((l) => l.id + ' '),
        p: Object.fromEntries(pbLimit.map((l) => [l.id + ' ', l.a])),
        q: Object.fromEntries(pbLimit.map((l) => [l.id + ' ', l.b])),
      },
      {
        name: '坏候选 {☆}', apex: 'd = {☆}', bad: true,
        desc: '小明在北京，火锅店在成都：f(p ☆) ≠ g(q ☆)，方块不交换，所以这根本不是锥。',
        elems: ['☆'], p: { '☆': '小明' }, q: { '☆': '火锅' },
      },
      {
        name: '坏候选 a × b', apex: 'd = a × b', bad: true,
        desc: '积 a × b 配上两个投影，并不是这个余跨上的锥：大多数 (人, 餐馆) 对不同城。积是“2”形状的极限，不是余跨形状的。',
        elems: PB.A.flatMap((a) => PB.B.map((b) => `${a}·${b}`)),
        p: Object.fromEntries(PB.A.flatMap((a) => PB.B.map((b) => [`${a}·${b}`, a]))),
        q: Object.fromEntries(PB.A.flatMap((a) => PB.B.map((b) => [`${a}·${b}`, b]))),
      },
    ],
  },
  equalizer: {
    name: '等化子（x mod 3 = x mod 2）',
    intro: '两条平行箭头 f, g : a → b，其中 a = {0,…,7}，b = {0,1,2}，f x = x mod 3，g x = x mod 2。等化子 E = {x | f x = g x}，ι 是包含映射。一个锥是顶点 d 加上 p : d → a，要求 f ∘ p = g ∘ p。',
    limit: eqLimit,
    boxes: {
      D: { x: 12, y: 12, w: 130 },
      L: { x: 12, y: 250, w: 130, label: 'E（等化子）' },
      A: { x: 300, y: 112, w: 120, label: 'a' },
      B: { x: 560, y: 170, w: 120, label: 'b' },
    },
    elems: { A: EQ.A, B: EQ.B },
    candidates: [
      {
        name: '单点 {★}', apex: 'd = {★}',
        desc: '选出方程 x mod 3 = x mod 2 的一个解：6。',
        elems: ['★'], p: { '★': '6' },
      },
      {
        name: 'Bool', apex: 'd = Bool',
        desc: '两个解：假 ↦ 0，真 ↦ 7。',
        elems: ['假', '真'], p: { 假: '0', 真: '7' },
      },
      {
        name: '{u, v, w}', apex: 'd = {u,v,w}',
        desc: 'u 和 v 都映到 1：h 也会把它们映到同一个点。',
        elems: ['u', 'v', 'w'], p: { u: '1', v: '1', w: '6' },
      },
      {
        name: '等化子自己', apex: 'd = E',
        desc: '极限锥自己，经由恒等态射分解。',
        elems: eqLimit.map((l) => l.id + ' '),
        p: Object.fromEntries(eqLimit.map((l) => [l.id + ' ', l.a])),
      },
      {
        name: '坏候选 {☆}', apex: 'd = {☆}', bad: true,
        desc: '2 mod 3 = 2，2 mod 2 = 0：f ∘ p ≠ g ∘ p，不是锥。',
        elems: ['☆'], p: { '☆': '2' },
      },
      {
        name: '坏候选 a 自己', apex: 'd = a', bad: true,
        desc: 'p = id：并不是 a 的每个元素都满足方程，所以不是锥。',
        elems: EQ.A.map((x) => x + ' '), p: Object.fromEntries(EQ.A.map((x) => [x + ' ', x])),
      },
    ],
  },
}

const mode = ref('pullback')
const candIdx = ref(0)
const focus = ref(null)
const hChoice = ref({})
const message = ref('')
let timers = []

const M = computed(() => MODES[mode.value])
const cand = computed(() => M.value.candidates[candIdx.value])
const isPB = computed(() => mode.value === 'pullback')

function clearTimers() {
  timers.forEach(clearTimeout)
  timers = []
}
onBeforeUnmount(clearTimers)

function reset() {
  clearTimers()
  focus.value = null
  hChoice.value = {}
  message.value = ''
}
watch([mode, candIdx], reset)
function setMode(m) {
  mode.value = m
  candIdx.value = 0
}

const fOf = (a) => (isPB.value ? PB.f[a] : EQ.f(a))
const gOfLeg = (x) => (isPB.value ? PB.g[cand.value.q[x]] : EQ.g(cand.value.p[x]))

function coneOk(x) {
  return fOf(cand.value.p[x]) === gOfLeg(x)
}
const isCone = computed(() => cand.value.elems.every(coneOk))

function limById(id) {
  return M.value.limit.find((l) => l.id === id)
}
function triOk(x, id) {
  const l = limById(id)
  if (!l) return false
  if (isPB.value) return l.a === cand.value.p[x] && l.b === cand.value.q[x]
  return l.a === cand.value.p[x]
}
function correctH(x) {
  const l = M.value.limit.find((l) => triOk(x, l.id))
  return l ? l.id : null
}
const allChosen = computed(() => cand.value.elems.every((x) => hChoice.value[x]))
const allOk = computed(() => cand.value.elems.every((x) => triOk(x, hChoice.value[x])))

function choose(x, id) {
  hChoice.value = { ...hChoice.value, [x]: id }
  focus.value = x
  message.value = ''
}

function autoSolve() {
  clearTimers()
  if (!isCone.value) {
    message.value = '这个候选者不是锥，没有任何 h 能让三角形交换——它根本没有资格参加排名。'
    return
  }
  const h = {}
  for (const x of cand.value.elems) h[x] = correctH(x)
  hChoice.value = h
  message.value = ''
}

function play() {
  clearTimers()
  hChoice.value = {}
  message.value = ''
  const xs = cand.value.elems
  xs.forEach((x, i) => {
    timers.push(setTimeout(() => {
      focus.value = x
      const c = correctH(x)
      if (c) hChoice.value = { ...hChoice.value, [x]: c }
    }, i * 1300))
  })
  timers.push(setTimeout(() => {
    if (!isCone.value) message.value = '有元素让方块不交换（红色），所以这不是锥，h 无从谈起。'
  }, xs.length * 1300))
}

// ---------- 几何 ----------
const boxes = computed(() => {
  const b = M.value.boxes
  const elems = {
    D: cand.value.elems,
    L: M.value.limit.map((l) => l.id),
    ...M.value.elems,
  }
  const out = {}
  for (const k of Object.keys(b)) {
    const n = elems[k].length
    out[k] = { ...b[k], key: k, items: elems[k], h: HEAD + n * ROW + 4, label: k === 'D' ? cand.value.apex : b[k].label }
  }
  return out
})

function pill(k, id) {
  const bx = boxes.value[k]
  const i = bx.items.indexOf(id)
  if (i < 0) return null
  return { x: bx.x + bx.w / 2, y: bx.y + HEAD + i * ROW + PILL_H / 2, w: bx.w - 16, h: PILL_H }
}

function clip(c, dx, dy, w, h, pad = 3) {
  const tx = dx === 0 ? Infinity : (w / 2 + pad) / Math.abs(dx)
  const ty = dy === 0 ? Infinity : (h / 2 + pad) / Math.abs(dy)
  const t = Math.min(tx, ty)
  return { x: c.x + dx * t, y: c.y + dy * t }
}

function curve(P, Q, bend = 0) {
  const len = Math.hypot(Q.x - P.x, Q.y - P.y) || 1
  const ux = (Q.x - P.x) / len, uy = (Q.y - P.y) / len
  const s = clip(P, ux, uy, P.w, P.h)
  const e = clip(Q, -ux, -uy, Q.w, Q.h, 5)
  const mx = (s.x + e.x) / 2 + uy * bend, my = (s.y + e.y) / 2 - ux * bend
  return { d: `M${s.x},${s.y} Q${mx},${my} ${e.x},${e.y}`, lx: mx, ly: my }
}

function boxCenter(k) {
  const b = boxes.value[k]
  return { x: b.x + b.w / 2, y: b.y + b.h / 2, w: b.w, h: b.h }
}

const objArrows = computed(() => {
  const list = isPB.value
    ? [
        ['D', 'L', 'h', -10, true], ['D', 'A', 'p', 60], ['D', 'B', 'q', -50],
        ['L', 'B', 'π₂', 0], ['L', 'A', 'π₁', 0], ['B', 'C', 'g', 0], ['A', 'C', 'f', 0],
      ]
    : [
        ['D', 'L', 'h', 0, true], ['D', 'A', 'p', -10], ['L', 'A', 'ι', 10],
        ['A', 'B', 'f', -40], ['A', 'B', 'g', 40],
      ]
  return list.map(([from, to, label, bend, dashed]) => ({
    key: from + to + label, label, dashed, ...curve(boxCenter(from), boxCenter(to), bend),
  }))
})

const COL = {
  p: 'var(--vp-c-warning-1)',
  q: 'var(--vp-c-purple-1, #8e5cd9)',
  h: 'var(--vp-c-brand-1)',
  pi: 'var(--vp-c-success-1, #18794e)',
  base: 'var(--vp-c-text-3)',
  bad: 'var(--vp-c-danger-1)',
}

const elemArrows = computed(() => {
  const x = focus.value
  if (!x || !cand.value.elems.includes(x)) return []
  const c = cand.value
  const out = []
  const add = (k1, id1, k2, id2, color, label, bend = 0, dashed = false) => {
    const P = pill(k1, id1), Q = pill(k2, id2)
    if (!P || !Q) return
    out.push({ key: out.length, color, label, dashed, ...curve(P, Q, bend) })
  }
  const pa = c.p[x]
  const ok = coneOk(x)
  if (isPB.value) {
    const qb = c.q[x]
    add('D', x, 'A', pa, COL.p, 'p', 40)
    add('D', x, 'B', qb, COL.q, 'q', -30)
    add('A', pa, 'C', PB.f[pa], ok ? COL.base : COL.bad, 'f', 0)
    add('B', qb, 'C', PB.g[qb], ok ? COL.base : COL.bad, 'g', 0)
    const hx = hChoice.value[x]
    if (hx) {
      const l = limById(hx)
      add('D', x, 'L', hx, COL.h, 'h', -8, true)
      add('L', hx, 'A', l.a, l.a === pa ? COL.pi : COL.bad, 'π₁', -12)
      add('L', hx, 'B', l.b, l.b === qb ? COL.pi : COL.bad, 'π₂', 12)
    }
  } else {
    add('D', x, 'A', pa, COL.p, 'p', -10)
    add('A', pa, 'B', EQ.f(pa), ok ? COL.base : COL.bad, 'f', -25)
    add('A', pa, 'B', EQ.g(pa), ok ? COL.base : COL.bad, 'g', 25)
    const hx = hChoice.value[x]
    if (hx) {
      const l = limById(hx)
      add('D', x, 'L', hx, COL.h, 'h', 20, true)
      add('L', hx, 'A', l.a, l.a === pa ? COL.pi : COL.bad, 'ι', 10)
    }
  }
  return out
})

function pillState(k, id) {
  const x = focus.value
  if (!x) return ''
  const c = cand.value
  if (k === 'D') return id === x ? 'focus' : ''
  if (k === 'A' && id === c.p[x]) return 'hit'
  if (k === 'B' && isPB.value && id === c.q[x]) return 'hit'
  if (k === 'L' && id === hChoice.value[x]) return 'hit'
  if (k === 'C' && (id === PB.f[c.p[x]] || id === PB.g[c.q[x]])) return coneOk(x) ? 'hit' : 'badhit'
  if (k === 'B' && !isPB.value && (id === EQ.f(c.p[x]) || id === EQ.g(c.p[x]))) return coneOk(x) ? 'hit' : 'badhit'
  return ''
}

const W = computed(() => (isPB.value ? 700 : 700))
const H = computed(() => {
  let m = 0
  for (const b of Object.values(boxes.value)) m = Math.max(m, b.y + b.h)
  return m + 14
})

const summary = computed(() => {
  if (!isCone.value) {
    const bad = cand.value.elems.filter((x) => !coneOk(x))
    return { cls: 'bad', text: `不是锥：在 ${bad.slice(0, 3).join('、')}${bad.length > 3 ? ' 等' : ''} 处方块不交换（f ∘ p ≠ g ∘ ${isPB.value ? 'q' : 'p'}）。` }
  }
  if (allChosen.value && allOk.value)
    return { cls: 'good', text: isPB.value ? '分解成功：p = π₁ ∘ h 且 q = π₂ ∘ h。而且你别无选择——h(x) 只能是 (p x, q x)。' : '分解成功：p = ι ∘ h。h(x) 只能是 p x 本身（作为 E 的元素）。' }
  return { cls: '', text: '这是一个锥。试着给每个元素选 h(x)，让所有三角形交换；或者点“自动求出 h”。' }
})
</script>

<template>
  <div class="ctfp-widget cone-explorer">
    <div class="ctfp-widget-title">交互：锥与极限——候选者如何唯一地经由极限分解</div>
    <div class="row tabs">
      <button v-for="(m, k) in MODES" :key="k" class="ctfp-btn" :class="{ on: mode === k }" @click="setMode(k)">{{ m.name }}</button>
    </div>
    <p class="intro">{{ M.intro }}</p>
    <div class="row">
      <span class="lbl">候选锥：</span>
      <button v-for="(c, i) in M.candidates" :key="c.name" class="ctfp-btn" :class="{ on: candIdx === i }" @click="candIdx = i">{{ c.name }}</button>
    </div>
    <p class="desc">{{ cand.desc }}</p>

    <svg :viewBox="`0 0 ${W} ${H}`" class="ce-svg" role="img">
      <defs>
        <marker id="ce-ah" viewBox="0 0 10 10" refX="8.5" refY="5" markerWidth="8" markerHeight="8" orient="auto-start-reverse">
          <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
        </marker>
      </defs>
      <g v-for="a in objArrows" :key="a.key" class="obj-arrow" :class="{ faded: elemArrows.length }">
        <path :d="a.d" fill="none" :stroke-dasharray="a.dashed ? '6 5' : null" marker-end="url(#ce-ah)" />
        <text v-if="!elemArrows.length" :x="a.lx" :y="a.ly - 4" text-anchor="middle">{{ a.label }}</text>
      </g>
      <g v-for="b in boxes" :key="b.key">
        <rect :x="b.x" :y="b.y" :width="b.w" :height="b.h" rx="10" :class="['box', { apex: b.key === 'D', lim: b.key === 'L' }]" />
        <text :x="b.x + b.w / 2" :y="b.y + 21" text-anchor="middle" class="box-label">{{ b.label }}</text>
        <g v-for="(it, i) in b.items" :key="it" class="pill" :class="pillState(b.key, it)" @click="b.key === 'D' ? (focus = it) : null" :style="{ cursor: b.key === 'D' ? 'pointer' : 'default' }">
          <rect :x="b.x + 8" :y="b.y + HEAD + i * ROW" :width="b.w - 16" :height="PILL_H" rx="11" />
          <text :x="b.x + b.w / 2" :y="b.y + HEAD + i * ROW + 15.5" text-anchor="middle">{{ it.trim() }}</text>
        </g>
      </g>
      <g v-for="a in elemArrows" :key="'e' + a.key">
        <path :d="a.d" fill="none" :stroke="a.color" stroke-width="2.4" :stroke-dasharray="a.dashed ? '6 4' : null" marker-end="url(#ce-ah)" />
        <text :x="a.lx" :y="a.ly - 5" text-anchor="middle" class="elem-label" :fill="a.color">{{ a.label }}</text>
      </g>
    </svg>

    <div class="row">
      <button class="ctfp-btn" @click="play">▶ 逐个演示分解</button>
      <button class="ctfp-btn" @click="autoSolve">自动求出 h</button>
      <button class="ctfp-btn" @click="reset">清空</button>
    </div>

    <div class="table-wrap">
      <table class="ce-table">
        <thead>
          <tr>
            <th>x ∈ d</th>
            <th>p(x)</th>
            <th v-if="isPB">q(x)</th>
            <th>{{ isPB ? 'f(p x) / g(q x)' : 'f(p x) / g(p x)' }}</th>
            <th>选 h(x)</th>
            <th>三角形</th>
          </tr>
        </thead>
        <tbody>
          <tr v-for="x in cand.elems" :key="x" :class="{ focus: focus === x }" @click="focus = x">
            <td>{{ x.trim() }}</td>
            <td>{{ cand.p[x] }}</td>
            <td v-if="isPB">{{ cand.q[x] }}</td>
            <td :class="coneOk(x) ? 'ok' : 'no'">
              {{ isPB ? PB.f[cand.p[x]] : EQ.f(cand.p[x]) }} {{ coneOk(x) ? '=' : '≠' }} {{ isPB ? PB.g[cand.q[x]] : EQ.g(cand.p[x]) }}
            </td>
            <td>
              <select :value="hChoice[x] || ''" @change="choose(x, $event.target.value)" @click.stop>
                <option value="" disabled>?</option>
                <option v-for="l in M.limit" :key="l.id" :value="l.id">{{ l.id }}</option>
              </select>
            </td>
            <td :class="hChoice[x] ? (triOk(x, hChoice[x]) ? 'ok' : 'no') : ''">
              {{ hChoice[x] ? (triOk(x, hChoice[x]) ? '✓ 交换' : '✗ 不交换') : '' }}
            </td>
          </tr>
        </tbody>
      </table>
    </div>
    <p class="summary" :class="summary.cls">{{ message || summary.text }}</p>
    <p class="hint">提示：点击顶点 d 中的元素（或表格中的一行）查看它沿各条箭头走到哪里。绿色箭头表示三角形交换，红色表示不交换。每个元素最多只有一个 h(x) 能让三角形交换——这就是“唯一分解”。</p>
  </div>
</template>

<style scoped>
.cone-explorer { max-width: 100%; }
.row { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin: 8px 0; }
.lbl { font-size: 13px; color: var(--vp-c-text-2); }
.intro, .desc, .hint { font-size: 13px; line-height: 1.6; color: var(--vp-c-text-2); margin: 6px 0; }
.desc { color: var(--vp-c-text-1); }
.ce-svg { width: 100%; height: auto; display: block; margin: 6px 0; }
.box { fill: var(--vp-c-bg); stroke: var(--vp-c-divider); stroke-width: 1.4; }
.box.apex { stroke: var(--vp-c-warning-1); }
.box.lim { stroke: var(--vp-c-brand-1); stroke-width: 2; }
.box-label { font-size: 13px; font-weight: 600; fill: var(--vp-c-text-1); }
.obj-arrow path { stroke: var(--vp-c-divider); stroke-width: 1.4; }
.obj-arrow text { font-size: 13px; font-style: italic; fill: var(--vp-c-text-3); }
.obj-arrow.faded { opacity: 0.4; }
.pill rect { fill: var(--vp-c-bg-soft); stroke: var(--vp-c-divider); }
.pill text { font-size: 12px; fill: var(--vp-c-text-1); }
.pill.focus rect { fill: var(--vp-c-warning-soft, rgba(234, 179, 8, 0.2)); stroke: var(--vp-c-warning-1); stroke-width: 2; }
.pill.hit rect { fill: var(--vp-c-brand-soft); stroke: var(--vp-c-brand-1); stroke-width: 2; }
.pill.badhit rect { fill: var(--vp-c-danger-soft); stroke: var(--vp-c-danger-1); stroke-width: 2; }
.elem-label { font-size: 13px; font-weight: 600; }
.table-wrap { overflow-x: auto; max-width: 100%; }
.ce-table { font-size: 13px; border-collapse: collapse; margin: 6px 0; display: table; width: 100%; }
.ce-table th, .ce-table td { padding: 4px 8px; border: 1px solid var(--vp-c-divider); text-align: center; white-space: nowrap; }
.ce-table tr { cursor: pointer; }
.ce-table tr.focus td { background: var(--vp-c-bg-soft); }
.ce-table td.ok { color: var(--vp-c-success-1, #18794e); }
.ce-table td.no { color: var(--vp-c-danger-1); font-weight: 600; }
.ce-table select { font-size: 13px; background: var(--vp-c-bg); color: var(--vp-c-text-1); border: 1px solid var(--vp-c-divider); border-radius: 6px; padding: 1px 4px; }
.summary { font-size: 14px; padding: 8px 12px; border-radius: 8px; background: var(--vp-c-bg); border: 1px solid var(--vp-c-divider); }
.summary.good { border-color: var(--vp-c-success-1, #18794e); color: var(--vp-c-success-1, #18794e); }
.summary.bad { border-color: var(--vp-c-danger-1); color: var(--vp-c-danger-1); }
</style>
