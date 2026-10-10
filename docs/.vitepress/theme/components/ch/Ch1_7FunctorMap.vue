<script setup>
import { computed, ref, onBeforeUnmount } from 'vue'

const uid = Math.random().toString(36).slice(2, 8)
const R = 15

// 源范畴 C：a → b → c，加上复合 g∘f 和三个恒等箭头
const C = {
  objects: [
    { id: 'a', label: 'a', x: 60, y: 215, loop: 'down' },
    { id: 'b', label: 'b', x: 160, y: 90, loop: 'up' },
    { id: 'c', label: 'c', x: 260, y: 215, loop: 'down' },
  ],
  arrows: [
    { id: 'f', label: 'f', from: 'a', to: 'b', bend: 0 },
    { id: 'g', label: 'g', from: 'b', to: 'c', bend: 0 },
    { id: 'h', label: 'g∘f', from: 'a', to: 'c', bend: 0, side: -1 },
  ],
  comp: { 'g,f': 'h' },
}

const FUNCTORS = [
  {
    key: 'embed',
    name: '嵌入',
    desc: '三个对象映到三个不同的对象，D 比 C 大（多了对象 w 和箭头 k），像是把 C 原样“放进” D 里。',
    D: {
      objects: [
        { id: 'x', label: 'x', x: 400, y: 215, loop: 'down' },
        { id: 'y', label: 'y', x: 500, y: 90, loop: 'up' },
        { id: 'z', label: 'z', x: 600, y: 215, loop: 'down' },
        { id: 'w', label: 'w', x: 600, y: 90, loop: 'up' },
      ],
      arrows: [
        { id: 'u', label: 'u', from: 'x', to: 'y' },
        { id: 'v', label: 'v', from: 'y', to: 'z' },
        { id: 'vu', label: 'v∘u', from: 'x', to: 'z', side: -1 },
        { id: 'k', label: 'k', from: 'w', to: 'z' },
      ],
      comp: { 'v,u': 'vu' },
    },
    obj: { a: 'x', b: 'y', c: 'z' },
    mor: { f: 'u', g: 'v', h: 'vu' },
  },
  {
    key: 'collapse',
    name: '坍缩',
    desc: 'a 和 b 被压成同一个对象 p，箭头 f 被压成恒等箭头 id_p。东西可以“粘”在一起，但没有任何连接被扯断。',
    D: {
      objects: [
        { id: 'p', label: 'p', x: 430, y: 160, loop: 'up' },
        { id: 'q', label: 'q', x: 580, y: 160, loop: 'up' },
      ],
      arrows: [{ id: 't', label: 't', from: 'p', to: 'q' }],
      comp: {},
    },
    obj: { a: 'p', b: 'p', c: 'q' },
    mor: { f: 'id_p', g: 't', h: 't' },
  },
  {
    key: 'const',
    name: '常函子 Δ',
    desc: '黑洞：所有对象都映到同一个对象 c₀，所有箭头都映成它的恒等箭头。两条定律都平凡地成立。',
    D: {
      objects: [{ id: 'c0', label: 'c₀', x: 505, y: 160, loop: 'up' }],
      arrows: [],
      comp: {},
    },
    obj: { a: 'c0', b: 'c0', c: 'c0' },
    mor: { f: 'id_c0', g: 'id_c0', h: 'id_c0' },
  },
  {
    key: 'tear',
    name: '撕裂（不是函子）',
    desc: 'D 中从 x 到 z 有两个不同的箭头：v∘u 和 k。这个映射把 g∘f 送到了 k，而不是 F g ∘ F f = v∘u——复合被“撕开”了。',
    D: {
      objects: [
        { id: 'x', label: 'x', x: 400, y: 190, loop: 'up' },
        { id: 'y', label: 'y', x: 500, y: 80, loop: 'up' },
        { id: 'z', label: 'z', x: 600, y: 190, loop: 'up' },
      ],
      arrows: [
        { id: 'u', label: 'u', from: 'x', to: 'y' },
        { id: 'v', label: 'v', from: 'y', to: 'z' },
        { id: 'vu', label: 'v∘u', from: 'x', to: 'z', side: 1 },
        { id: 'k', label: 'k', from: 'x', to: 'z', bend: -50, side: -1 },
      ],
      comp: { 'v,u': 'vu' },
    },
    obj: { a: 'x', b: 'y', c: 'z' },
    mor: { f: 'u', g: 'v', h: 'k' },
  },
  {
    key: 'noid',
    name: '丢了恒等（不是函子）',
    desc: 'D 只有一个对象 x，箭头是 id 和 e（满足 e∘e = e）。把一切箭头——包括恒等箭头——都送到 e：复合碰巧保持了，恒等却没有。',
    D: {
      objects: [{ id: 'x', label: 'x', x: 505, y: 160, loop: 'up' }],
      arrows: [{ id: 'e', label: 'e', from: 'x', to: 'x', loop: 'down' }],
      comp: { 'e,e': 'e' },
    },
    obj: { a: 'x', b: 'x', c: 'x' },
    mor: { f: 'e', g: 'e', h: 'e', id_a: 'e', id_b: 'e', id_c: 'e' },
  },
]

const fi = ref(0)
const F = computed(() => FUNCTORS[fi.value])

const sel = ref(null) // { side: 'C' | 'D', id }
const demo = ref(null) // { kind: 'comp' | 'id', step }
let timers = []
const clearTimers = () => {
  timers.forEach(clearTimeout)
  timers = []
}
onBeforeUnmount(clearTimers)

function pickFunctor(i) {
  clearTimers()
  fi.value = i
  sel.value = null
  demo.value = null
}

// 把恒等箭头补进范畴
function withIds(cat) {
  const ids = cat.objects.map((o) => ({
    id: `id_${o.id}`, label: 'id', from: o.id, to: o.id, loop: o.loop || 'up', isId: true,
  }))
  return { ...cat, arrows: [...ids, ...cat.arrows] }
}
const catC = withIds(C)
const catD = computed(() => withIds(F.value.D))

const objF = (o) => F.value.obj[o]
const morF = (m) => {
  if (F.value.mor[m]) return F.value.mor[m]
  if (m.startsWith('id_')) return `id_${objF(m.slice(3))}`
  return null
}
const isIdArrow = (m) => m.startsWith('id_')
function compose(cat, g, f) {
  if (isIdArrow(f)) return g
  if (isIdArrow(g)) return f
  return cat.comp[`${g},${f}`] ?? null
}

// ---------- 几何 ----------
function geom(cat) {
  const byId = Object.fromEntries(cat.objects.map((o) => [o.id, o]))
  const arrows = cat.arrows.map((a) => {
    const p = byId[a.from], q = byId[a.to]
    if (a.from === a.to) {
      const dirs = { up: [0, -1], down: [0, 1], left: [-1, 0], right: [1, 0] }
      const [dx, dy] = dirs[a.loop || 'up']
      const nx = -dy, ny = dx
      const s = { x: p.x + dx * R + nx * 7, y: p.y + dy * R + ny * 7 }
      const e = { x: p.x + dx * R - nx * 7, y: p.y + dy * R - ny * 7 }
      const L = 34
      const d = `M${s.x},${s.y} C${s.x + dx * L + nx * 18},${s.y + dy * L + ny * 18} ${e.x + dx * L - nx * 18},${e.y + dy * L - ny * 18} ${e.x},${e.y}`
      const mid = { x: p.x + dx * (R + 27), y: p.y + dy * (R + 27) }
      return { ...a, d, mid, lx: p.x + dx * (R + 42), ly: p.y + dy * (R + 42) + 4 }
    }
    const dx = q.x - p.x, dy = q.y - p.y
    const len = Math.hypot(dx, dy)
    const ux = dx / len, uy = dy / len
    const nx = uy, ny = -ux
    const bend = a.bend || 0
    const cx = (p.x + q.x) / 2 + nx * bend * 2, cy = (p.y + q.y) / 2 + ny * bend * 2
    const toC = (o) => {
      const vx = cx - o.x, vy = cy - o.y, l = Math.hypot(vx, vy)
      return { x: o.x + (vx / l) * (R + 2), y: o.y + (vy / l) * (R + 2) }
    }
    const s = toC(p), e = toC(q)
    const d = `M${s.x},${s.y} Q${cx},${cy} ${e.x},${e.y}`
    const mid = { x: 0.25 * s.x + 0.5 * cx + 0.25 * e.x, y: 0.25 * s.y + 0.5 * cy + 0.25 * e.y }
    const side = a.side ?? 1
    return { ...a, d, mid, lx: mid.x + nx * 15 * side, ly: mid.y + ny * 15 * side + 5 }
  })
  return { objects: cat.objects, arrows, byId, arrowById: Object.fromEntries(arrows.map((a) => [a.id, a])) }
}
const gC = geom(catC)
const gD = computed(() => geom(catD.value))

// ---------- 高亮 ----------
const COL = {
  sel: 'var(--vp-c-brand-1)',
  f: 'var(--vp-c-danger-1)',
  g: 'var(--vp-c-success-1, #18794e)',
  h: 'var(--vp-c-purple-1, #8e5cd9)',
  bad: 'var(--vp-c-danger-1)',
}

const highlights = computed(() => {
  const c = {}, d = {}
  const links = [] // [{ from: {x,y}, to: {x,y}, color }]
  const link = (cid, did, color, kind) => {
    const a = kind === 'obj' ? gC.byId[cid] : gC.arrowById[cid]?.mid
    const b = kind === 'obj' ? gD.value.byId[did] : gD.value.arrowById[did]?.mid
    if (a && b) links.push({ x1: a.x, y1: a.y, x2: b.x, y2: b.y, color })
  }
  if (demo.value?.kind === 'comp') {
    const st = demo.value.step
    const steps = [['f', COL.f], ['g', COL.g], ['h', COL.h]]
    steps.slice(0, st).forEach(([m, col]) => {
      c[m] = col
      d[morF(m)] = col
      link(m, morF(m), col, 'arr')
    })
  } else if (demo.value?.kind === 'id') {
    for (const o of C.objects) {
      const m = `id_${o.id}`
      const ok = morF(m) === `id_${objF(o.id)}`
      c[m] = ok ? COL.g : COL.bad
      d[morF(m)] = ok ? COL.g : COL.bad
      link(m, morF(m), ok ? COL.g : COL.bad, 'arr')
    }
  } else if (sel.value) {
    const { side, id, kind } = sel.value
    if (side === 'C') {
      c[id] = COL.sel
      const img = kind === 'obj' ? objF(id) : morF(id)
      d[img] = COL.sel
      link(id, img, COL.sel, kind)
    } else {
      d[id] = COL.sel
      if (kind === 'obj') {
        for (const o of C.objects) if (objF(o.id) === id) { c[o.id] = COL.sel; link(o.id, id, COL.sel, 'obj') }
      } else {
        for (const a of catC.arrows) if (morF(a.id) === id) { c[a.id] = COL.sel; link(a.id, id, COL.sel, 'arr') }
      }
    }
  }
  return { c, d, links }
})

const labelOf = (cat, id) => {
  const a = cat.arrows.find((x) => x.id === id)
  if (!a) return id
  return a.isId ? `id_${cat.objects.find((o) => o.id === a.from).label}` : a.label
}
const objLabel = (cat, id) => cat.objects.find((o) => o.id === id)?.label ?? id

const info = computed(() => {
  if (!sel.value || demo.value) return ''
  const { side, id, kind } = sel.value
  if (side === 'C') {
    if (kind === 'obj') return `F ${objLabel(catC, id)} = ${objLabel(catD.value, objF(id))}`
    const a = catC.arrows.find((x) => x.id === id)
    const img = morF(id)
    return `F(${labelOf(catC, id)}) = ${labelOf(catD.value, img)}  :  F ${a.from} → F ${a.to}，即 ${objLabel(catD.value, objF(a.from))} → ${objLabel(catD.value, objF(a.to))}`
  }
  if (kind === 'obj') {
    const pre = C.objects.filter((o) => objF(o.id) === id).map((o) => o.label)
    return pre.length ? `${objLabel(catD.value, id)} 的原像：${pre.join('，')}` : `${objLabel(catD.value, id)} 不是任何对象的像（函子不必是满的）`
  }
  const pre = catC.arrows.filter((a) => morF(a.id) === id).map((a) => labelOf(catC, a.id))
  return pre.length ? `${labelOf(catD.value, id)} 的原像：${pre.join('，')}` : `${labelOf(catD.value, id)} 不是任何箭头的像`
})

const verdict = ref(null)

function runComp() {
  clearTimers()
  sel.value = null
  verdict.value = null
  demo.value = { kind: 'comp', step: 0 }
  ;[1, 2, 3].forEach((s, i) => timers.push(setTimeout(() => (demo.value = { kind: 'comp', step: s }), 550 * (i + 1))))
  timers.push(setTimeout(() => {
    const Fh = morF('h')
    const FgFf = compose(catD.value, morF('g'), morF('f'))
    verdict.value = {
      ok: Fh === FgFf,
      text: `F(g∘f) = ${labelOf(catD.value, Fh)}；  F g ∘ F f = ${labelOf(catD.value, morF('g'))} ∘ ${labelOf(catD.value, morF('f'))} = ${FgFf ? labelOf(catD.value, FgFf) : '?'}`,
    }
  }, 550 * 3 + 250))
}

function runId() {
  clearTimers()
  sel.value = null
  demo.value = { kind: 'id', step: 1 }
  const rows = C.objects.map((o) => {
    const img = morF(`id_${o.id}`)
    const want = `id_${objF(o.id)}`
    return `F(id_${o.label}) = ${labelOf(catD.value, img)} ${img === want ? '=' : '≠'} ${labelOf(catD.value, want)}`
  })
  const ok = C.objects.every((o) => morF(`id_${o.id}`) === `id_${objF(o.id)}`)
  verdict.value = { ok, text: rows.join('；  ') }
}

function click(side, kind, id) {
  clearTimers()
  demo.value = null
  verdict.value = null
  sel.value = sel.value && sel.value.side === side && sel.value.id === id ? null : { side, kind, id }
}

const lawStatus = computed(() => {
  const compOk = morF('h') === compose(catD.value, morF('g'), morF('f'))
  const idOk = C.objects.every((o) => morF(`id_${o.id}`) === `id_${objF(o.id)}`)
  return { compOk, idOk }
})

const mapTable = computed(() => ({
  objs: C.objects.map((o) => `${o.label} ↦ ${objLabel(catD.value, objF(o.id))}`),
  mors: catC.arrows.map((a) => `${labelOf(catC, a.id)} ↦ ${labelOf(catD.value, morF(a.id))}`),
}))
</script>

<template>
  <div class="ctfp-widget fm">
    <div class="ctfp-widget-title">函子是范畴之间的映射：点击左边或右边的对象、箭头，看它的像（或原像）</div>

    <div class="fm-choices">
      <button v-for="(fn, i) in FUNCTORS" :key="fn.key" class="ctfp-btn" :class="{ on: fi === i, bad: fn.key === 'tear' || fn.key === 'noid' }" @click="pickFunctor(i)">
        {{ fn.name }}
      </button>
    </div>
    <p class="fm-desc">{{ F.desc }}</p>

    <svg class="fm-svg" viewBox="0 0 660 300" role="img">
      <defs>
        <marker :id="`fm-ah-${uid}`" viewBox="0 0 10 10" refX="8.5" refY="5" markerUnits="userSpaceOnUse" markerWidth="10" markerHeight="10" orient="auto-start-reverse">
          <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
        </marker>
      </defs>

      <rect x="8" y="8" width="304" height="284" rx="16" class="fm-panel" />
      <rect x="348" y="8" width="304" height="284" rx="16" class="fm-panel d" />
      <text x="24" y="34" class="fm-cat">𝒞</text>
      <text x="364" y="34" class="fm-cat">𝒟</text>
      <text x="330" y="156" class="fm-F" text-anchor="middle">F</text>

      <!-- 映射连线 -->
      <line v-for="(l, i) in highlights.links" :key="'l' + i" :x1="l.x1" :y1="l.y1" :x2="l.x2" :y2="l.y2" class="fm-link" :stroke="l.color" />

      <!-- 两个范畴 -->
      <g v-for="side in ['C', 'D']" :key="side">
        <g
          v-for="a in (side === 'C' ? gC : gD).arrows"
          :key="side + a.id"
          class="fm-arrow"
          :class="{ idarrow: a.isId }"
          @click="click(side, 'arr', a.id)"
        >
          <path :d="a.d" class="fm-hit" />
          <path
            :d="a.d"
            fill="none"
            :stroke="(side === 'C' ? highlights.c : highlights.d)[a.id] || (a.isId ? 'var(--vp-c-text-3)' : 'var(--vp-c-text-1)')"
            :stroke-width="(side === 'C' ? highlights.c : highlights.d)[a.id] ? 3 : 1.5"
            :marker-end="`url(#fm-ah-${uid})`"
          />
          <text
            :x="a.lx" :y="a.ly" text-anchor="middle"
            class="fm-alabel" :class="{ small: a.isId }"
            :fill="(side === 'C' ? highlights.c : highlights.d)[a.id] || (a.isId ? 'var(--vp-c-text-3)' : 'var(--vp-c-text-1)')"
          >{{ a.label }}</text>
        </g>
        <g
          v-for="o in (side === 'C' ? gC : gD).objects"
          :key="side + o.id"
          class="fm-obj"
          @click="click(side, 'obj', o.id)"
        >
          <circle
            :cx="o.x" :cy="o.y" :r="R"
            :stroke="(side === 'C' ? highlights.c : highlights.d)[o.id] || 'var(--vp-c-text-2)'"
            :stroke-width="(side === 'C' ? highlights.c : highlights.d)[o.id] ? 3 : 1.4"
          />
          <text :x="o.x" :y="o.y + 6" text-anchor="middle" class="fm-olabel">{{ o.label }}</text>
        </g>
      </g>
    </svg>

    <div class="fm-info" :class="{ ok: verdict && verdict.ok, bad: verdict && !verdict.ok }">
      <template v-if="verdict">{{ verdict.ok ? '✓ ' : '✗ ' }}{{ verdict.text }}</template>
      <template v-else-if="info">{{ info }}</template>
      <template v-else-if="demo">……</template>
      <template v-else>提示：点一个对象或箭头试试。灰色的小圈是恒等箭头，它们也可以点。</template>
    </div>

    <div class="fm-controls">
      <button class="ctfp-btn" @click="runComp">▶ 检验复合：F(g∘f) = F g ∘ F f ?</button>
      <button class="ctfp-btn" @click="runId">▶ 检验恒等：F(id) = id ?</button>
    </div>

    <div class="fm-table">
      <div><b>对象：</b><code v-for="s in mapTable.objs" :key="s">{{ s }}</code></div>
      <div><b>箭头：</b><code v-for="s in mapTable.mors" :key="s">{{ s }}</code></div>
      <div class="fm-laws">
        <span :class="lawStatus.compOk ? 'ok' : 'bad'">{{ lawStatus.compOk ? '✓' : '✗' }} 保持复合</span>
        <span :class="lawStatus.idOk ? 'ok' : 'bad'">{{ lawStatus.idOk ? '✓' : '✗' }} 保持恒等</span>
        <span :class="lawStatus.compOk && lawStatus.idOk ? 'ok' : 'bad'">
          {{ lawStatus.compOk && lawStatus.idOk ? '这是一个函子' : '这不是函子' }}
        </span>
      </div>
    </div>
  </div>
</template>

<style scoped>
.fm-choices {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
}
.fm-choices .bad.on {
  border-color: var(--vp-c-danger-1);
  color: var(--vp-c-danger-1);
}
.fm-desc {
  font-size: 13px;
  color: var(--vp-c-text-2);
  margin: 10px 0 6px;
  min-height: 2.6em;
}
.fm-svg {
  width: 100%;
  max-width: 660px;
  height: auto;
  display: block;
  margin: 0 auto;
  user-select: none;
}
.fm-panel {
  fill: var(--vp-c-bg);
  stroke: var(--vp-c-divider);
}
.fm-cat {
  font-size: 20px;
  fill: var(--vp-c-text-2);
  font-family: 'Times New Roman', serif;
  font-style: italic;
}
.fm-F {
  font-size: 18px;
  font-style: italic;
  fill: var(--vp-c-brand-1);
  font-family: 'Times New Roman', serif;
}
.fm-link {
  stroke-dasharray: 5 5;
  stroke-width: 1.6;
  opacity: 0.8;
}
.fm-arrow,
.fm-obj {
  cursor: pointer;
}
.fm-hit {
  fill: none;
  stroke: transparent;
  stroke-width: 14;
}
.fm-arrow path {
  transition: stroke 0.25s, stroke-width 0.25s;
}
.fm-alabel {
  font-family: 'Times New Roman', serif;
  font-style: italic;
  font-size: 16px;
}
.fm-alabel.small {
  font-size: 11px;
}
.fm-obj circle {
  fill: var(--vp-c-bg-soft);
  transition: stroke 0.25s, stroke-width 0.25s;
}
.fm-olabel {
  font-family: 'Times New Roman', serif;
  font-style: italic;
  font-size: 17px;
  fill: var(--vp-c-text-1);
  pointer-events: none;
}
.fm-info {
  text-align: center;
  font-size: 14px;
  min-height: 1.8em;
  margin: 6px 0;
  color: var(--vp-c-text-1);
  font-family: var(--vp-font-family-mono);
  word-break: break-word;
}
.fm-info.ok {
  color: var(--vp-c-success-1, #18794e);
}
.fm-info.bad {
  color: var(--vp-c-danger-1);
}
.fm-controls {
  display: flex;
  flex-wrap: wrap;
  gap: 8px;
  justify-content: center;
  margin-bottom: 10px;
}
.fm-table {
  font-size: 13px;
  display: flex;
  flex-direction: column;
  gap: 4px;
}
.fm-table code {
  margin-right: 6px;
  font-size: 12px;
}
.fm-laws {
  display: flex;
  gap: 14px;
  flex-wrap: wrap;
  margin-top: 2px;
}
.fm-laws .ok {
  color: var(--vp-c-success-1, #18794e);
}
.fm-laws .bad {
  color: var(--vp-c-danger-1);
}
</style>
