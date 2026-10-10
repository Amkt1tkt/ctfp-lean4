<script setup>
// 交换图（commutative diagram）渲染器。由 ```diagram 围栏自动生成，语法见 STYLE.md。
import { computed, ref, onBeforeUnmount } from 'vue'
import katex from 'katex'

const props = defineProps({ spec: { type: String, required: true } })

const UNIT = 110
const PAD = 46
const NODE_R = 20

const COLORS = {
  brand: 'var(--vp-c-brand-1)',
  red: 'var(--vp-c-danger-1)',
  green: 'var(--vp-c-success-1, #18794e)',
  orange: 'var(--vp-c-warning-1)',
  purple: 'var(--vp-c-purple-1, #8e5cd9)',
  gray: 'var(--vp-c-text-3)',
  text: 'var(--vp-c-text-1)',
}
const color = (c) => (c ? COLORS[c] || c : COLORS.text)

function parseOpts(s) {
  const o = {}
  for (const m of s.matchAll(/([\w-]+)(?:=([^\s]+))?/g)) o[m[1]] = m[2] === undefined ? true : m[2]
  return o
}

function tex(src) {
  try {
    return katex.renderToString(src, { throwOnError: false, displayMode: false })
  } catch {
    return src
  }
}

const parsed = computed(() => {
  const nodes = []
  const arrows = []
  const paths = []
  let caption = ''
  let scale = 1
  const errors = []
  for (const raw of props.spec.split('\n')) {
    const line = raw.replace(/(^|\s)#.*$/, '').trim()
    if (!line) continue
    let m
    if ((m = line.match(/^caption:\s*(.*)$/))) caption = m[1]
    else if ((m = line.match(/^size:\s*([\d.]+)/))) scale = Number(m[1])
    else if ((m = line.match(/^path\s+"([^"]*)"\s*:\s*(.*)$/))) {
      const rest = m[2].split(/\s+/)
      const ids = rest.filter((w) => !w.includes('='))
      const o = parseOpts(rest.filter((w) => w.includes('=')).join(' '))
      paths.push({ name: m[1], ids, color: o.color || 'red' })
    } else if ((m = line.match(/^([\w']+)\s*:\s*([\w']+)\s*(->|=>|-->|<->)\s*([\w']+)\s*(?:"((?:[^"\\]|\\.)*)")?\s*(.*)$/))) {
      const o = parseOpts(m[6] || '')
      arrows.push({
        id: m[1], from: m[2], to: m[4], kind: m[3],
        label: m[5] !== undefined ? m[5] : m[1].replace(/'/g, "'"),
        bend: Number(o.bend || 0), dashed: !!o.dashed || m[3] === '-->', color: o.color,
        loop: o.loop || 'up', side: o.side || 'left', pos: Number(o.pos || 0.5), width: Number(o.width || (m[3] === '=>' ? 3.6 : 1.6)),
      })
    } else if ((m = line.match(/^([\w']+)\s*:\s*\(\s*(-?[\d.]+)\s*,\s*(-?[\d.]+)\s*\)\s*(?:"((?:[^"\\]|\\.)*)")?\s*(.*)$/))) {
      const o = parseOpts(m[5] || '')
      nodes.push({ id: m[1], x: Number(m[2]), y: Number(m[3]), label: m[4] !== undefined ? m[4] : m[1], dot: o.shape === 'dot', color: o.color })
    } else errors.push(raw)
  }
  return { nodes, arrows, paths, caption, scale, errors }
})

const geom = computed(() => {
  const { nodes, arrows, scale } = parsed.value
  const u = UNIT * scale
  const byId = Object.fromEntries(nodes.map((n) => [n.id, n]))
  const xs = nodes.map((n) => n.x), ys = nodes.map((n) => n.y)
  const minX = Math.min(...xs, 0), minY = Math.min(...ys, 0)
  const maxX = Math.max(...xs, 0), maxY = Math.max(...ys, 0)
  const P = (n) => ({ x: (n.x - minX) * u + PAD, y: (n.y - minY) * u + PAD })
  const gnodes = nodes.map((n) => ({ ...n, ...P(n), html: tex(n.label) }))
  const garrows = arrows.flatMap((a) => {
    const A = byId[a.from], B = byId[a.to]
    if (!A || !B) return []
    const p = P(A), q = P(B)
    const rA = A.dot ? 7 : NODE_R, rB = B.dot ? 8 : NODE_R + 2
    let d, lx, ly
    if (a.from === a.to) {
      const dirs = { up: [0, -1], down: [0, 1], left: [-1, 0], right: [1, 0] }
      const [dx, dy] = dirs[a.loop] || dirs.up
      const nx = -dy, ny = dx
      const s = { x: p.x + dx * rA + nx * 9, y: p.y + dy * rA + ny * 9 }
      const e = { x: p.x + dx * rA - nx * 9, y: p.y + dy * rA - ny * 9 }
      const L = 46
      d = `M${s.x},${s.y} C${s.x + dx * L + nx * 26},${s.y + dy * L + ny * 26} ${e.x + dx * L - nx * 26},${e.y + dy * L - ny * 26} ${e.x},${e.y}`
      lx = p.x + dx * (rA + 50); ly = p.y + dy * (rA + 50)
    } else {
      const dx = q.x - p.x, dy = q.y - p.y
      const len = Math.hypot(dx, dy) || 1
      const ux = dx / len, uy = dy / len
      const nx = uy, ny = -ux // 方向左侧的法向量（屏幕坐标）
      const bend = a.bend * scale
      const mx = (p.x + q.x) / 2 + nx * bend, my = (p.y + q.y) / 2 + ny * bend
      const ang = Math.atan2(bend, len / 2)
      const rot = (vx, vy, t) => [vx * Math.cos(t) - vy * Math.sin(t), vx * Math.sin(t) + vy * Math.cos(t)]
      const [sx, sy] = rot(ux, uy, -ang * 1.0)
      const [ex, ey] = rot(-ux, -uy, ang * 1.0)
      const s = { x: p.x + sx * rA, y: p.y + sy * rA }
      const e = { x: q.x + ex * rB, y: q.y + ey * rB }
      d = `M${s.x},${s.y} Q${mx * 2 - (s.x + e.x) / 2},${my * 2 - (s.y + e.y) / 2} ${e.x},${e.y}`
      const t = a.pos
      const cx = mx * 2 - (s.x + e.x) / 2, cy = my * 2 - (s.y + e.y) / 2
      const bx = (1 - t) ** 2 * s.x + 2 * (1 - t) * t * cx + t * t * e.x
      const by = (1 - t) ** 2 * s.y + 2 * (1 - t) * t * cy + t * t * e.y
      const sign = a.side === 'right' ? -1 : 1
      const off = 16 + Math.min(10, a.label.length * 1.2)
      lx = bx + nx * off * sign; ly = by + ny * off * sign
    }
    return [{ ...a, d, lx, ly, html: tex(a.label) }]
  })
  return {
    nodes: gnodes, arrows: garrows,
    w: (maxX - minX) * u + PAD * 2, h: (maxY - minY) * u + PAD * 2,
  }
})

const active = ref(null) // { idx, ids, step }
const dot = ref(null)
const uid = Math.random().toString(36).slice(2, 8)
const pathEls = {}
let raf = 0

function setRef(id, el) {
  if (el) pathEls[id] = el
}

function play(pi) {
  cancelAnimationFrame(raf)
  const p = parsed.value.paths[pi]
  active.value = { idx: pi, ids: p.ids, color: color(p.color) }
  const segs = p.ids.map((id) => pathEls[id]).filter(Boolean)
  if (!segs.length) return
  const per = 700
  const t0 = performance.now()
  const tick = (now) => {
    const t = (now - t0) / per
    const i = Math.min(Math.floor(t), segs.length - 1)
    const frac = Math.min(1, t - i)
    const el = segs[i]
    const L = el.getTotalLength()
    const pt = el.getPointAtLength(L * frac)
    dot.value = { x: pt.x, y: pt.y, step: i }
    if (t < segs.length) raf = requestAnimationFrame(tick)
    else dot.value = { ...dot.value, done: true }
  }
  raf = requestAnimationFrame(tick)
}

function reset() {
  cancelAnimationFrame(raf)
  active.value = null
  dot.value = null
}

onBeforeUnmount(() => cancelAnimationFrame(raf))

const isLit = (id) => {
  if (!active.value) return false
  const k = active.value.ids.indexOf(id)
  if (k < 0) return false
  return !dot.value || dot.value.done || k <= dot.value.step
}
</script>

<template>
  <figure class="cat-diagram">
    <svg :viewBox="`0 0 ${geom.w} ${geom.h}`" :width="geom.w" :style="{ maxWidth: '100%' }" role="img">
      <defs>
        <marker :id="`ah-${uid}`" viewBox="0 0 10 10" refX="8.5" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
          <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
        </marker>
      </defs>
      <g v-for="a in geom.arrows" :key="a.id" :class="['cd-arrow', { lit: isLit(a.id), dim: active && !isLit(a.id) }]">
        <path
          :ref="(el) => setRef(a.id, el)"
          :d="a.d" fill="none"
          :stroke="isLit(a.id) ? active.color : color(a.color)"
          :stroke-width="isLit(a.id) ? a.width + 1.4 : a.width"
          :stroke-dasharray="a.dashed ? '6 5' : null"
          :marker-end="`url(#ah-${uid})`"
          :marker-start="a.kind === '<->' ? `url(#ah-${uid})` : null"
        />
        <path v-if="a.kind === '=>'" :d="a.d" fill="none" stroke="var(--vp-c-bg)" stroke-width="1" />
        <foreignObject v-if="a.label" :x="a.lx - 70" :y="a.ly - 14" width="140" height="28">
          <div class="cd-label" :style="{ color: isLit(a.id) ? active.color : color(a.color) }" v-html="a.html" />
        </foreignObject>
      </g>
      <g v-for="n in geom.nodes" :key="n.id" class="cd-node">
        <circle v-if="n.dot" :cx="n.x" :cy="n.y" r="5" :fill="color(n.color)" />
        <foreignObject :x="n.x - 80" :y="n.dot ? n.y - 34 : n.y - 16" width="160" height="32">
          <div class="cd-label cd-node-label" :style="{ color: color(n.color) }" v-html="n.html" />
        </foreignObject>
      </g>
      <circle v-if="dot && !dot.done" :cx="dot.x" :cy="dot.y" r="6" :fill="active.color" class="cd-dot" />
    </svg>
    <div v-if="parsed.paths.length" class="cd-controls">
      <button v-for="(p, i) in parsed.paths" :key="i" :class="{ on: active && active.idx === i }" @click="play(i)">
        ▶ {{ p.name }}
      </button>
      <button v-if="active" class="cd-reset" @click="reset">重置</button>
    </div>
    <figcaption v-if="parsed.caption">{{ parsed.caption }}</figcaption>
    <pre v-if="parsed.errors.length" class="cd-error">无法解析：{{ parsed.errors.join('\n') }}</pre>
  </figure>
</template>
