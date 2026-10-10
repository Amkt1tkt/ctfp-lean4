<script setup>
// 1.1 复合游乐场：在一个小范畴里依次点击首尾相接的箭头，观察复合结果、恒等律与结合律。
import { computed, ref, onBeforeUnmount } from 'vue'
import katex from 'katex'

const R = 24

const objects = {
  A: { x: 130, y: 90 },
  B: { x: 130, y: 310 },
  C: { x: 490, y: 310 },
  D: { x: 490, y: 90 },
}

// word：沿箭头方向依次经过的“生成箭头”，用来计算复合（复合 = 把两个 word 接起来）。
const arrows = [
  { id: 'f', src: 'A', tgt: 'B', word: ['f'], tex: 'f', kind: 'gen', lab: [104, 200] },
  { id: 'g', src: 'B', tgt: 'C', word: ['g'], tex: 'g', kind: 'gen', lab: [310, 334] },
  { id: 'h', src: 'C', tgt: 'D', word: ['h'], tex: 'h', kind: 'gen', lab: [516, 200] },
  { id: 'u', src: 'A', tgt: 'C', word: ['f', 'g'], tex: 'u', kind: 'comp', lab: [222, 136] },
  { id: 'v', src: 'B', tgt: 'D', word: ['g', 'h'], tex: 'v', kind: 'comp', lab: [222, 264] },
  { id: 'w', src: 'A', tgt: 'D', word: ['f', 'g', 'h'], tex: 'w', kind: 'comp', lab: [310, 66] },
  { id: 'idA', src: 'A', tgt: 'A', word: [], tex: '\\mathrm{id}_A', kind: 'id', dir: [-1, -1] },
  { id: 'idB', src: 'B', tgt: 'B', word: [], tex: '\\mathrm{id}_B', kind: 'id', dir: [-1, 1] },
  { id: 'idC', src: 'C', tgt: 'C', word: [], tex: '\\mathrm{id}_C', kind: 'id', dir: [1, 1] },
  { id: 'idD', src: 'D', tgt: 'D', word: [], tex: '\\mathrm{id}_D', kind: 'id', dir: [1, -1] },
]
const byId = Object.fromEntries(arrows.map((a) => [a.id, a]))

function compose(second, first) {
  if (first.tgt !== second.src) return null
  const word = [...first.word, ...second.word]
  return arrows.find((a) => a.src === first.src && a.tgt === second.tgt && a.word.join() === word.join()) || null
}

function geometry(a) {
  const p = objects[a.src]
  const q = objects[a.tgt]
  if (a.kind === 'id') {
    const len = Math.hypot(a.dir[0], a.dir[1])
    const dx = a.dir[0] / len
    const dy = a.dir[1] / len
    const nx = -dy
    const ny = dx
    const s = { x: p.x + dx * R + nx * 10, y: p.y + dy * R + ny * 10 }
    const e = { x: p.x + dx * R - nx * 10, y: p.y + dy * R - ny * 10 }
    const L = 58
    const d = `M${s.x},${s.y} C${s.x + dx * L + nx * 30},${s.y + dy * L + ny * 30} ${e.x + dx * L - nx * 30},${e.y + dy * L - ny * 30} ${e.x},${e.y}`
    return { d, lx: p.x + dx * (R + 66), ly: p.y + dy * (R + 66) }
  }
  const dx = q.x - p.x
  const dy = q.y - p.y
  const len = Math.hypot(dx, dy)
  const ux = dx / len
  const uy = dy / len
  const s = { x: p.x + ux * R, y: p.y + uy * R }
  const e = { x: q.x - ux * (R + 3), y: q.y - uy * (R + 3) }
  return { d: `M${s.x},${s.y} L${e.x},${e.y}`, lx: a.lab[0], ly: a.lab[1] }
}
const geo = Object.fromEntries(arrows.map((a) => [a.id, geometry(a)]))

const tex = (s) => katex.renderToString(s, { throwOnError: false })

// ---------- 状态 ----------
const path = ref([]) // 按“行走顺序”记录的箭头 id
const message = ref({ text: '从任意一个对象出发，点击一条箭头开始。', kind: 'info' })
const flash = ref(null)
const anim = ref(null) // { pair: [id, id], result: id }
const animKey = ref(null)
const showTable = ref(false)
let timers = []

function clearTimers() {
  timers.forEach(clearTimeout)
  timers = []
}
onBeforeUnmount(clearTimers)

const endpoint = computed(() => (path.value.length ? byId[path.value[path.value.length - 1]].tgt : null))
const startpoint = computed(() => (path.value.length ? byId[path.value[0]].src : null))

const result = computed(() => {
  let acc = null
  for (const id of path.value) {
    const a = byId[id]
    acc = acc ? compose(a, acc) : a
  }
  return acc
})

const mathOrder = computed(() => [...path.value].reverse().map((id) => byId[id]))

function clickArrow(id) {
  clearTimers()
  anim.value = null
  animKey.value = null
  const a = byId[id]
  if (endpoint.value && a.src !== endpoint.value) {
    const last = byId[path.value[path.value.length - 1]]
    message.value = {
      kind: 'error',
      html: `首尾不相接，无法复合：${tex(last.tex)} 的终点是 ${tex(last.tgt)}，而 ${tex(a.tex)} 的起点是 ${tex(a.src)}。`,
    }
    flash.value = id
    timers.push(setTimeout(() => (flash.value = null), 600))
    return
  }
  path.value = [...path.value, id]
  if (a.kind === 'id' && path.value.length > 1) {
    message.value = { kind: 'ok', html: `恒等箭头 ${tex(a.tex)} 是复合的单位：加上它，结果不变。` }
  } else if (path.value.length === 1) {
    message.value = { kind: 'info', html: `现在停在 ${tex(a.tgt)}。接下来只能点击从 ${tex(a.tgt)} 出发的箭头（其余箭头已变淡）。` }
  } else {
    message.value = { kind: 'ok', html: `复合成功！结果是一条从 ${tex(startpoint.value)} 到 ${tex(a.tgt)} 的箭头。` }
  }
}

function undo() {
  clearTimers()
  anim.value = null
  animKey.value = null
  path.value = path.value.slice(0, -1)
  message.value = { kind: 'info', text: path.value.length ? '已撤销最后一步。' : '从任意一个对象出发，点击一条箭头开始。' }
}

function reset() {
  clearTimers()
  anim.value = null
  animKey.value = null
  path.value = []
  message.value = { kind: 'info', text: '从任意一个对象出发，点击一条箭头开始。' }
}

function preset(ids, text) {
  clearTimers()
  anim.value = null
  animKey.value = null
  path.value = ids
  message.value = { kind: 'info', text }
}

// ---------- 加括号（结合律） ----------
function trees(list, i, j) {
  if (i === j) return [{ leaf: list[i] }]
  const out = []
  for (let k = i; k < j; k++) {
    for (const L of trees(list, i, k)) for (const Rt of trees(list, k + 1, j)) out.push({ left: L, right: Rt })
  }
  return out
}
function texOf(node, top = true) {
  if (node.leaf) return node.leaf.tex
  const s = `${texOf(node.left, false)} \\circ ${texOf(node.right, false)}`
  return top ? s : `(${s})`
}
function reduceOnce(node) {
  if (node.leaf) return null
  if (node.left.leaf && node.right.leaf) {
    const r = compose(node.left.leaf, node.right.leaf)
    return { node: { leaf: r }, step: { pair: [node.left.leaf.id, node.right.leaf.id], result: r.id } }
  }
  const l = reduceOnce(node.left)
  if (l) return { node: { left: l.node, right: node.right }, step: l.step }
  const r = reduceOnce(node.right)
  return { node: { left: node.left, right: r.node }, step: r.step }
}

const MAX_BRACKET = 4
const bracketings = computed(() => {
  const m = mathOrder.value
  if (m.length < 2 || m.length > MAX_BRACKET) return []
  return trees(m, 0, m.length - 1).map((t) => {
    const chain = [texOf(t)]
    const steps = []
    let cur = t
    while (!cur.leaf) {
      const r = reduceOnce(cur)
      steps.push(r.step)
      cur = r.node
      chain.push(texOf(cur))
    }
    return { html: tex(chain.join(' = ')), steps }
  })
})

function catalan(n) {
  let c = 1
  for (let i = 0; i < n - 1; i++) c = (c * 2 * (2 * i + 1)) / (i + 2)
  return c
}

function play(bi) {
  clearTimers()
  const b = bracketings.value[bi]
  animKey.value = bi
  b.steps.forEach((s, k) => {
    timers.push(setTimeout(() => (anim.value = { pair: s.pair, result: null }), k * 1600))
    timers.push(setTimeout(() => (anim.value = { pair: s.pair, result: s.result }), k * 1600 + 800))
  })
  timers.push(
    setTimeout(() => {
      anim.value = null
      animKey.value = null
    }, b.steps.length * 1600 + 900),
  )
}

// ---------- 样式辅助 ----------
function arrowState(a) {
  if (flash.value === a.id) return 'flash'
  if (anim.value) {
    if (anim.value.result === a.id) return 'result'
    if (anim.value.pair.includes(a.id)) return 'pair'
    return 'dim'
  }
  if (path.value.length) {
    if (result.value && result.value.id === a.id && path.value.length > 1) return 'result'
    if (path.value.includes(a.id)) return 'path'
    if (a.src !== endpoint.value) return 'dim'
  }
  return 'idle'
}

const pathHtml = computed(() => {
  if (!path.value.length) return ''
  const m = mathOrder.value
  const r = result.value
  const lhs = m.map((a) => a.tex).join(' \\circ ')
  const typ = `${r.tex} : ${r.src} \\to ${r.tgt}`
  return m.length > 1 ? tex(`${lhs} = ${r.tex}`) + '　　' + tex(typ) : tex(typ)
})

const tableRows = computed(() =>
  arrows.map((second) => ({
    head: second,
    cells: arrows.map((first) => compose(second, first)),
  })),
)
</script>

<template>
  <div class="ctfp-widget ch11-play">
    <div class="ctfp-widget-title">复合游乐场：一个有 4 个对象、10 条箭头的小范畴</div>
    <p class="hint">
      按箭头<strong>行走的顺序</strong>依次点击首尾相接的箭头（可以点恒等箭头和虚线的复合箭头）。
      下方公式按数学习惯<strong>从右往左</strong>写：先走的箭头在最右边。
    </p>
    <div class="stage">
      <svg viewBox="0 0 620 400" role="img" aria-label="一个小范畴">
        <defs>
          <marker id="ch11-ah" viewBox="0 0 10 10" refX="8.5" refY="5" markerUnits="userSpaceOnUse" markerWidth="12" markerHeight="12" orient="auto">
            <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
          </marker>
        </defs>
        <g v-for="a in arrows" :key="a.id" :class="['arr', a.kind, arrowState(a)]" @click="clickArrow(a.id)">
          <path class="hit" :d="geo[a.id].d" />
          <path class="line" :d="geo[a.id].d" marker-end="url(#ch11-ah)" />
          <text class="alab" :x="geo[a.id].lx" :y="geo[a.id].ly" text-anchor="middle" dominant-baseline="middle">
            <template v-if="a.kind === 'id'">id<tspan class="sub" dy="5">{{ a.src }}</tspan></template>
            <template v-else>{{ a.tex }}</template>
          </text>
        </g>
        <g v-for="(o, name) in objects" :key="name" :class="['obj', { here: endpoint === name, start: startpoint === name && endpoint !== name }]">
          <circle :cx="o.x" :cy="o.y" :r="R" />
          <text :x="o.x" :y="o.y + 1" text-anchor="middle" dominant-baseline="middle">{{ name }}</text>
        </g>
      </svg>
    </div>
    <div class="legend">
      <span><i class="sw gen" />生成箭头 f, g, h</span>
      <span><i class="sw comp" />复合箭头 u, v, w（范畴要求它们存在）</span>
      <span><i class="sw id" />恒等箭头</span>
    </div>

    <div :class="['msg', message.kind]">
      <span v-if="message.html" v-html="message.html" />
      <span v-else>{{ message.text }}</span>
    </div>

    <div class="formula">
      <span class="flabel">当前路径：</span>
      <span v-if="path.length" v-html="pathHtml" />
      <span v-else class="muted">（空）</span>
    </div>

    <div class="buttons">
      <button class="ctfp-btn" :disabled="!path.length" @click="undo">撤销</button>
      <button class="ctfp-btn" :disabled="!path.length" @click="reset">清空</button>
      <span class="sep" />
      <button class="ctfp-btn" @click="preset(['f', 'g'], '示例：先 f 再 g，复合的结果就是 u。')">示例：g ∘ f</button>
      <button class="ctfp-btn" @click="preset(['idA', 'f', 'idB'], '示例：两端加上恒等箭头，结果仍然是 f。')">示例：恒等律</button>
      <button class="ctfp-btn" @click="preset(['f', 'g', 'h'], '示例：三条箭头有两种加括号的方式，点 ▶ 看它们如何得到同一条箭头。')">示例：结合律</button>
    </div>

    <div v-if="bracketings.length > 1" class="brackets">
      <div class="btitle">所有加括号的方式（共 {{ bracketings.length }} 种）——结果都相同，这就是结合律：</div>
      <div v-for="(b, i) in bracketings" :key="i" :class="['brow', { on: animKey === i }]">
        <button class="ctfp-btn play" @click="play(i)">▶</button>
        <span v-html="b.html" />
      </div>
    </div>
    <div v-else-if="path.length > MAX_BRACKET" class="brackets muted">
      这条路径有 {{ path.length }} 条箭头，共有 {{ catalan(path.length) }} 种加括号方式，这里只列出不超过 {{ MAX_BRACKET }} 条箭头的情形。
    </div>

    <div class="tablebox">
      <button class="ctfp-btn" @click="showTable = !showTable">{{ showTable ? '收起复合表' : '查看完整的复合表' }}</button>
      <div v-if="showTable" class="tablewrap">
        <p class="hint">第 <em>行</em> 的箭头 ∘ 第 <em>列</em> 的箭头（先走列，再走行）。“·”表示首尾不相接、不能复合。一个范畴的全部信息，就是这张表加上结合律与恒等律。</p>
        <table>
          <thead>
            <tr>
              <th>∘</th>
              <th v-for="c in arrows" :key="c.id"><span v-html="tex(c.tex)" /></th>
            </tr>
          </thead>
          <tbody>
            <tr v-for="row in tableRows" :key="row.head.id">
              <th><span v-html="tex(row.head.tex)" /></th>
              <td v-for="(cell, j) in row.cells" :key="j" :class="{ none: !cell }">
                <span v-if="cell" v-html="tex(cell.tex)" />
                <span v-else>·</span>
              </td>
            </tr>
          </tbody>
        </table>
      </div>
    </div>
  </div>
</template>

<style scoped>
.ch11-play {
  max-width: 100%;
}
.hint {
  margin: 0 0 8px;
  font-size: 13px;
  color: var(--vp-c-text-2);
  line-height: 1.7;
}
.stage {
  display: flex;
  justify-content: center;
}
.stage svg {
  width: 100%;
  max-width: 560px;
  height: auto;
  user-select: none;
}
.arr {
  cursor: pointer;
}
.arr .hit {
  fill: none;
  stroke: transparent;
  stroke-width: 18;
}
.arr .line {
  fill: none;
  stroke: var(--vp-c-text-1);
  stroke-width: 2;
  transition: stroke 0.2s, stroke-width 0.2s, opacity 0.2s;
}
.arr.comp .line {
  stroke-dasharray: 7 5;
  stroke: var(--vp-c-purple-1, #8e5cd9);
}
.arr.id .line {
  stroke: var(--vp-c-text-3);
}
.arr .alab {
  font-family: 'KaTeX_Math', 'Times New Roman', serif;
  font-style: italic;
  font-size: 19px;
  fill: var(--vp-c-text-1);
  pointer-events: none;
  transition: fill 0.2s;
}
.arr.comp .alab {
  fill: var(--vp-c-purple-1, #8e5cd9);
}
.arr.id .alab {
  font-style: normal;
  font-family: 'KaTeX_Main', 'Times New Roman', serif;
  font-size: 16px;
  fill: var(--vp-c-text-2);
}
.arr .alab .sub {
  font-size: 12px;
  font-style: italic;
}
.arr:hover .line {
  stroke-width: 3.2;
}
.arr.dim {
  opacity: 0.25;
}
.arr.path .line {
  stroke: var(--vp-c-brand-1);
  stroke-width: 3.4;
}
.arr.path .alab {
  fill: var(--vp-c-brand-1);
}
.arr.pair .line {
  stroke: var(--vp-c-warning-1);
  stroke-width: 3.6;
}
.arr.pair .alab {
  fill: var(--vp-c-warning-1);
}
.arr.result .line {
  stroke: var(--vp-c-success-1, #18794e);
  stroke-width: 4;
  stroke-dasharray: none;
}
.arr.result .alab {
  fill: var(--vp-c-success-1, #18794e);
  font-weight: 700;
}
.arr.flash .line {
  stroke: var(--vp-c-danger-1);
  stroke-width: 4;
}
.obj circle {
  fill: var(--vp-c-bg);
  stroke: var(--vp-c-text-1);
  stroke-width: 2;
  transition: stroke 0.2s, stroke-width 0.2s;
}
.obj text {
  font-family: 'KaTeX_Math', 'Times New Roman', serif;
  font-style: italic;
  font-size: 22px;
  fill: var(--vp-c-text-1);
  pointer-events: none;
}
.obj.here circle {
  stroke: var(--vp-c-brand-1);
  stroke-width: 4;
}
.obj.start circle {
  stroke: var(--vp-c-brand-1);
  stroke-dasharray: 4 3;
  stroke-width: 2.5;
}
.legend {
  display: flex;
  flex-wrap: wrap;
  gap: 6px 18px;
  justify-content: center;
  font-size: 12px;
  color: var(--vp-c-text-2);
  margin: 2px 0 10px;
}
.legend .sw {
  display: inline-block;
  width: 22px;
  height: 0;
  border-top: 2px solid var(--vp-c-text-1);
  vertical-align: middle;
  margin-right: 6px;
}
.legend .sw.comp {
  border-top: 2px dashed var(--vp-c-purple-1, #8e5cd9);
}
.legend .sw.id {
  border-top-color: var(--vp-c-text-3);
}
.msg {
  font-size: 14px;
  padding: 8px 12px;
  border-radius: 8px;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
  min-height: 40px;
  line-height: 1.7;
}
.msg.error {
  border-color: var(--vp-c-danger-1);
  color: var(--vp-c-danger-1);
}
.msg.ok {
  border-color: var(--vp-c-success-1, #18794e);
}
.formula {
  margin: 10px 0;
  font-size: 16px;
  min-height: 30px;
  overflow-x: auto;
}
.flabel {
  font-size: 13px;
  color: var(--vp-c-text-2);
}
.muted {
  color: var(--vp-c-text-3);
  font-size: 13px;
}
.buttons {
  display: flex;
  flex-wrap: wrap;
  gap: 8px;
  align-items: center;
}
.buttons .sep {
  flex: 0 0 8px;
}
.ctfp-btn:disabled {
  opacity: 0.45;
  cursor: default;
}
.brackets {
  margin-top: 14px;
  padding-top: 10px;
  border-top: 1px dashed var(--vp-c-divider);
}
.btitle {
  font-size: 13px;
  color: var(--vp-c-text-2);
  margin-bottom: 6px;
}
.brow {
  display: flex;
  align-items: center;
  gap: 10px;
  padding: 4px 8px;
  border-radius: 8px;
  overflow-x: auto;
  transition: background 0.2s;
}
.brow.on {
  background: var(--vp-c-bg);
}
.brow .play {
  padding: 2px 10px;
  flex: none;
}
.tablebox {
  margin-top: 14px;
}
.tablewrap {
  margin-top: 8px;
  overflow-x: auto;
  max-width: 100%;
}
.tablewrap table {
  border-collapse: collapse;
  font-size: 13px;
  margin: 0;
  display: table;
}
.tablewrap th,
.tablewrap td {
  border: 1px solid var(--vp-c-divider);
  padding: 3px 7px;
  text-align: center;
  white-space: nowrap;
}
.tablewrap td.none {
  color: var(--vp-c-text-3);
}
</style>
