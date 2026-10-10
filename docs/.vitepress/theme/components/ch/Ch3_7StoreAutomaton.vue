<script setup>
// Store 余单子与一维元胞自动机：extend 把局部规则推广到整条“纸带”。
import { ref, computed, onBeforeUnmount } from 'vue'

const W = 63 // 环形纸带宽度：Store (Fin W) Bool
const H = 40 // 显示的代数
const CELL = 9

const rule = ref(90)
const presets = [30, 90, 110, 184]
const patterns = [7, 6, 5, 4, 3, 2, 1, 0] // 111 110 … 000

const outOf = (pat) => ((rule.value >> pat) & 1) === 1
function toggle(pat) {
  rule.value = rule.value ^ (1 << pat)
}
function setRule(r) {
  const n = Math.max(0, Math.min(255, Math.floor(Number(r) || 0)))
  rule.value = n
}

function single() {
  const row = Array(W).fill(false)
  row[Math.floor(W / 2)] = true
  return row
}
function randomRow() {
  return Array.from({ length: W }, () => Math.random() < 0.5)
}
const history = ref([single()])

// co-Kleisli 箭头：只看焦点和左右邻居（Store 的 peek 与 pos）
const peek = (row, i) => row[((i % W) + W) % W]
const localRule = (row, pos) => outOf((peek(row, pos - 1) << 2) | (peek(row, pos) << 1) | peek(row, pos + 1))
// extend：把焦点依次移到每个位置，再用局部规则
const extendRow = (row) => row.map((_, pos) => localRule(row, pos))

const current = computed(() => history.value[history.value.length - 1])

// 慢动作：partial 记录正在写的下一代，sweep 是焦点位置
const partial = ref(null)
const sweep = ref(-1)
let timer = 0
let playTimer = 0
const playing = ref(false)

function pushRow(row) {
  const h = history.value.slice()
  h.push(row)
  if (h.length > H) h.shift()
  history.value = h
}
function stopAll() {
  clearInterval(timer)
  clearInterval(playTimer)
  playing.value = false
  partial.value = null
  sweep.value = -1
}
function stepFast() {
  stopAll()
  pushRow(extendRow(current.value))
}
function slowExtend() {
  stopAll()
  const row = current.value
  partial.value = Array(W).fill(null)
  sweep.value = 0
  timer = setInterval(() => {
    const p = partial.value.slice()
    p[sweep.value] = localRule(row, sweep.value)
    partial.value = p
    sweep.value++
    if (sweep.value >= W) {
      clearInterval(timer)
      const done = partial.value
      partial.value = null
      sweep.value = -1
      pushRow(done)
    }
  }, 45)
}
function togglePlay() {
  if (playing.value) return stopAll()
  stopAll()
  playing.value = true
  playTimer = setInterval(() => pushRow(extendRow(current.value)), 110)
}
function reset(kind) {
  stopAll()
  history.value = [kind === 'random' ? randomRow() : single()]
}
onBeforeUnmount(stopAll)

// 悬停：显示某个格子依赖的上一代邻域
const hover = ref(null)
const rowsShown = computed(() => {
  const rows = history.value.map((r) => r)
  if (partial.value) rows.push(partial.value)
  return rows
})
const svgH = computed(() => Math.max(rowsShown.value.length, 1) * CELL)

const focusBox = computed(() => {
  if (sweep.value < 0) return null
  const r = history.value.length - 1
  return { r, c: sweep.value }
})
const hoverBox = computed(() => {
  if (!hover.value || hover.value.r === 0) return null
  return { r: hover.value.r - 1, c: hover.value.c }
})

function neighborhoodRects(box) {
  if (!box) return []
  return [-1, 0, 1].map((d) => ({ x: (((box.c + d) % W) + W) % W, y: box.r }))
}
</script>

<template>
  <div class="ctfp-widget ca">
    <div class="ctfp-widget-title">Store 余单子：用 extend 跑一维元胞自动机</div>
    <div class="ca-bar">
      <span class="ca-label">规则：</span>
      <button v-for="p in presets" :key="p" class="ctfp-btn" :class="{ on: rule === p }" @click="rule = p">Rule {{ p }}</button>
      <label class="ca-num">编号 <input type="number" min="0" max="255" :value="rule" @change="setRule($event.target.value)" /></label>
    </div>
    <div class="ca-table">
      <button v-for="pat in patterns" :key="pat" class="ca-pat" :title="'点击翻转这个模式的输出'" @click="toggle(pat)">
        <span class="ca-cells">
          <i :class="{ on: (pat >> 2) & 1 }"></i><i :class="{ on: (pat >> 1) & 1 }"></i><i :class="{ on: pat & 1 }"></i>
        </span>
        <span class="ca-out"><i :class="{ on: outOf(pat) }"></i></span>
      </button>
    </div>
    <div class="ca-lean">
      <code>rule (w : Store (Fin {{ W }}) Bool) : Bool := table (w.peek (w.pos - 1)) (extract w) (w.peek (w.pos + 1))</code><br />
      <code>step := extend rule</code>
    </div>

    <div class="ca-grid">
      <svg :viewBox="`0 0 ${W * CELL} ${svgH}`" :width="W * CELL" :style="{ maxWidth: '100%' }" @mouseleave="hover = null">
        <g v-for="(row, r) in rowsShown" :key="r">
          <rect
            v-for="(v, c) in row"
            :key="c"
            :x="c * CELL"
            :y="r * CELL"
            :width="CELL - 1"
            :height="CELL - 1"
            :class="['cell', { on: v === true, pending: v === null }]"
            @mouseenter="hover = { r, c }"
          />
        </g>
        <rect
          v-for="(n, i) in neighborhoodRects(focusBox)"
          :key="'f' + i"
          :x="n.x * CELL - 1"
          :y="n.y * CELL - 1"
          :width="CELL + 1"
          :height="CELL + 1"
          class="ring focus"
        />
        <rect
          v-if="focusBox"
          :x="focusBox.c * CELL - 1"
          :y="(focusBox.r + 1) * CELL - 1"
          :width="CELL + 1"
          :height="CELL + 1"
          class="ring target"
        />
        <rect
          v-for="(n, i) in neighborhoodRects(hoverBox)"
          :key="'h' + i"
          :x="n.x * CELL - 1"
          :y="n.y * CELL - 1"
          :width="CELL + 1"
          :height="CELL + 1"
          class="ring hover"
        />
      </svg>
    </div>

    <div class="ca-bar ca-controls">
      <button class="ctfp-btn" @click="slowExtend">extend 慢动作（焦点扫过整条纸带）</button>
      <button class="ctfp-btn" @click="stepFast">下一代</button>
      <button class="ctfp-btn" :class="{ on: playing }" @click="togglePlay">{{ playing ? '暂停' : '自动播放' }}</button>
      <button class="ctfp-btn" @click="reset('single')">重置（中间一个点）</button>
      <button class="ctfp-btn" @click="reset('random')">重置（随机）</button>
    </div>
    <div class="ca-tip">
      每一行是一代，最上面是最早的。慢动作里，橙框是焦点 <code>pos</code> 和它的两个邻居（co-Kleisli 箭头读取的“上下文”），
      蓝框是 extend 写出的新格子。鼠标悬停在任意格子上，可以看到它是由上一代的哪三个格子决定的。点击规则表可以翻转某个模式的输出。
    </div>
  </div>
</template>

<style scoped>
.ca-bar {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
  align-items: center;
  margin-bottom: 8px;
}
.ca-label {
  font-size: 13px;
  color: var(--vp-c-text-2);
}
.ca-num {
  font-size: 13px;
  color: var(--vp-c-text-2);
  margin-left: 6px;
}
.ca-num input {
  width: 64px;
  padding: 2px 6px;
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
}
.ca-table {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
  margin: 6px 0 10px;
}
.ca-pat {
  display: inline-flex;
  flex-direction: column;
  align-items: center;
  gap: 3px;
  padding: 5px 6px;
  border: 1px solid var(--vp-c-divider);
  border-radius: 8px;
  background: var(--vp-c-bg);
  cursor: pointer;
}
.ca-pat:hover {
  border-color: var(--vp-c-brand-1);
}
.ca-cells,
.ca-out {
  display: inline-flex;
  gap: 2px;
}
.ca-pat i {
  display: inline-block;
  width: 11px;
  height: 11px;
  border: 1px solid var(--vp-c-text-3);
  background: var(--vp-c-bg);
}
.ca-pat i.on {
  background: var(--vp-c-text-1);
  border-color: var(--vp-c-text-1);
}
.ca-out i.on {
  background: var(--vp-c-brand-1);
  border-color: var(--vp-c-brand-1);
}
.ca-lean {
  font-size: 12px;
  margin-bottom: 10px;
  line-height: 1.9;
}
.ca-lean code {
  font-size: 11.5px;
  overflow-wrap: anywhere;
  box-decoration-break: clone;
  -webkit-box-decoration-break: clone;
}
.ca-grid {
  overflow: hidden;
  border: 1px solid var(--vp-c-divider);
  border-radius: 8px;
  padding: 6px;
  background: var(--vp-c-bg);
  display: flex;
  justify-content: center;
}
.ca-grid svg {
  height: auto;
  display: block;
}
.cell {
  fill: var(--vp-c-bg-soft);
}
.cell.on {
  fill: var(--vp-c-text-1);
}
.cell.pending {
  fill: transparent;
}
.ring {
  fill: none;
  stroke-width: 1.6;
  pointer-events: none;
}
.ring.focus {
  stroke: var(--vp-c-warning-1);
}
.ring.target {
  stroke: var(--vp-c-brand-1);
}
.ring.hover {
  stroke: var(--vp-c-danger-1);
}
.ca-controls {
  margin-top: 10px;
}
.ca-tip {
  font-size: 12px;
  color: var(--vp-c-text-3);
  line-height: 1.6;
}
</style>
