<script setup>
// 费马最短时间原理：拖动光线在水面上的入射点，比较所有“候选路径”的用时；
// 既可以像命令式那样一小步一小步地往下走（梯度下降），也可以像声明式那样直接“挑出最优者”。
import { computed, ref, onBeforeUnmount } from 'vue'

const W = 640
const SH = 300 // 场景高度
const PH = 150 // 曲线图高度
const surf = 140 // 水面 y
const A = { x: 70, y: 44 }
const B = { x: 570, y: 270 }

const px = ref(200) // 入射点横坐标
const ratio = ref(0.75) // v2 / v1
const v1 = 1
const v2 = computed(() => ratio.value)
const steps = ref(0)
const mode = ref('') // '' | 'local' | 'global'

const T = (x) => Math.hypot(x - A.x, surf - A.y) / v1 + Math.hypot(B.x - x, B.y - surf) / v2.value
const dT = (x) => (x - A.x) / Math.hypot(x - A.x, surf - A.y) / v1 - (B.x - x) / Math.hypot(B.x - x, B.y - surf) / v2.value

const xmin = computed(() => {
  // T 是凸函数：三分法求最小值
  let lo = A.x, hi = B.x
  for (let i = 0; i < 80; i++) {
    const m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3
    if (T(m1) < T(m2)) hi = m2
    else lo = m1
  }
  return (lo + hi) / 2
})

const sin1 = computed(() => (px.value - A.x) / Math.hypot(px.value - A.x, surf - A.y))
const sin2 = computed(() => (B.x - px.value) / Math.hypot(B.x - px.value, B.y - surf))
const snellL = computed(() => sin1.value / sin2.value)
const snellR = computed(() => v1 / v2.value)
const atMin = computed(() => Math.abs(px.value - xmin.value) < 1.5)

// 曲线图
const plot = computed(() => {
  const xs = []
  for (let x = A.x; x <= B.x; x += 5) xs.push(x)
  const ts = xs.map(T)
  const tmin = Math.min(...ts), tmax = Math.max(...ts)
  const Y = (t) => SH + 34 + (PH - 54) * (1 - (t - tmin) / (tmax - tmin || 1))
  return {
    d: xs.map((x, i) => `${i ? 'L' : 'M'}${x},${Y(ts[i])}`).join(' '),
    Y,
  }
})

let raf = 0
function animateTo(target, dur = 700) {
  cancelAnimationFrame(raf)
  const x0 = px.value, t0 = performance.now()
  const tick = (now) => {
    const t = Math.min(1, (now - t0) / dur)
    px.value = x0 + (target - x0) * (1 - (1 - t) ** 3)
    if (t < 1) raf = requestAnimationFrame(tick)
  }
  raf = requestAnimationFrame(tick)
}
function localStep() {
  mode.value = 'local'
  steps.value++
  const g = dT(px.value)
  const next = Math.min(B.x - 1, Math.max(A.x + 1, px.value - 260 * g))
  animateTo(next, 350)
}
function globalPick() {
  mode.value = 'global'
  animateTo(xmin.value)
}
function reset() {
  cancelAnimationFrame(raf)
  mode.value = ''
  steps.value = 0
  px.value = 200
}
onBeforeUnmount(() => cancelAnimationFrame(raf))

// 在场景中拖动入射点
const svgEl = ref(null)
let dragging = false
function toX(ev) {
  const r = svgEl.value.getBoundingClientRect()
  return ((ev.clientX - r.left) / r.width) * W
}
function down(ev) {
  dragging = true
  mode.value = ''
  px.value = Math.min(B.x - 1, Math.max(A.x + 1, toX(ev)))
  ev.target.setPointerCapture?.(ev.pointerId)
}
function move(ev) {
  if (dragging) px.value = Math.min(B.x - 1, Math.max(A.x + 1, toX(ev)))
}
function up() {
  dragging = false
}

const f2 = (x) => x.toFixed(3)
// 角度 a 从“竖直向下”量起：a = 0 指向下方，a = π 指向上方
const arcPath = (cx, cy, r, a0, a1) => {
  const pts = []
  for (let i = 0; i <= 16; i++) {
    const a = a0 + ((a1 - a0) * i) / 16
    pts.push(`${i ? 'L' : 'M'}${cx + r * Math.sin(a)},${cy + r * Math.cos(a)}`)
  }
  return pts.join(' ')
}
const th1 = computed(() => Math.asin(Math.min(1, Math.max(-1, sin1.value))))
const th2 = computed(() => Math.asin(Math.min(1, Math.max(-1, sin2.value))))
</script>

<template>
  <div class="ctfp-widget fm">
    <div class="ctfp-widget-title">费马原理：光在所有候选路径中挑出用时最短的那一条</div>

    <svg ref="svgEl" :viewBox="`0 0 ${W} ${SH + PH}`" class="fm-svg"
      @pointerdown="down" @pointermove="move" @pointerup="up" @pointerleave="up">
      <rect x="0" y="0" :width="W" :height="surf" class="fm-air" />
      <rect x="0" :y="surf" :width="W" :height="SH - surf" class="fm-water" />
      <text :x="W - 12" y="20" text-anchor="end" class="fm-tag">空气：光速 v₁ = 1</text>
      <text :x="12" :y="SH - 12" class="fm-tag">水：光速 v₂ = {{ ratio.toFixed(2) }}</text>
      <line x1="0" :y1="surf" :x2="W" :y2="surf" class="fm-surface" />

      <!-- 法线与角度 -->
      <line :x1="px" :y1="surf - 70" :x2="px" :y2="surf + 70" class="fm-normal" />
      <path :d="arcPath(px, surf, 34, Math.PI, Math.PI + th1)" class="fm-arc" />
      <path :d="arcPath(px, surf, 34, 0, th2)" class="fm-arc" />
      <text :x="px - 30" :y="surf - 40" class="fm-angle" text-anchor="end">θ₁</text>
      <text :x="px + 30" :y="surf + 52" class="fm-angle">θ₂</text>

      <!-- 光路 -->
      <line :x1="A.x" :y1="A.y" :x2="px" :y2="surf" class="fm-ray" :class="{ best: atMin }" />
      <line :x1="px" :y1="surf" :x2="B.x" :y2="B.y" class="fm-ray" :class="{ best: atMin }" />
      <line :x1="A.x" :y1="A.y" :x2="B.x" :y2="B.y" class="fm-straight" />
      <circle :cx="A.x" :cy="A.y" r="6" class="fm-pt" />
      <circle :cx="B.x" :cy="B.y" r="6" class="fm-pt" />
      <text :x="A.x - 10" :y="A.y + 5" text-anchor="end" class="fm-lbl">A</text>
      <text :x="B.x + 10" :y="B.y + 4" class="fm-lbl">B</text>
      <circle :cx="px" :cy="surf" r="8" class="fm-handle" />

      <!-- 用时曲线 -->
      <line x1="0" :y1="SH" :x2="W" :y2="SH" class="fm-sep" />
      <text x="12" :y="SH + 20" class="fm-tag">总用时 T(x)：每个入射点 x 对应一条候选路径</text>
      <path :d="plot.d" class="fm-curve" />
      <line :x1="xmin" :y1="SH + 30" :x2="xmin" :y2="SH + PH - 8" class="fm-minline" />
      <text :x="xmin" :y="SH + PH - 2" text-anchor="middle" class="fm-tag">最短</text>
      <circle :cx="px" :cy="plot.Y(T(px))" r="6" class="fm-handle" />
    </svg>

    <div class="fm-controls">
      <label>水中光速 v₂/v₁：
        <input v-model.number="ratio" type="range" min="0.4" max="1" step="0.01" />
      </label>
      <button class="ctfp-btn" @click="localStep">命令式：顺着坡走一小步</button>
      <button class="ctfp-btn" @click="globalPick">声明式：直接挑出最优者</button>
      <button class="ctfp-btn" @click="reset">重置</button>
    </div>

    <div class="fm-read">
      <div>总用时 T = <b>{{ f2(T(px) / 100) }}</b>（最短可达 {{ f2(T(xmin) / 100) }}）</div>
      <div>sin θ₁ / sin θ₂ = <b>{{ f2(snellL) }}</b>，v₁ / v₂ = <b>{{ f2(snellR) }}</b>
        <span v-if="atMin" class="ok">——相等，这就是斯涅尔定律</span>
      </div>
      <div v-if="mode === 'local'" class="fm-note">已走 {{ steps }} 步：每一步只看脚下的坡度（导数），一点点逼近答案。</div>
      <div v-if="mode === 'global'" class="fm-note">一步到位：在所有候选者中“声明”那个用时最短的。两种方法终点相同。</div>
    </div>
    <div class="fm-hint">拖动水面上的圆点改变入射点；灰色虚线是“最短距离”的直线，它并不是最快的路。</div>
  </div>
</template>

<style scoped>
.fm { max-width: 100%; }
.fm-svg { width: 100%; max-width: 640px; display: block; margin: 0 auto; touch-action: none; cursor: ew-resize; user-select: none; }
.fm-air { fill: var(--vp-c-bg); }
.fm-water { fill: rgba(56, 132, 255, 0.13); }
.fm-surface { stroke: rgba(56, 132, 255, 0.7); stroke-width: 2; }
.fm-normal { stroke: var(--vp-c-text-3); stroke-dasharray: 4 4; }
.fm-arc { fill: none; stroke: var(--vp-c-text-2); stroke-width: 1.2; }
.fm-angle { font-size: 13px; fill: var(--vp-c-text-2); }
.fm-ray { stroke: var(--vp-c-warning-1); stroke-width: 3; transition: stroke 0.2s; }
.fm-ray.best { stroke: var(--vp-c-success-1, #18794e); }
.fm-straight { stroke: var(--vp-c-text-3); stroke-dasharray: 3 5; }
.fm-pt { fill: var(--vp-c-text-1); }
.fm-lbl { font-size: 14px; font-weight: 600; fill: var(--vp-c-text-1); }
.fm-handle { fill: var(--vp-c-brand-1); stroke: var(--vp-c-bg); stroke-width: 2; }
.fm-tag { font-size: 12px; fill: var(--vp-c-text-2); }
.fm-sep { stroke: var(--vp-c-divider); }
.fm-curve { fill: none; stroke: var(--vp-c-brand-1); stroke-width: 2; }
.fm-minline { stroke: var(--vp-c-success-1, #18794e); stroke-dasharray: 4 3; }
.fm-controls { display: flex; flex-wrap: wrap; gap: 8px 12px; align-items: center; justify-content: center; margin: 8px 0; font-size: 13px; }
.fm-controls input { vertical-align: middle; width: 120px; }
.fm-read { font-size: 13.5px; text-align: center; line-height: 1.8; }
.fm-read .ok { color: var(--vp-c-success-1, #18794e); font-weight: 600; }
.fm-note { color: var(--vp-c-text-2); }
.fm-hint { text-align: center; font-size: 12.5px; color: var(--vp-c-text-2); margin-top: 4px; }
</style>
