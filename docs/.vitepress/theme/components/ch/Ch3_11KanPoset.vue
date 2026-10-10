<script setup>
import { computed, ref } from 'vue'

// A = {a0 < a1 < … < a7}（全序，看作范畴：x → y 当且仅当 x ≤ y）
// I ⊆ A，K 是包含；C = {⊥ < 0 < 1 < … < 8 < ⊤}
// 值的编码：0 = ⊥，1..9 = 数值 0..8，10 = ⊤
const N = 8
const TOP = 10
const BOT = 0
const vLabel = (r) => (r === TOP ? '⊤' : r === BOT ? '⊥' : String(r - 1))

const inI = ref([false, true, false, true, false, false, true, false])
const D = ref([3, 3, 4, 4, 5, 6, 7, 7]) // 只在 I 上有意义
const Fp = ref([2, 2, 3, 3, 3, 5, 6, 6])
const mode = ref('D') // 'D' | 'F'
const side = ref('right') // 'right' | 'left'
const showRan = ref(true)
const showLan = ref(true)
const showF = ref(false)

const Is = computed(() => inI.value.map((b, i) => (b ? i : -1)).filter((i) => i >= 0))

const monoViolation = computed(() => {
  const is = Is.value
  for (let x = 0; x < is.length; x++)
    for (let y = x + 1; y < is.length; y++)
      if (D.value[is[x]] > D.value[is[y]]) return [is[x], is[y]]
  return null
})

const ran = computed(() =>
  Array.from({ length: N }, (_, a) => {
    const vs = Is.value.filter((i) => i >= a).map((i) => D.value[i])
    return vs.length ? Math.min(...vs) : TOP
  }),
)
const lan = computed(() =>
  Array.from({ length: N }, (_, a) => {
    const vs = Is.value.filter((i) => i <= a).map((i) => D.value[i])
    return vs.length ? Math.max(...vs) : BOT
  }),
)

const fMonoBad = computed(() => {
  const bad = []
  for (let a = 0; a + 1 < N; a++) if (Fp.value[a] > Fp.value[a + 1]) bad.push(a)
  return bad
})
const fCondBad = computed(() =>
  Is.value.filter((i) => (side.value === 'right' ? Fp.value[i] > D.value[i] : D.value[i] > Fp.value[i])),
)
const fValid = computed(() => !fMonoBad.value.length && !fCondBad.value.length)

function toggleI(a) {
  const v = inI.value.slice()
  v[a] = !v[a]
  inI.value = v
}
function clickCell(a, r) {
  if (mode.value === 'D') {
    if (!inI.value[a] || r === TOP || r === BOT) return
    const d = D.value.slice()
    d[a] = r
    D.value = d
  } else {
    const f = Fp.value.slice()
    f[a] = r
    Fp.value = f
    showF.value = true
  }
}
function setMode(m) {
  mode.value = m
  if (m === 'F') showF.value = true
}
function copyFrom(src) {
  Fp.value = src.slice()
  showF.value = true
  mode.value = 'F'
}
function bump(delta) {
  // 把 F′ 在某个不在 I 中的位置上抬高/降低一格，演示“再大一点就不行了”
  const f = Fp.value.slice()
  const candidates = Array.from({ length: N }, (_, a) => a)
  const a = candidates.find((x) => !inI.value[x] && f[x] + delta >= BOT && f[x] + delta <= TOP) ?? 0
  f[a] = Math.max(BOT, Math.min(TOP, f[a] + delta))
  Fp.value = f
  showF.value = true
}
function reset() {
  inI.value = [false, true, false, true, false, false, true, false]
  D.value = [3, 3, 4, 4, 5, 6, 7, 7]
  Fp.value = [2, 2, 3, 3, 3, 5, 6, 6]
  showF.value = false
  mode.value = 'D'
}

// ---------- 几何 ----------
const W = 680
const H = 440
const X0 = 96
const DX = 72
const Y0 = 40
const DY = 28
const cx = (a) => X0 + a * DX
const ry = (r) => Y0 + (TOP - r) * DY
const AXIS_Y = ry(BOT) + 40
const rows = Array.from({ length: TOP + 1 }, (_, r) => r)
const cols = Array.from({ length: N }, (_, a) => a)

function stepPath(vals, dy) {
  let d = ''
  vals.forEach((v, a) => {
    const x1 = cx(a) - DX / 2 + 6
    const x2 = cx(a) + DX / 2 - 6
    const y = ry(v) + dy
    d += `M${x1},${y} L${x2},${y} `
  })
  return d
}
const ranPath = computed(() => stepPath(ran.value, -3))
const lanPath = computed(() => stepPath(lan.value, 3))
const fPath = computed(() => Fp.value.map((v, a) => `${a ? 'L' : 'M'}${cx(a)},${ry(v)}`).join(' '))

const sigma = computed(() => {
  if (!showF.value || !fValid.value) return []
  return cols
    .map((a) => {
      const from = side.value === 'right' ? Fp.value[a] : lan.value[a]
      const to = side.value === 'right' ? ran.value[a] : Fp.value[a]
      return { a, from, to }
    })
    .filter((s) => s.to > s.from)
})
</script>

<template>
  <div class="ctfp-widget kan-poset">
    <div class="ctfp-widget-title">Kan 扩张：沿 K 把 D 延伸到整个 A 上的“最好近似”</div>
    <div class="row">
      <button class="ctfp-btn" :class="{ on: mode === 'D' }" @click="setMode('D')">编辑 D</button>
      <button class="ctfp-btn" :class="{ on: mode === 'F' }" @click="setMode('F')">编辑候选 F′</button>
      <span class="sep" />
      <label><input v-model="showRan" type="checkbox" /> 显示 Ran</label>
      <label><input v-model="showLan" type="checkbox" /> 显示 Lan</label>
      <label><input v-model="showF" type="checkbox" /> 显示 F′</label>
    </div>

    <svg :viewBox="`0 0 ${W} ${H}`" class="canvas" role="img" aria-label="偏序上的 Kan 扩张">
      <defs>
        <marker id="ch311k-ah" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto" markerUnits="userSpaceOnUse">
          <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
        </marker>
      </defs>
      <!-- 行：C 的元素 -->
      <g v-for="r in rows" :key="'r' + r">
        <line :x1="X0 - DX / 2" :x2="cx(N - 1) + DX / 2" :y1="ry(r)" :y2="ry(r)" :class="['grid', { rail: r === TOP || r === BOT }]" />
        <text :x="X0 - DX / 2 - 10" :y="ry(r) + 4" text-anchor="end" class="rlab">{{ vLabel(r) }}</text>
      </g>
      <text :x="X0 - DX / 2 - 26" :y="14" class="axis-name">范畴 C（越往上越“大”）</text>

      <!-- 列背景：I 中的对象 -->
      <rect v-for="a in cols" :key="'bg' + a" :x="cx(a) - DX / 2 + 3" :y="ry(TOP) - 14" :width="DX - 6" :height="ry(BOT) - ry(TOP) + 28" rx="8" :class="['colbg', { inI: inI[a] }]" />

      <!-- 可点击的格子 -->
      <g v-for="a in cols" :key="'c' + a">
        <rect v-for="r in rows" :key="'cell' + a + '-' + r" :x="cx(a) - DX / 2 + 3" :y="ry(r) - DY / 2" :width="DX - 6" :height="DY" class="cell" :class="{ disabled: mode === 'D' && (!inI[a] || r === TOP || r === BOT) }" @click="clickCell(a, r)" />
      </g>

      <!-- Ran / Lan -->
      <path v-if="showRan && !monoViolation" :d="ranPath" class="ran-line" />
      <path v-if="showLan && !monoViolation" :d="lanPath" class="lan-line" />

      <!-- σ -->
      <g v-if="!monoViolation">
        <line v-for="s in sigma" :key="'s' + s.a" :x1="cx(s.a) + 14" :x2="cx(s.a) + 14" :y1="ry(s.from) - 4" :y2="ry(s.to) + 6" class="sigma" marker-end="url(#ch311k-ah)" />
      </g>

      <!-- F′ -->
      <g v-if="showF">
        <path :d="fPath" class="f-line" />
        <circle v-for="a in cols" :key="'f' + a" :cx="cx(a)" :cy="ry(Fp[a])" r="7" :class="['f-dot', { bad: fCondBad.includes(a) }]" />
      </g>

      <!-- D -->
      <g v-for="i in Is" :key="'d' + i">
        <circle :cx="cx(i)" :cy="ry(D[i])" r="8" :class="['d-dot', { bad: monoViolation && monoViolation.includes(i) }]" />
      </g>

      <!-- 横轴：A 的对象 -->
      <line :x1="X0 - DX / 2" :x2="cx(N - 1) + DX / 2" :y1="AXIS_Y" :y2="AXIS_Y" class="axis" marker-end="url(#ch311k-ah)" />
      <g v-for="a in cols" :key="'ax' + a" class="clickable" @click="toggleI(a)">
        <circle :cx="cx(a)" :cy="AXIS_Y" r="13" :class="['obj', { inI: inI[a] }]" />
        <text :x="cx(a)" :y="AXIS_Y + 4" text-anchor="middle" :class="['obj-t', { inI: inI[a] }]">a{{ a }}</text>
      </g>
      <text :x="cx(N - 1) + DX / 2" :y="AXIS_Y + 32" text-anchor="end" class="axis-name">范畴 A（箭头方向 →，即 ≤）；实心圆 = 子范畴 I</text>
    </svg>

    <div class="legend">
      <span><i class="dot d" />D（只定义在 I 上）</span>
      <span v-if="showRan"><i class="sw ran" />Ran<sub>K</sub>D</span>
      <span v-if="showLan"><i class="sw lan" />Lan<sub>K</sub>D</span>
      <span v-if="showF"><i class="dot f" />候选 F′</span>
      <span v-if="showF"><i class="sw sig" />σ（≤ 即箭头）</span>
    </div>

    <div v-if="monoViolation" class="status bad">
      D 不是单调的：a{{ monoViolation[0] }} ≤ a{{ monoViolation[1] }}，但 D(a{{ monoViolation[0] }}) = {{ vLabel(D[monoViolation[0]]) }} &gt; D(a{{ monoViolation[1] }}) = {{ vLabel(D[monoViolation[1]]) }}。
      它没有把箭头送到箭头，所以不是函子——Kan 扩张无从谈起。请把红点调整一下。
    </div>
    <div v-else class="status info">
      <b>Ran<sub>K</sub>D(a)</b> = min{ D(i) | a ≤ K(i) }：往右看，取所有能到达的 I 中对象的最小值（一个也没有就是 ⊤）。
      <b>Lan<sub>K</sub>D(a)</b> = max{ D(i) | K(i) ≤ a }：往左看，取最大值（没有就是 ⊥）。
      两者在 I 上都与 D 重合；在 I 之外，它们是两种“最好的外推”。
    </div>

    <div v-if="showF && !monoViolation" class="cand">
      <div class="row">
        <span class="lab">检验 F′ 作为：</span>
        <button class="ctfp-btn" :class="{ on: side === 'right' }" @click="side = 'right'">右 Kan 的候选（F′∘K ⇒ D）</button>
        <button class="ctfp-btn" :class="{ on: side === 'left' }" @click="side = 'left'">左 Kan 的候选（D ⇒ F′∘K）</button>
      </div>
      <ul class="checks">
        <li :class="fMonoBad.length ? 'no' : 'yes'">
          F′ 单调（是 A → C 的函子）：
          <template v-if="!fMonoBad.length">是</template>
          <template v-else>否，在 a{{ fMonoBad[0] }} → a{{ fMonoBad[0] + 1 }} 处下降了</template>
        </li>
        <li :class="fCondBad.length ? 'no' : 'yes'">
          <template v-if="side === 'right'">ε′ : F′∘K ⇒ D 存在（每个 i ∈ I 上 F′(i) ≤ D(i)）：</template>
          <template v-else>η′ : D ⇒ F′∘K 存在（每个 i ∈ I 上 D(i) ≤ F′(i)）：</template>
          <template v-if="!fCondBad.length">是</template>
          <template v-else>否，红圈处不满足</template>
        </li>
        <li v-if="fValid" class="yes">
          <template v-if="side === 'right'">于是存在唯一的 σ : F′ ⇒ Ran（处处 F′(a) ≤ Ran(a)，绿色箭头）——F′ 经由 Ran 分解。Ran 是所有右候选中最大的那个。</template>
          <template v-else>于是存在唯一的 σ : Lan ⇒ F′（处处 Lan(a) ≤ F′(a)，绿色箭头）——F′ 经由 Lan 分解。Lan 是所有左候选中最小的那个。</template>
        </li>
      </ul>
      <div class="row">
        <button class="ctfp-btn" @click="copyFrom(ran)">F′ := Ran</button>
        <button class="ctfp-btn" @click="copyFrom(lan)">F′ := Lan</button>
        <button class="ctfp-btn" @click="bump(1)">把 F′ 某处抬高一格</button>
        <button class="ctfp-btn" @click="bump(-1)">把 F′ 某处降低一格</button>
        <button class="ctfp-btn" @click="reset">重置</button>
      </div>
    </div>
    <p class="hint">
      操作：点击下方圆圈把对象放进 / 移出子范畴 I（K 是包含）；在“编辑 D”模式下点击 I 的列设置 D 的值；
      在“编辑候选 F′”模式下点击任意格子设置 F′。试试：令 F′ := Ran，再把它在 I 之外的某处抬高一格——它要么不再单调，要么违反条件。
    </p>
  </div>
</template>

<style scoped>
.kan-poset .row {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 6px;
  margin: 6px 0;
  font-size: 13px;
}
.kan-poset label {
  font-size: 13px;
  color: var(--vp-c-text-2);
  cursor: pointer;
}
.sep {
  width: 10px;
}
.lab {
  color: var(--vp-c-text-2);
}
.canvas {
  width: 100%;
  max-width: 680px;
  height: auto;
  display: block;
  margin: 6px auto 0;
}
.grid {
  stroke: var(--vp-c-divider);
  stroke-width: 1;
}
.grid.rail {
  stroke-dasharray: 4 4;
  stroke: var(--vp-c-text-3);
}
.rlab {
  font-size: 12px;
  fill: var(--vp-c-text-2);
}
.axis-name {
  font-size: 11px;
  fill: var(--vp-c-text-3);
}
.colbg {
  fill: transparent;
}
.colbg.inI {
  fill: var(--vp-c-brand-soft, rgba(59, 111, 216, 0.12));
}
.cell {
  fill: transparent;
  cursor: pointer;
}
.cell:hover {
  fill: rgba(127, 127, 127, 0.12);
}
.cell.disabled {
  cursor: default;
}
.cell.disabled:hover {
  fill: transparent;
}
.ran-line {
  stroke: var(--vp-c-brand-1);
  stroke-width: 4;
  fill: none;
  stroke-linecap: round;
  pointer-events: none;
}
.lan-line {
  stroke: var(--vp-c-warning-1);
  stroke-width: 4;
  fill: none;
  stroke-linecap: round;
  pointer-events: none;
}
.f-line {
  stroke: var(--vp-c-purple-1, #8e5cd9);
  stroke-width: 1.5;
  stroke-dasharray: 4 3;
  fill: none;
  pointer-events: none;
}
.f-dot {
  fill: var(--vp-c-bg);
  stroke: var(--vp-c-purple-1, #8e5cd9);
  stroke-width: 2.5;
  pointer-events: none;
}
.f-dot.bad {
  stroke: var(--vp-c-danger-1);
  stroke-width: 3.5;
}
.d-dot {
  fill: var(--vp-c-text-1);
  pointer-events: none;
}
.d-dot.bad {
  fill: var(--vp-c-danger-1);
}
.sigma {
  stroke: var(--vp-c-success-1, #18794e);
  stroke-width: 2;
  pointer-events: none;
}
.axis {
  stroke: var(--vp-c-text-2);
  stroke-width: 1.5;
}
.obj {
  fill: var(--vp-c-bg);
  stroke: var(--vp-c-text-3);
  stroke-width: 1.5;
}
.obj.inI {
  fill: var(--vp-c-brand-1);
  stroke: var(--vp-c-brand-1);
}
.obj-t {
  font-size: 11px;
  fill: var(--vp-c-text-2);
  pointer-events: none;
}
.obj-t.inI {
  fill: var(--vp-c-bg);
  font-weight: 600;
}
.clickable {
  cursor: pointer;
}
.legend {
  display: flex;
  flex-wrap: wrap;
  gap: 14px;
  justify-content: center;
  font-size: 12px;
  color: var(--vp-c-text-2);
}
.sw {
  display: inline-block;
  width: 18px;
  height: 4px;
  margin-right: 5px;
  vertical-align: middle;
}
.sw.ran {
  background: var(--vp-c-brand-1);
}
.sw.lan {
  background: var(--vp-c-warning-1);
}
.sw.sig {
  background: var(--vp-c-success-1, #18794e);
  height: 2px;
}
.dot {
  display: inline-block;
  width: 10px;
  height: 10px;
  border-radius: 50%;
  margin-right: 5px;
  vertical-align: middle;
}
.dot.d {
  background: var(--vp-c-text-1);
}
.dot.f {
  border: 2px solid var(--vp-c-purple-1, #8e5cd9);
}
.status {
  margin: 10px 0 4px;
  padding: 8px 12px;
  border-radius: 8px;
  font-size: 13px;
  line-height: 1.7;
  border-left: 4px solid;
}
.status.info {
  border-color: var(--vp-c-brand-1);
  background: var(--vp-c-bg);
}
.status.bad {
  border-color: var(--vp-c-danger-1);
  background: var(--vp-c-danger-soft, rgba(200, 50, 50, 0.08));
}
.cand {
  margin-top: 8px;
}
.checks {
  margin: 4px 0;
  padding-left: 20px;
  font-size: 13px;
}
.checks li.yes::marker {
  content: '✓  ';
  color: var(--vp-c-success-1, #18794e);
}
.checks li.no::marker {
  content: '✗  ';
  color: var(--vp-c-danger-1);
}
.hint {
  font-size: 12px;
  color: var(--vp-c-text-3);
  margin: 6px 0 0;
}
</style>
