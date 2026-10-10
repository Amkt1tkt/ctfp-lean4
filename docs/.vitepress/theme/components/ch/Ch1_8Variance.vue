<script setup>
import { ref, computed, onBeforeUnmount } from 'vue'

const examples = [
  {
    name: '奇偶性：Nat → 奇偶',
    aType: 'Nat', bType: '奇偶', rType: '颜色',
    as: ['1', '2', '3', '4'],
    bs: ['偶', '奇'],
    f: { '1': '奇', '2': '偶', '3': '奇', '4': '偶' },
    fName: 'parity',
    list: ['3', '4', '1'],
    k: { '偶': '红', '奇': '蓝' },
  },
  {
    name: '长度：String → Nat',
    aType: 'String', bType: 'Nat', rType: '评价',
    as: ['"ok"', '"cat"', '"lean"', '"hi"'],
    bs: ['2', '3', '4'],
    f: { '"ok"': '2', '"cat"': '3', '"lean"': '4', '"hi"': '2' },
    fName: 'length',
    list: ['"lean"', '"ok"', '"cat"'],
    k: { '2': '短', '3': '中', '4': '长' },
  },
]

const ex = ref(0)
const E = computed(() => examples[ex.value])
const mode = ref('co') // 'co' | 'contra'
const step = ref(-1) // 当前处理到第几个元素；-1 表示未开始
const phase = ref(0) // 每个元素内部的小阶段
const playing = ref(false)
let timer = 0

const W = 660
const colA = 150
const colB = 510
const rowY = (i, n) => 62 + i * 30 + (4 - n) * 15

const aPos = computed(() => E.value.as.map((x, i) => ({ x: colA, y: rowY(i, E.value.as.length), v: x })))
const bPos = computed(() => E.value.bs.map((x, i) => ({ x: colB, y: rowY(i, E.value.bs.length), v: x })))
const edges = computed(() =>
  aPos.value.map((p) => {
    const q = bPos.value.find((b) => b.v === E.value.f[p.v])
    return { from: p, to: q, a: p.v, b: q.v }
  }),
)

// 当前高亮的 f 边（哪个 a 元素）
const litA = computed(() => {
  if (step.value < 0) return null
  if (mode.value === 'co') return E.value.list[step.value] ?? null
  return E.value.as[step.value] ?? null
})

const coOut = computed(() => {
  const out = []
  E.value.list.forEach((x, i) => {
    if (i < step.value || (i === step.value && phase.value >= 1)) out.push(E.value.f[x])
  })
  return out
})

const contraRows = computed(() =>
  E.value.as.map((x, i) => {
    const done = i < step.value || (i === step.value && phase.value >= 2)
    return { a: x, r: done ? E.value.k[E.value.f[x]] : '?' }
  }),
)

const litB = computed(() => {
  if (mode.value !== 'contra' || step.value < 0) return null
  const a = E.value.as[step.value]
  if (!a || phase.value < 1) return null
  return E.value.f[a]
})

const total = computed(() => (mode.value === 'co' ? E.value.list.length : E.value.as.length))
const phases = computed(() => (mode.value === 'co' ? 2 : 3))

const narration = computed(() => {
  const e = E.value
  if (step.value < 0) {
    return mode.value === 'co'
      ? `协变：List 里装的是 ${e.aType} 值。map ${e.fName} 把每个值沿着 ${e.fName} 往右送，得到 List ${e.bType}。`
      : `逆变：右边是一个“消费 ${e.bType}”的函数 k : ${e.bType} → ${e.rType}。要得到“消费 ${e.aType}”的函数，只能先用 ${e.fName} 把 ${e.aType} 变成 ${e.bType}，再交给 k。`
  }
  if (step.value >= total.value) {
    return mode.value === 'co'
      ? `完成：f 指向右边，map f 也指向右边——同向，所以叫“协变”。`
      : `完成：f 指向右边，contramap f 却是从右边的 (${e.bType} → ${e.rType}) 造出左边的 (${e.aType} → ${e.rType})——反向，所以叫“逆变”。`
  }
  if (mode.value === 'co') {
    const x = e.list[step.value]
    return `取出 ${x}，沿 ${e.fName} 走到 ${e.f[x]}，放进结果列表。`
  }
  const x = e.as[step.value]
  const b = e.f[x]
  if (phase.value === 0) return `问：新函数在 ${x} 处的值是什么？`
  if (phase.value === 1) return `先沿 ${e.fName} 走：${x} ↦ ${b}。`
  return `再查 k 的表：${b} ↦ ${e.k[b]}。所以 (k ∘ ${e.fName}) ${x} = ${e.k[b]}。`
})

function stop() {
  clearTimeout(timer)
  playing.value = false
}
function reset() {
  stop()
  step.value = -1
  phase.value = 0
}
function tick() {
  if (step.value < 0) {
    step.value = 0
    phase.value = 0
  } else if (phase.value + 1 < phases.value) {
    phase.value++
  } else {
    step.value++
    phase.value = 0
  }
  if (step.value >= total.value) {
    playing.value = false
    return
  }
  timer = setTimeout(tick, 900)
}
function play(m) {
  reset()
  mode.value = m
  playing.value = true
  timer = setTimeout(tick, 300)
}
function pick(i) {
  ex.value = i
  reset()
}
onBeforeUnmount(stop)

const done = computed(() => step.value >= total.value)
const liftDir = computed(() => (mode.value === 'co' ? 'right' : 'left'))
</script>

<template>
  <div class="ctfp-widget var-widget">
    <div class="ctfp-widget-title">协变 vs 逆变：被提升的箭头往哪边走？</div>
    <div class="controls">
      <span class="lbl">选一个 f：</span>
      <button v-for="(e, i) in examples" :key="i" class="ctfp-btn" :class="{ on: ex === i }" @click="pick(i)">{{ e.name }}</button>
    </div>
    <div class="controls">
      <button class="ctfp-btn" :class="{ on: mode === 'co' }" @click="play('co')">▶ 协变：List.map f</button>
      <button class="ctfp-btn" :class="{ on: mode === 'contra' }" @click="play('contra')">▶ 逆变：contramap f</button>
      <button class="ctfp-btn" @click="reset">重置</button>
    </div>

    <svg :viewBox="`0 0 ${W} 400`" class="stage" role="img">
      <defs>
        <marker id="v-ah" viewBox="0 0 10 10" refX="8.5" refY="5" markerWidth="9" markerHeight="9" orient="auto-start-reverse">
          <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
        </marker>
      </defs>

      <!-- 上半：基础箭头 f : a → b -->
      <text :x="colA" y="24" class="hdr" text-anchor="middle">{{ E.aType }}（a）</text>
      <text :x="colB" y="24" class="hdr" text-anchor="middle">{{ E.bType }}（b）</text>
      <path :d="`M${colA + 70},20 L${colB - 70},20`" class="big base" marker-end="url(#v-ah)" />
      <text :x="W / 2" y="14" class="lab base-t" text-anchor="middle">{{ E.fName }} : a → b</text>

      <g v-for="e in edges" :key="e.a">
        <path
          :d="`M${e.from.x + 34},${e.from.y} L${e.to.x - 34},${e.to.y}`"
          :class="['edge', { lit: litA === e.a }]"
          marker-end="url(#v-ah)"
        />
      </g>
      <g v-for="p in aPos" :key="'a' + p.v">
        <rect :x="p.x - 32" :y="p.y - 12" width="64" height="24" rx="12" :class="['chip', { lit: litA === p.v }]" />
        <text :x="p.x" :y="p.y + 5" text-anchor="middle" class="ct">{{ p.v }}</text>
      </g>
      <g v-for="p in bPos" :key="'b' + p.v">
        <rect :x="p.x - 32" :y="p.y - 12" width="64" height="24" rx="12" :class="['chip', { lit: litB === p.v || (mode === 'co' && litA && E.f[litA] === p.v && phase >= 1) }]" />
        <text :x="p.x" :y="p.y + 5" text-anchor="middle" class="ct">{{ p.v }}</text>
      </g>

      <line x1="20" y1="196" :x2="W - 20" y2="196" class="sep" />

      <!-- 下半：协变 -->
      <g v-if="mode === 'co'">
        <rect :x="colA - 120" y="232" width="240" height="120" rx="10" class="box" />
        <rect :x="colB - 120" y="232" width="240" height="120" rx="10" class="box" />
        <text :x="colA" y="254" text-anchor="middle" class="hdr">List {{ E.aType }}</text>
        <text :x="colB" y="254" text-anchor="middle" class="hdr">List {{ E.bType }}</text>
        <g v-for="(x, i) in E.list" :key="'l' + i">
          <rect :x="colA - 105 + i * 72" y="280" width="62" height="28" rx="6" :class="['chip', { lit: step === i, used: step > i }]" />
          <text :x="colA - 74 + i * 72" y="299" text-anchor="middle" class="ct">{{ x }}</text>
        </g>
        <g v-for="(y, i) in coOut" :key="'o' + i">
          <rect :x="colB - 105 + i * 72" y="280" width="62" height="28" rx="6" class="chip out" />
          <text :x="colB - 74 + i * 72" y="299" text-anchor="middle" class="ct">{{ y }}</text>
        </g>
        <text :x="colA" y="336" text-anchor="middle" class="code">[{{ E.list.join(', ') }}]</text>
        <text :x="colB" y="336" text-anchor="middle" class="code">[{{ coOut.join(', ') }}]</text>
      </g>

      <!-- 下半：逆变 -->
      <g v-else>
        <rect :x="colA - 120" y="214" width="240" height="176" rx="10" class="box" />
        <rect :x="colB - 120" y="214" width="240" height="176" rx="10" class="box" />
        <text :x="colA" y="232" text-anchor="middle" class="hdr">{{ E.aType }} → {{ E.rType }}</text>
        <text :x="colA" y="247" text-anchor="middle" class="code">k ∘ {{ E.fName }}</text>
        <text :x="colB" y="232" text-anchor="middle" class="hdr">{{ E.bType }} → {{ E.rType }}</text>
        <text :x="colB" y="247" text-anchor="middle" class="code">k</text>
        <g v-for="(row, i) in contraRows" :key="'ca' + i">
          <rect :x="colA - 90" :y="255 + i * 32" width="180" height="27" rx="6" :class="['row', { lit: step === i && !done }]" />
          <text :x="colA - 40" :y="273 + i * 32" text-anchor="middle" class="ct">{{ row.a }}</text>
          <text :x="colA" :y="273 + i * 32" text-anchor="middle" class="ct dim">↦</text>
          <text :x="colA + 40" :y="273 + i * 32" text-anchor="middle" :class="['ct', { q: row.r === '?' }]">{{ row.r }}</text>
        </g>
        <g v-for="(b, i) in E.bs" :key="'cb' + i">
          <rect :x="colB - 90" :y="255 + i * 32" width="180" height="27" rx="6" :class="['row', { lit: litB === b && phase >= 1 && !done }]" />
          <text :x="colB - 40" :y="273 + i * 32" text-anchor="middle" class="ct">{{ b }}</text>
          <text :x="colB" :y="273 + i * 32" text-anchor="middle" class="ct dim">↦</text>
          <text :x="colB + 40" :y="273 + i * 32" text-anchor="middle" class="ct">{{ E.k[b] }}</text>
        </g>
      </g>

      <!-- 被提升的箭头 -->
      <path
        v-if="liftDir === 'right'"
        :d="`M${colA + 128},300 L${colB - 128},300`"
        :class="['big', 'lift-co', { anim: playing }]"
        marker-end="url(#v-ah)"
      />
      <path
        v-else
        :d="`M${colB - 128},300 L${colA + 128},300`"
        :class="['big', 'lift-contra', { anim: playing }]"
        marker-end="url(#v-ah)"
      />
      <text :x="W / 2" y="288" text-anchor="middle" :class="['lab', liftDir === 'right' ? 'co-t' : 'contra-t']">
        {{ mode === 'co' ? 'map ' + E.fName : 'contramap ' + E.fName }}
      </text>
      <text :x="W / 2" y="324" text-anchor="middle" class="lab small">
        {{ mode === 'co' ? '同向 →' : '反向 ←' }}
      </text>
    </svg>

    <p class="narr">{{ narration }}</p>
    <p class="sig">
      <code v-if="mode === 'co'">List.map {{ E.fName }} : List {{ E.aType }} → List {{ E.bType }}</code>
      <code v-else>contramap {{ E.fName }} : ({{ E.bType }} → {{ E.rType }}) → ({{ E.aType }} → {{ E.rType }})</code>
    </p>
    <p class="hint">提示：上下两排的左边都对应 a，右边都对应 b。看被提升的粗箭头和上面的 f 是不是同一个方向。</p>
  </div>
</template>

<style scoped>
.var-widget { max-width: 100%; }
.controls { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; margin-bottom: 8px; }
.lbl { font-size: 13px; color: var(--vp-c-text-2); }
.stage { width: 100%; max-width: 660px; display: block; margin: 6px auto; }
.hdr { font-size: 13px; font-weight: 600; fill: var(--vp-c-text-1); }
.lab { font-size: 14px; font-weight: 600; fill: var(--vp-c-text-2); font-family: var(--vp-font-family-mono); }
.lab.small { font-size: 12px; font-family: inherit; }
.base-t { fill: var(--vp-c-text-2); }
.co-t { fill: var(--vp-c-success-1, #18794e); }
.contra-t { fill: var(--vp-c-warning-1, #c77d00); }
.big { stroke-width: 4; fill: none; }
.base { stroke: var(--vp-c-text-3); stroke-width: 2.5; }
.lift-co { stroke: var(--vp-c-success-1, #18794e); }
.lift-contra { stroke: var(--vp-c-warning-1, #c77d00); }
.big.anim { stroke-dasharray: 10 7; animation: flow 0.8s linear infinite; }
@keyframes flow { to { stroke-dashoffset: -17; } }
.edge { stroke: var(--vp-c-text-3); stroke-width: 1.4; fill: none; transition: all 0.25s; }
.edge.lit { stroke: var(--vp-c-brand-1); stroke-width: 3; }
.chip { fill: var(--vp-c-bg); stroke: var(--vp-c-divider); stroke-width: 1.4; transition: all 0.25s; }
.chip.lit { stroke: var(--vp-c-brand-1); stroke-width: 2.6; fill: var(--vp-c-brand-soft); }
.chip.used { opacity: 0.55; }
.chip.out { stroke: var(--vp-c-success-1, #18794e); }
.row { fill: var(--vp-c-bg); stroke: var(--vp-c-divider); transition: all 0.25s; }
.row.lit { stroke: var(--vp-c-brand-1); stroke-width: 2.4; fill: var(--vp-c-brand-soft); }
.ct { font-size: 13px; fill: var(--vp-c-text-1); font-family: var(--vp-font-family-mono); }
.ct.dim { fill: var(--vp-c-text-3); }
.ct.q { fill: var(--vp-c-text-3); }
.code { font-size: 12px; fill: var(--vp-c-text-2); font-family: var(--vp-font-family-mono); }
.box { fill: var(--vp-c-bg-soft); stroke: var(--vp-c-divider); }
.sep { stroke: var(--vp-c-divider); stroke-dasharray: 4 4; }
.narr { margin: 6px 0 2px; font-size: 14px; min-height: 2.6em; }
.sig { margin: 0; font-size: 13px; }
.hint { margin: 4px 0 0; font-size: 12px; color: var(--vp-c-text-3); }
</style>
