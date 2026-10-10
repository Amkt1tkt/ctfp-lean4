<script setup>
import { ref, computed, watch, onBeforeUnmount } from 'vue'

const fmtList = (xs) => '[' + xs.join(', ') + ']'
const S = (i) => 's' + String(i).replace(/\d/g, (d) => '₀₁₂₃₄₅₆₇₈₉'[d])

// 每条语句：code（do 块中的写法）、explicit（bind 替你写的显式状态传递代码）、run（状态 × 环境 → 新状态、新绑定、值）
const PROGRAMS = [
  {
    name: '倍增计数器',
    type: 'StateM Nat String',
    initLabel: '初始状态 s₀（自然数）',
    init: '5',
    parse: (t) => { const n = parseInt(t, 10); return Number.isFinite(n) && n >= 0 ? n : null },
    show: (s) => String(s),
    lines: [
      { code: 'let a ← get', explicit: (i) => `let (a, ${S(i + 1)}) := (${S(i)}, ${S(i)})`, run: (s, env) => ({ s, bind: ['a', s] }) },
      { code: 'set (a * 2)', explicit: (i) => `let ((), ${S(i + 1)}) := ((), a * 2)`, run: (s, env) => ({ s: env.a * 2 }) },
      { code: 'modify (· + 3)', explicit: (i) => `let ((), ${S(i + 1)}) := ((), ${S(i)} + 3)`, run: (s) => ({ s: s + 3 }) },
      { code: 'let b ← get', explicit: (i) => `let (b, ${S(i + 1)}) := (${S(i)}, ${S(i)})`, run: (s) => ({ s, bind: ['b', s] }) },
      { code: 'return s!"{a} → {b}"', explicit: (i) => `(s!"{a} → {b}", ${S(i)})`, run: (s, env) => ({ s, value: `"${env.a} → ${env.b}"` }) },
    ],
  },
  {
    name: '栈机',
    type: 'StateM (List Nat) Nat',
    initLabel: '初始栈 s₀（用逗号分隔，栈顶在左）',
    init: '',
    parse: (t) => {
      const parts = t.split(',').map((x) => x.trim()).filter((x) => x !== '')
      const ns = parts.map((x) => parseInt(x, 10))
      return ns.every((n) => Number.isFinite(n) && n >= 0) ? ns : null
    },
    show: fmtList,
    lines: [
      { code: 'push 1', explicit: (i) => `let ((), ${S(i + 1)}) := ((), 1 :: ${S(i)})`, run: (s) => ({ s: [1, ...s] }) },
      { code: 'push 2', explicit: (i) => `let ((), ${S(i + 1)}) := ((), 2 :: ${S(i)})`, run: (s) => ({ s: [2, ...s] }) },
      { code: 'let x ← pop', explicit: (i) => `let (x, ${S(i + 1)}) := (${S(i)}.headD 0, ${S(i)}.tail)`, run: (s) => ({ s: s.slice(1), bind: ['x', s.length ? s[0] : 0] }) },
      { code: 'push (x * 10)', explicit: (i) => `let ((), ${S(i + 1)}) := ((), (x * 10) :: ${S(i)})`, run: (s, env) => ({ s: [env.x * 10, ...s] }) },
      { code: 'let y ← pop', explicit: (i) => `let (y, ${S(i + 1)}) := (${S(i)}.headD 0, ${S(i)}.tail)`, run: (s) => ({ s: s.slice(1), bind: ['y', s.length ? s[0] : 0] }) },
      { code: 'return x + y', explicit: (i) => `(x + y, ${S(i)})`, run: (s, env) => ({ s, value: String(env.x + env.y) }) },
    ],
  },
  {
    name: '两次取号',
    type: 'StateM Nat Nat',
    initLabel: '初始状态 s₀（自然数）',
    init: '10',
    parse: (t) => { const n = parseInt(t, 10); return Number.isFinite(n) && n >= 0 ? n : null },
    show: (s) => String(s),
    note: 'counter = do let n ← get; set (n + 1); return n',
    lines: [
      { code: 'let a ← counter', explicit: (i) => `let (a, ${S(i + 1)}) := (${S(i)}, ${S(i)} + 1)`, run: (s) => ({ s: s + 1, bind: ['a', s] }) },
      { code: 'let b ← counter', explicit: (i) => `let (b, ${S(i + 1)}) := (${S(i)}, ${S(i)} + 1)`, run: (s) => ({ s: s + 1, bind: ['b', s] }) },
      { code: 'return a + b', explicit: (i) => `(a + b, ${S(i)})`, run: (s, env) => ({ s, value: String(env.a + env.b) }) },
    ],
  },
]

const pi = ref(0)
const prog = computed(() => PROGRAMS[pi.value])
const initText = ref(PROGRAMS[0].init)
const step = ref(0)
const explicit = ref(false)
const playing = ref(false)
let timer = null

watch(pi, () => {
  initText.value = prog.value.init
  step.value = 0
  stop()
})
watch(initText, () => (step.value = 0))

const init = computed(() => prog.value.parse(initText.value))

const trace = computed(() => {
  if (init.value === null) return null
  let s = init.value
  const env = {}
  const rows = []
  let value = null
  for (const l of prog.value.lines) {
    const r = l.run(s, env)
    const row = { sIn: s, sOut: r.s, bind: r.bind || null }
    if (r.bind) env[r.bind[0]] = r.bind[1]
    if (r.value !== undefined) value = r.value
    row.env = { ...env }
    rows.push(row)
    s = r.s
  }
  return { rows, value, final: s }
})

const n = computed(() => prog.value.lines.length)
const envNow = computed(() => (step.value === 0 || !trace.value ? {} : trace.value.rows[step.value - 1].env))

function stop() {
  playing.value = false
  if (timer) clearInterval(timer)
  timer = null
}
function play() {
  if (playing.value) return stop()
  if (step.value >= n.value) step.value = 0
  playing.value = true
  timer = setInterval(() => {
    if (step.value >= n.value) stop()
    else step.value++
  }, 900)
}
onBeforeUnmount(stop)
</script>

<template>
  <div class="ctfp-widget sp">
    <div class="ctfp-widget-title">bind 流水线：State 单子里那条看不见的管道</div>
    <div class="row">
      <button v-for="(p, i) in PROGRAMS" :key="i" class="ctfp-btn" :class="{ on: pi === i }" @click="pi = i">{{ p.name }}</button>
    </div>
    <div class="row small">
      <label>{{ prog.initLabel }} <input v-model="initText" class="txt" /></label>
      <label><input type="checkbox" v-model="explicit" /> 显示隐藏的管道（bind 替你写的代码）</label>
    </div>
    <div v-if="prog.note" class="row small mono dim">{{ prog.note }}</div>

    <div v-if="!trace" class="err">无法解析初始状态。</div>
    <div v-else class="grid">
      <div class="hdr">do 块（{{ prog.type }}）</div>
      <div class="hdr">状态管道</div>

      <div class="code mono head">{{ explicit ? 'fun s₀ =>' : 'do' }}</div>
      <div class="pipe-cell">
        <span class="st on">s₀ = {{ prog.show(trace.rows[0].sIn) }}</span>
      </div>

      <template v-for="(l, i) in prog.lines" :key="pi + '-' + i">
        <div class="code mono" :class="{ cur: step === i + 1, done: step > i, todo: step <= i }">
          <span class="ln">{{ i + 1 }}</span>
          <span v-if="!explicit">{{ l.code }}</span>
          <span v-else class="exp"><span>{{ l.explicit(i) }}</span><span class="was">-- {{ l.code }}</span></span>
        </div>
        <div class="pipe-cell" :class="{ cur: step === i + 1 }">
          <div class="pipe" :class="{ flowing: step > i }">
            <span v-if="step === i + 1" class="token" />
          </div>
          <span v-if="step > i" class="st on">{{ S(i + 1) }} = {{ prog.show(trace.rows[i].sOut) }}</span>
          <span v-else class="st">{{ S(i + 1) }} = ?</span>
          <span v-if="step > i && trace.rows[i].bind" class="bindv">{{ trace.rows[i].bind[0] }} = {{ trace.rows[i].bind[1] }}</span>
          <span v-if="step > i && trace.rows[i].sOut === trace.rows[i].sIn" class="same">（状态未变）</span>
        </div>
      </template>
    </div>

    <div class="row">
      <button class="ctfp-btn" :disabled="step === 0" @click="step--; stop()">上一步</button>
      <button class="ctfp-btn" :disabled="step >= n" @click="step++; stop()">下一步</button>
      <button class="ctfp-btn" @click="play">{{ playing ? '暂停' : '自动播放' }}</button>
      <button class="ctfp-btn" @click="step = 0; stop()">重置</button>
    </div>
    <div v-if="trace" class="foot small">
      <div><b>可见的变量：</b>
        <span v-if="Object.keys(envNow).length === 0" class="dim">（无）</span>
        <span v-for="(v, k) in envNow" :key="k" class="mono chip">{{ k }} = {{ v }}</span>
      </div>
      <div v-if="step >= n"><b>.run s₀ 的结果：</b><span class="mono">({{ trace.value }}, {{ prog.show(trace.final) }})</span></div>
      <div class="dim">
        你写的 do 块里从未出现过 s₀、s₁、s₂……：它们由 State 的 bind 在幕后逐行传递。勾选“显示隐藏的管道”就能看到这些代码。
      </div>
    </div>
  </div>
</template>

<style scoped>
.sp, .sp * { font-variant-ligatures: none; font-feature-settings: "liga" 0, "calt" 0; }
.row { display: flex; flex-wrap: wrap; gap: 8px 14px; align-items: center; margin: 8px 0; }
.small { font-size: 13px; }
.mono { font-family: var(--vp-font-family-mono); }
.dim { color: var(--vp-c-text-3); }
.txt { border: 1px solid var(--vp-c-divider); border-radius: 6px; padding: 2px 8px; background: var(--vp-c-bg); color: var(--vp-c-text-1); width: 110px; font-family: var(--vp-font-family-mono); }
.err { color: var(--vp-c-danger-1); font-size: 13px; }
.grid { display: grid; grid-template-columns: minmax(0, 1.25fr) minmax(0, 1fr); column-gap: 14px; margin: 10px 0; background: var(--vp-c-bg); border: 1px solid var(--vp-c-divider); border-radius: 10px; padding: 10px 12px; overflow-x: auto; }
.hdr { font-size: 12px; color: var(--vp-c-text-2); padding-bottom: 6px; border-bottom: 1px solid var(--vp-c-divider); margin-bottom: 4px; }
.code { font-size: 13px; padding: 6px 8px; border-radius: 6px; white-space: nowrap; overflow: hidden; display: flex; align-items: center; transition: background 0.3s, opacity 0.3s; min-height: 44px; }
.code.head { min-height: 30px; color: var(--vp-c-brand-1); font-weight: 600; }
.code.todo { opacity: 0.55; }
.code.cur { background: color-mix(in srgb, var(--vp-c-brand-1) 15%, transparent); opacity: 1; }
.ln { flex: none; display: inline-block; width: 1.6em; color: var(--vp-c-text-3); font-size: 11px; }
.exp { color: var(--vp-c-text-1); display: flex; flex-direction: column; min-width: 0; }
.was { color: var(--vp-c-text-3); font-size: 11px; line-height: 1.3; }
.pipe-cell { overflow: visible; display: flex; align-items: center; gap: 8px; flex-wrap: wrap; font-size: 13px; position: relative; padding-left: 26px; min-height: 30px; }
.pipe { z-index: 0; position: absolute; left: 8px; top: -50%; bottom: 50%; width: 6px; border-radius: 3px; background: var(--vp-c-divider); }
.pipe.flowing { background: color-mix(in srgb, #16a34a 55%, transparent); }
.token { position: absolute; z-index: 2; left: -1px; width: 8px; height: 8px; border-radius: 50%; background: #16a34a; box-shadow: 0 0 6px #16a34a; animation: flow 0.9s linear infinite; }
@keyframes flow { from { top: -8px; } to { top: 100%; } }
.st { position: relative; z-index: 1; background: var(--vp-c-bg); font-family: var(--vp-font-family-mono); padding: 1px 8px; border-radius: 999px; border: 1px dashed var(--vp-c-divider); color: var(--vp-c-text-3); }
.st.on { border: 1px solid #16a34a; color: var(--vp-c-text-1); background: color-mix(in srgb, #16a34a 10%, var(--vp-c-bg)); }
.bindv { font-family: var(--vp-font-family-mono); color: var(--vp-c-brand-1); }
.same { color: var(--vp-c-text-3); font-size: 12px; }
.foot > div { margin: 4px 0; line-height: 1.7; }
.chip { display: inline-block; margin: 0 6px 0 0; padding: 0 8px; border-radius: 999px; background: color-mix(in srgb, var(--vp-c-brand-1) 12%, transparent); }
button:disabled { opacity: 0.4; cursor: default; }
</style>
