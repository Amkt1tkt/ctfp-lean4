<script setup>
import { ref, computed, watch } from 'vue'

const mode = ref('writer')

// ---------- Writer：值 + 日志 ----------
const WRITER_FNS = {
  upCase: { from: 'String', to: 'String', msg: 'upCase ', run: (s) => s.toUpperCase() },
  reverse: { from: 'String', to: 'String', msg: 'reverse ', run: (s) => Array.from(s).reverse().join('') },
  toWords: { from: 'String', to: 'List String', msg: 'toWords ', run: (s) => s.split(/\s+/).filter((w) => w !== '') },
  count: { from: 'List String', to: 'Nat', msg: 'count ', run: (xs) => xs.length },
  isEven: { from: 'Nat', to: 'Bool', msg: 'isEven ', run: (n) => n % 2 === 0 },
  negate: { from: 'Bool', to: 'Bool', msg: 'Not so! ', run: (b) => !b },
  ret: { from: '*', to: '*', msg: '', run: (x) => x },
}

// ---------- Option：偏函数 ----------
const OPTION_FNS = {
  safeReciprocal: { note: 'x ≠ 0', run: (x) => (x !== 0 ? 1 / x : null) },
  safeRoot: { note: 'x ≥ 0', run: (x) => (x >= 0 ? Math.sqrt(x) : null) },
  minusOne: { note: '总是成功', run: (x) => x - 1 },
  safeLog: { note: 'x > 0', run: (x) => (x > 0 ? Math.log(x) : null) },
  ret: { note: '= some', run: (x) => x },
}

const writerInput = ref('hello kleisli world')
const optionInput = ref('4')
const writerChain = ref(['upCase', 'toWords', 'count', 'isEven', 'negate'])
const optionChain = ref(['safeReciprocal', 'safeRoot'])
const step = ref(0)

const fns = computed(() => (mode.value === 'writer' ? WRITER_FNS : OPTION_FNS))
const chain = computed(() => (mode.value === 'writer' ? writerChain.value : optionChain.value))

function outType(ch) {
  let t = 'String'
  for (const id of ch) {
    const f = WRITER_FNS[id]
    if (f.to !== '*') t = f.to
  }
  return t
}

const currentType = computed(() => (mode.value === 'writer' ? outType(writerChain.value) : 'Float'))

function canAppend(id) {
  if (mode.value === 'option') return true
  const f = WRITER_FNS[id]
  return f.from === '*' || f.from === currentType.value
}

function append(id) {
  if (!canAppend(id) || chain.value.length >= 8) return
  chain.value.push(id)
  step.value = 0
}
function removeLast() {
  chain.value.pop()
  step.value = 0
}
function clearChain() {
  chain.value.splice(0, chain.value.length)
  step.value = 0
}
function reset() {
  step.value = 0
}
function next() {
  if (step.value < chain.value.length) step.value++
}
function runAll() {
  step.value = chain.value.length
}

watch([mode, writerInput, optionInput], () => (step.value = 0))

const parsedNumber = computed(() => {
  const v = Number(optionInput.value)
  return Number.isFinite(v) ? v : null
})

// 逐步计算所有中间结果
const trace = computed(() => {
  const rows = []
  if (mode.value === 'writer') {
    let val = writerInput.value
    let log = ''
    for (const id of writerChain.value) {
      const f = WRITER_FNS[id]
      const y = f.run(val)
      rows.push({ id, input: val, out: y, msg: f.msg, prevLog: log, log: log + f.msg })
      val = y
      log = log + f.msg
    }
    return { rows, final: { val, log } }
  }
  let val = parsedNumber.value
  let failedAt = val === null ? -1 : null
  optionChain.value.forEach((id, i) => {
    if (val === null) {
      rows.push({ id, skipped: true })
      return
    }
    const y = OPTION_FNS[id].run(val)
    rows.push({ id, input: val, out: y })
    if (y === null && failedAt === null) failedAt = i
    val = y
  })
  return { rows, final: { val }, failedAt }
})

const shown = computed(() => trace.value.rows.slice(0, step.value))

const state = computed(() => {
  if (step.value === 0) {
    return mode.value === 'writer'
      ? { val: writerInput.value, log: '', fresh: '' }
      : { val: parsedNumber.value }
  }
  const r = trace.value.rows[step.value - 1]
  if (mode.value === 'writer') return { val: r.out, log: r.prevLog, fresh: r.msg }
  let v = parsedNumber.value
  for (let i = 0; i < step.value; i++) {
    const row = trace.value.rows[i]
    if (row.skipped) { v = null; break }
    v = row.out
  }
  return { val: v }
})

function show(v) {
  if (Array.isArray(v)) return '[' + v.map((x) => JSON.stringify(x)).join(', ') + ']'
  if (typeof v === 'string') return JSON.stringify(v)
  if (typeof v === 'number') return Number.isInteger(v) ? String(v) : String(Math.round(v * 10000) / 10000)
  return String(v)
}
function showOpt(v) {
  return v === null ? 'none' : `some ${show(v)}`
}

const leanExpr = computed(() => (chain.value.length ? chain.value.join(' >=> ') : 'ret'))
const signature = computed(() =>
  mode.value === 'writer' ? `String → Writer (${currentType.value})` : 'Float → Option Float',
)
const done = computed(() => step.value >= chain.value.length)
</script>

<template>
  <div class="ctfp-widget kl">
    <div class="ctfp-widget-title">Kleisli 复合逐步执行器</div>
    <div class="kl-tabs">
      <button :class="['ctfp-btn', { on: mode === 'writer' }]" @click="mode = 'writer'">Writer：值 + 日志</button>
      <button :class="['ctfp-btn', { on: mode === 'option' }]" @click="mode = 'option'">Option：偏函数</button>
    </div>
    <p class="kl-hint" v-if="mode === 'writer'">
      点击下方函数把它接到链条末尾（只有输入类型与当前输出类型吻合的函数才能接上——这就是“可复合”）。然后单步执行，观察值如何传递、日志如何拼接。
    </p>
    <p class="kl-hint" v-else>
      每个函数都可能失败（返回 <code>none</code>）。一旦某一步失败，后面的函数根本不会被调用——复合在幕后替你处理了失败。
    </p>

    <div class="kl-row">
      <label>输入：</label>
      <input v-if="mode === 'writer'" v-model="writerInput" class="kl-input" spellcheck="false" />
      <input v-else v-model="optionInput" class="kl-input kl-num" inputmode="decimal" />
      <span class="kl-type">{{ mode === 'writer' ? 'String' : 'Float' }}</span>
    </div>

    <div class="kl-palette">
      <button
        v-for="(f, id) in fns" :key="id"
        :class="['kl-fn', { disabled: !canAppend(id) }]"
        :disabled="!canAppend(id)"
        :title="mode === 'writer' ? `${id} : ${f.from === '*' ? 'α' : f.from} → Writer ${f.to === '*' ? 'α' : f.to}` : `${id}（${f.note}）`"
        @click="append(id)"
      >
        <code>{{ id }}</code>
        <span class="kl-sig" v-if="mode === 'writer'">{{ f.from === '*' ? 'α' : f.from }} → Writer {{ f.to === '*' ? 'α' : f.to }}</span>
        <span class="kl-sig" v-else>Float → Option Float · {{ f.note }}</span>
      </button>
    </div>

    <div class="kl-chain">
      <span class="kl-chain-label">链条：</span>
      <code class="kl-expr">{{ leanExpr }}</code>
      <span class="kl-chain-sig">: {{ signature }}</span>
    </div>

    <div class="kl-controls">
      <button class="ctfp-btn" :disabled="done" @click="next">单步 ▶</button>
      <button class="ctfp-btn" :disabled="done" @click="runAll">全部执行</button>
      <button class="ctfp-btn" @click="reset">重置</button>
      <button class="ctfp-btn" :disabled="!chain.length" @click="removeLast">撤销最后一个</button>
      <button class="ctfp-btn" :disabled="!chain.length" @click="clearChain">清空链条</button>
      <span class="kl-progress">第 {{ step }} / {{ chain.length }} 步</span>
    </div>

    <!-- 当前状态 -->
    <div class="kl-state">
      <div class="kl-state-label">{{ done ? '最终结果' : '当前状态' }}</div>
      <div v-if="mode === 'writer'" class="kl-pair">
        <span class="kl-paren">(</span>
        <span class="kl-val">{{ show(state.val) }}</span>
        <span class="kl-paren">,</span>
        <span class="kl-log">"<span class="kl-old">{{ state.log }}</span><span class="kl-new">{{ state.fresh }}</span>"</span>
        <span class="kl-paren">)</span>
      </div>
      <div v-else class="kl-pair">
        <span :class="['kl-val', { 'kl-none': state.val === null }]">{{ showOpt(state.val) }}</span>
      </div>
    </div>

    <!-- 执行轨迹 -->
    <ol class="kl-trace">
      <li v-for="(r, i) in shown" :key="i" :class="{ latest: i === step - 1, skipped: r.skipped }">
        <template v-if="mode === 'writer'">
          <div><code>{{ r.id }}</code> 收到值 <code>{{ show(r.input) }}</code>，返回 <code>({{ show(r.out) }}, {{ JSON.stringify(r.msg) }})</code></div>
          <div class="kl-sub">
            鱼把值 <code>{{ show(r.out) }}</code> 交给下一步，并拼接日志：
            <code>{{ JSON.stringify(r.prevLog) }} ++ {{ JSON.stringify(r.msg) }} = {{ JSON.stringify(r.log) }}</code>
            <span v-if="r.id === 'ret'" class="kl-note">（ret 只贡献空串：它是单位元）</span>
          </div>
        </template>
        <template v-else>
          <div v-if="r.skipped"><code>{{ r.id }}</code> 被跳过：前面已经得到 <code>none</code>，整个复合短路</div>
          <div v-else>
            <code>{{ r.id }}</code> 收到 <code>{{ show(r.input) }}</code>，返回
            <code :class="{ 'kl-none': r.out === null }">{{ showOpt(r.out) }}</code>
            <span v-if="r.out === null" class="kl-note">（条件 {{ fns[r.id].note }} 不满足）</span>
          </div>
        </template>
      </li>
    </ol>
    <p v-if="mode === 'option' && parsedNumber === null" class="kl-note">请输入一个数字。</p>
  </div>
</template>

<style scoped>
.kl { max-width: 100%; overflow: hidden; }
.kl-tabs { display: flex; gap: 8px; flex-wrap: wrap; margin-bottom: 8px; }
.kl-hint { font-size: 13px; color: var(--vp-c-text-2); margin: 6px 0 10px; line-height: 1.6; }
.kl-row { display: flex; align-items: center; gap: 8px; flex-wrap: wrap; margin-bottom: 10px; font-size: 14px; }
.kl-input {
  flex: 1 1 200px; min-width: 0; max-width: 360px;
  padding: 4px 10px; border: 1px solid var(--vp-c-divider); border-radius: 6px;
  background: var(--vp-c-bg); color: var(--vp-c-text-1); font-family: var(--vp-font-family-mono); font-size: 13px;
}
.kl-num { max-width: 120px; }
.kl-type { font-family: var(--vp-font-family-mono); font-size: 12px; color: var(--vp-c-text-3); }
.kl-palette { display: flex; flex-wrap: wrap; gap: 6px; margin-bottom: 10px; }
.kl-fn {
  display: flex; flex-direction: column; align-items: flex-start; gap: 1px;
  padding: 4px 10px; border: 1px solid var(--vp-c-divider); border-radius: 8px;
  background: var(--vp-c-bg); color: var(--vp-c-text-1); cursor: pointer; font-size: 13px;
}
.kl-fn:hover:not(.disabled) { border-color: var(--vp-c-brand-1); }
.kl-fn.disabled { opacity: 0.4; cursor: not-allowed; }
.kl-sig { font-size: 11px; color: var(--vp-c-text-3); font-family: var(--vp-font-family-mono); }
.kl-chain { font-size: 13px; margin-bottom: 10px; overflow-x: auto; white-space: nowrap; }
.kl-chain-label { color: var(--vp-c-text-2); }
.kl-expr { color: var(--vp-c-brand-1); }
.kl-chain-sig { font-family: var(--vp-font-family-mono); font-size: 12px; color: var(--vp-c-text-2); margin-left: 4px; }
.kl-controls { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin-bottom: 12px; }
.kl-controls .ctfp-btn:disabled { opacity: 0.45; cursor: not-allowed; }
.kl-progress { font-size: 12px; color: var(--vp-c-text-3); margin-left: 4px; }
.kl-state {
  border: 1px solid var(--vp-c-brand-1); border-radius: 10px; padding: 10px 14px; margin-bottom: 10px;
  background: var(--vp-c-bg);
}
.kl-state-label { font-size: 12px; color: var(--vp-c-text-3); margin-bottom: 4px; }
.kl-pair { font-family: var(--vp-font-family-mono); font-size: 15px; word-break: break-all; line-height: 1.7; }
.kl-paren { color: var(--vp-c-text-3); margin: 0 3px; }
.kl-val { color: var(--vp-c-brand-1); font-weight: 600; }
.kl-log { color: var(--vp-c-text-1); }
.kl-old { color: var(--vp-c-text-2); }
.kl-new { background: var(--vp-c-warning-soft); color: var(--vp-c-warning-1); border-radius: 3px; font-weight: 600; }
.kl-none { color: var(--vp-c-danger-1) !important; }
.kl-trace { margin: 0; padding-left: 22px; font-size: 13px; line-height: 1.7; }
.kl-trace li { margin: 4px 0; color: var(--vp-c-text-2); word-break: break-word; }
.kl-trace li.latest { color: var(--vp-c-text-1); }
.kl-trace li.skipped { opacity: 0.55; }
.kl-sub { font-size: 12px; color: var(--vp-c-text-2); }
.kl-note { font-size: 12px; color: var(--vp-c-text-3); }
</style>
