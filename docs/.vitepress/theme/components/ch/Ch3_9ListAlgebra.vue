<script setup>
import { ref, computed } from 'vue'

const ops = [
  { key: 'add', name: '加法', z: 0, f: (x, y) => x + y, show: String, monoid: true },
  { key: 'mul', name: '乘法', z: 1, f: (x, y) => x * y, show: String, monoid: true },
  { key: 'max', name: 'max', z: 0, f: (x, y) => Math.max(x, y), show: String, monoid: true, note: '（在自然数上，0 是 max 的单位元）' },
  { key: 'cat', name: '字符串拼接', z: '', f: (x, y) => String(x) + String(y), show: (v) => JSON.stringify(String(v)), monoid: true, str: true },
  { key: 'sub', name: '减法', z: 0, f: (x, y) => x - y, show: String, monoid: false, note: '（不满足结合律！）' },
  { key: 'mulOne', name: '乘法，但 z = 0', z: 0, f: (x, y) => x * y, show: String, monoid: false, note: '（0 不是乘法的单位元）' },
]

const inputs = [
  [[1, 2], [3], [4, 5]],
  [[2, 3], [], [4]],
  [[5], [1, 1, 1], [2, 3]],
]

const opIdx = ref(0)
const inIdx = ref(0)
const op = computed(() => ops[opIdx.value])
const xss = computed(() => (op.value.str ? inputs[inIdx.value].map((xs) => xs.map(String)) : inputs[inIdx.value]))

const alg = (xs) => xs.reduceRight((acc, x) => op.value.f(x, acc), op.value.z)
const showList = (xs) => '[' + xs.map(op.value.show).join(', ') + ']'
const showNested = (xss) => '[' + xss.map(showList).join(', ') + ']'

const joined = computed(() => xss.value.flat())
const pathA = computed(() => alg(joined.value))
const inner = computed(() => xss.value.map(alg))
const pathB = computed(() => alg(inner.value))
const multOk = computed(() => pathA.value === pathB.value)

const unitSample = computed(() => (op.value.str ? '7' : 7))
const unitVal = computed(() => alg([unitSample.value]))
const unitOk = computed(() => unitVal.value === unitSample.value)
</script>

<template>
  <div class="ctfp-widget lalg">
    <div class="ctfp-widget-title">List 单子的代数：两条路是否走到同一个地方？</div>
    <p class="hint">
      取 <code>alg = foldr f z</code>。选一个二元运算 <code>f</code> 和起始值 <code>z</code>，看看它是否满足单子代数的两条定律。
      满足的那些恰好就是幺半群。
    </p>
    <div class="row">
      <span class="lbl">运算：</span>
      <button v-for="(o, i) in ops" :key="o.key" class="ctfp-btn" :class="{ on: i === opIdx }" @click="opIdx = i">{{ o.name }}</button>
    </div>
    <div class="row">
      <span class="lbl">嵌套列表：</span>
      <button v-for="(v, i) in inputs" :key="i" class="ctfp-btn" :class="{ on: i === inIdx }" @click="inIdx = i">{{ showNested(v) }}</button>
    </div>
    <div class="meta">
      当前：<code>f = {{ op.name }}</code>，<code>z = {{ op.show(op.z) }}</code> <span class="muted">{{ op.note }}</span>
    </div>

    <div class="law">
      <div class="law-title">结合律方块：<code>alg ∘ join = alg ∘ map alg</code></div>
      <div class="paths">
        <div class="path">
          <div class="ptitle">路径一：先 <code>join</code> 再 <code>alg</code></div>
          <div class="stepline"><code>{{ showNested(xss) }}</code></div>
          <div class="arrow">↓ join（拼接）</div>
          <div class="stepline"><code>{{ showList(joined) }}</code></div>
          <div class="arrow">↓ alg</div>
          <div class="stepline result"><code>{{ op.show(pathA) }}</code></div>
        </div>
        <div class="path">
          <div class="ptitle">路径二：先 <code>map alg</code> 再 <code>alg</code></div>
          <div class="stepline"><code>{{ showNested(xss) }}</code></div>
          <div class="arrow">↓ map alg（逐个折叠内层）</div>
          <div class="stepline"><code>{{ showList(inner) }}</code></div>
          <div class="arrow">↓ alg</div>
          <div class="stepline result"><code>{{ op.show(pathB) }}</code></div>
        </div>
      </div>
      <div :class="['verdict', multOk ? 'good' : 'bad']">
        {{ multOk ? '两条路径结果相同：这个方块交换。' : '两条路径结果不同：方块不交换，这不是单子代数。' }}
      </div>
    </div>

    <div class="law">
      <div class="law-title">单位律：<code>alg ∘ pure = id</code></div>
      <div class="stepline">
        <code>alg [{{ op.show(unitSample) }}] = f {{ op.show(unitSample) }} {{ op.show(op.z) }} = {{ op.show(unitVal) }}</code>
      </div>
      <div :class="['verdict', unitOk ? 'good' : 'bad']">
        {{ unitOk ? '得到原来的值：z 是 f 的右单位元。' : '没有得回原来的值：z 不是右单位元。' }}
      </div>
    </div>
    <p class="hint small">
      提示：对减法试试不同的嵌套方式。对某些输入两条路恰好相等，但只要有一个反例，定律就不成立；
      而对幺半群，无论怎么选，两条路总是相等（下文的 Lean 证明对所有输入一次性保证了这一点）。
    </p>
  </div>
</template>

<style scoped>
.lalg { max-width: 100%; }
.hint { font-size: 0.9em; color: var(--vp-c-text-2); margin: 0.3em 0 0.6em; }
.hint.small { font-size: 0.85em; margin-top: 10px; }
.row { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin: 6px 0; }
.lbl { font-size: 0.9em; color: var(--vp-c-text-2); }
.ctfp-btn.on { background: var(--vp-c-brand-1); color: var(--vp-c-white, #fff); border-color: var(--vp-c-brand-1); }
.meta { font-size: 0.9em; margin: 6px 0; }
.muted { color: var(--vp-c-text-3); }
.law { border: 1px solid var(--vp-c-divider); border-radius: 8px; padding: 8px 12px; margin-top: 10px; }
.law-title { font-weight: 600; font-size: 0.92em; margin-bottom: 6px; }
.paths { display: flex; flex-wrap: wrap; gap: 12px; }
.path { flex: 1 1 240px; background: var(--vp-c-bg-soft); border-radius: 6px; padding: 8px 10px; min-width: 0; }
.ptitle { font-size: 0.88em; color: var(--vp-c-text-2); margin-bottom: 4px; }
.stepline { font-size: 0.88em; word-break: break-all; }
.stepline.result code { font-weight: 700; color: var(--vp-c-brand-1); }
.arrow { font-size: 0.8em; color: var(--vp-c-text-3); margin: 2px 0 2px 6px; }
.verdict { margin-top: 8px; font-size: 0.9em; font-weight: 600; }
.verdict.good { color: var(--vp-c-success-1, #18794e); }
.verdict.bad { color: var(--vp-c-danger-1); }
</style>
