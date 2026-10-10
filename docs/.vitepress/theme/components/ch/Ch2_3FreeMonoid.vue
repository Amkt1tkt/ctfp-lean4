<script setup>
import { ref, computed, watch, onBeforeUnmount } from 'vue'

const matmul = (x, y) => [
  x[0] * y[0] + x[1] * y[2], x[0] * y[1] + x[1] * y[3],
  x[2] * y[0] + x[3] * y[2], x[2] * y[1] + x[3] * y[3],
]

const TARGETS = [
  {
    key: 'add', name: '(ℕ, +, 0)', sym: '+', kind: 'num', e: 0, op: (x, y) => x + y,
    show: (x) => String(x), defaults: { a: 1, b: 1 },
    note: '取 a ↦ 1、b ↦ 1，同态就是“求长度”；取 a ↦ 1、b ↦ 0，就是“数 a 的个数”。加法可交换，所以 ab 和 ba 一定被等同。',
  },
  {
    key: 'mul', name: '(ℕ, ×, 1)', sym: '×', kind: 'num', e: 1, op: (x, y) => x * y,
    show: (x) => String(x), defaults: { a: 2, b: 3 },
    note: '乘法也可交换：只要两个词里 a 和 b 的个数相同，像就相同。试试把 a 设成 1——所有 a 都“消失”了。',
  },
  {
    key: 'xor', name: '(Bool, xor, false)', sym: '⊕', kind: 'bool', e: false, op: (x, y) => x !== y,
    show: (x) => (x ? 'true' : 'false'), defaults: { a: true, b: false },
    note: '只有两个元素的幺半群。a ↦ true、b ↦ false 时，同态计算的是“a 的个数是奇数吗”。15 个词被压成了 2 类。',
  },
  {
    key: 'mat', name: '2×2 整数矩阵（乘法）', sym: '·', kind: 'fixed', e: [1, 0, 0, 1], op: matmul,
    show: (m) => `[${m[0]} ${m[1]}; ${m[2]} ${m[3]}]`,
    defaults: { a: [1, 1, 0, 1], b: [1, 0, 1, 1] },
    note: '矩阵乘法不可交换。这两个矩阵生成的子幺半群恰好是自由的：不同的词永远映到不同的矩阵——这个同态是单射，什么都没被等同。',
  },
  {
    key: 'free', name: '自由幺半群自己', sym: '++', kind: 'fixed', e: '', op: (x, y) => x + y,
    show: (x) => (x === '' ? 'ε' : `"${x}"`), defaults: { a: 'a', b: 'b' },
    note: 'a ↦ "a"、b ↦ "b"：这就是恒等同态。由唯一性，从自由幺半群到它自己、并且固定生成元的同态，只有恒等这一个。',
  },
]

const tIdx = ref(0)
const T = computed(() => TARGETS[tIdx.value])
const gens = ref({ ...TARGETS[0].defaults })
watch(tIdx, () => {
  gens.value = JSON.parse(JSON.stringify(T.value.defaults))
  resetAnim()
})

const word = ref('abba')
const u = ref('ab')
const v = ref('ba')
const clean = (s) => s.replace(/[^ab]/g, '').slice(0, 10)

const keyOf = (x) => JSON.stringify(x)
const f = (c) => gens.value[c]

function steps(w) {
  // foldr：从右往左累乘，acc₀ = e
  const out = [{ acc: T.value.e, idx: w.length }]
  let acc = T.value.e
  for (let i = w.length - 1; i >= 0; i--) {
    acc = T.value.op(f(w[i]), acc)
    out.push({ acc, idx: i })
  }
  return out
}
const h = (w) => steps(w).at(-1).acc

const wordSteps = computed(() => steps(word.value))
const animStep = ref(-1)
let timer = null
function resetAnim() {
  clearInterval(timer)
  timer = null
  animStep.value = -1
}
onBeforeUnmount(resetAnim)
function play() {
  resetAnim()
  animStep.value = 0
  timer = setInterval(() => {
    if (animStep.value >= wordSteps.value.length - 1) {
      clearInterval(timer)
      timer = null
      return
    }
    animStep.value++
  }, 800)
}
watch(word, resetAnim)

const shownSteps = computed(() => (animStep.value < 0 ? wordSteps.value : wordSteps.value.slice(0, animStep.value + 1)))

const expr = computed(() => {
  const w = word.value
  if (!w) return `h(ε) = e = ${T.value.show(T.value.e)}`
  return 'h(' + w + ') = ' + [...w].map((c) => `f(${c})`).join(` ${T.value.sym} `) + ` ${T.value.sym} e`
})

const homCheck = computed(() => {
  const lhs = h(u.value + v.value)
  const rhs = T.value.op(h(u.value), h(v.value))
  return { lhs: T.value.show(lhs), rhs: T.value.show(rhs), ok: keyOf(lhs) === keyOf(rhs) }
})

const cmp = computed(() => {
  const freeEq = u.value === v.value
  const hu = h(u.value), hv = h(v.value)
  const tEq = keyOf(hu) === keyOf(hv)
  let msg
  if (freeEq) msg = '两个词本来就相同。'
  else if (tEq) msg = `在自由幺半群里 ${u.value || 'ε'} ≠ ${v.value || 'ε'}，但同态 h 把它们压到了同一个元素上——这个“等式”是目标幺半群带来的，不是自由幺半群自己的。`
  else msg = `在自由幺半群里 ${u.value || 'ε'} ≠ ${v.value || 'ε'}，在目标里它们也不同：h 没有把它们等同。`
  return { freeEq, tEq, hu: T.value.show(hu), hv: T.value.show(hv), msg }
})

const allWords = (() => {
  const out = ['']
  let layer = ['']
  for (let n = 1; n <= 3; n++) {
    layer = layer.flatMap((w) => [w + 'a', w + 'b'])
    out.push(...layer)
  }
  return out
})()

const groups = computed(() => {
  const m = new Map()
  for (const w of allWords) {
    const val = h(w)
    const k = keyOf(val)
    if (!m.has(k)) m.set(k, { val: T.value.show(val), words: [] })
    m.get(k).words.push(w)
  }
  return [...m.values()]
})
const hue = (i) => (i * 67) % 360

function setNum(c, e) {
  const n = Math.max(0, Math.min(9, Math.floor(Number(e.target.value) || 0)))
  gens.value = { ...gens.value, [c]: n }
}
function setBool(c, e) {
  gens.value = { ...gens.value, [c]: e.target.value === 'true' }
}
</script>

<template>
  <div class="ctfp-widget free-monoid">
    <div class="ctfp-widget-title">交互：自由幺半群——生成元的去向唯一地决定一切</div>

    <div class="row">
      <span class="lbl">目标幺半群 n：</span>
      <button v-for="(t, i) in TARGETS" :key="t.key" class="ctfp-btn" :class="{ on: tIdx === i }" @click="tIdx = i">{{ t.name }}</button>
    </div>

    <div class="row gens">
      <span class="lbl">生成元的去向 f :</span>
      <template v-for="c in ['a', 'b']" :key="c">
        <span class="gen">{{ c }} ↦</span>
        <input v-if="T.kind === 'num'" type="number" min="0" max="9" :value="gens[c]" @input="setNum(c, $event)" class="num" />
        <select v-else-if="T.kind === 'bool'" :value="String(gens[c])" @change="setBool(c, $event)">
          <option value="true">true</option>
          <option value="false">false</option>
        </select>
        <code v-else>{{ T.show(gens[c]) }}</code>
      </template>
      <span class="lbl">单位元 e = <code>{{ T.show(T.e) }}</code></span>
    </div>
    <p class="note">{{ T.note }}</p>

    <div class="panel">
      <div class="row">
        <span class="lbl">词 w ∈ List {a, b}：</span>
        <span class="word">
          <span v-for="(c, i) in word" :key="i" class="letter" :class="{ active: animStep >= 0 && wordSteps[animStep] && wordSteps[animStep].idx === i }">{{ c }}</span>
          <span v-if="!word" class="letter empty">ε</span>
        </span>
      </div>
      <div class="row">
        <button class="ctfp-btn" @click="word = clean(word + 'a')">+ a</button>
        <button class="ctfp-btn" @click="word = clean(word + 'b')">+ b</button>
        <button class="ctfp-btn" @click="word = word.slice(0, -1)">⌫</button>
        <button class="ctfp-btn" @click="word = ''">清空</button>
        <button class="ctfp-btn" @click="play">▶ 逐步计算 h(w)</button>
      </div>
      <div class="expr"><code>{{ expr }}</code></div>
      <ol class="steps">
        <li v-for="(s, i) in shownSteps" :key="i" :class="{ last: i === shownSteps.length - 1 }">
          <template v-if="i === 0">从右边开始：acc = e = <b>{{ T.show(s.acc) }}</b></template>
          <template v-else>acc = f({{ word[s.idx] }}) {{ T.sym }} acc = {{ T.show(f(word[s.idx])) }} {{ T.sym }} {{ T.show(shownSteps[i - 1].acc) }} = <b>{{ T.show(s.acc) }}</b></template>
        </li>
      </ol>
      <p class="result">h({{ word || 'ε' }}) = <b>{{ T.show(h(word)) }}</b></p>
    </div>

    <div class="panel">
      <div class="row">
        <span class="lbl">比较两个词：</span>
        <input class="w" :value="u" @input="u = clean($event.target.value)" placeholder="ε" />
        <input class="w" :value="v" @input="v = clean($event.target.value)" placeholder="ε" />
      </div>
      <table class="cmp">
        <tbody>
          <tr><th></th><th>u = {{ u || 'ε' }}</th><th>v = {{ v || 'ε' }}</th><th>相等吗？</th></tr>
          <tr><td>自由幺半群中</td><td>{{ u || 'ε' }}</td><td>{{ v || 'ε' }}</td><td :class="cmp.freeEq ? 'yes' : 'no'">{{ cmp.freeEq ? '相等' : '不相等' }}</td></tr>
          <tr><td>经 h 映到 n 中</td><td>{{ cmp.hu }}</td><td>{{ cmp.hv }}</td><td :class="cmp.tEq ? 'yes' : 'no'">{{ cmp.tEq ? '相等' : '不相等' }}</td></tr>
        </tbody>
      </table>
      <p class="note">{{ cmp.msg }}</p>
      <p class="note">同态性质检查：h(u ++ v) = <code>{{ homCheck.lhs }}</code>，h(u) {{ T.sym }} h(v) = <code>{{ homCheck.rhs }}</code> {{ homCheck.ok ? '✓' : '✗' }}</p>
    </div>

    <div class="panel">
      <div class="lbl">长度 ≤ 3 的全部 15 个词，按它们在 n 中的像分组（同一组 = 被 h 等同）：</div>
      <div class="groups">
        <div v-for="(g, i) in groups" :key="g.val" class="group" :style="{ borderColor: `hsl(${hue(i)} 60% 55%)` }">
          <div class="gval" :style="{ color: `hsl(${hue(i)} 55% 45%)` }">{{ g.val }}</div>
          <div class="gwords">
            <span v-for="w in g.words" :key="w" class="chip" @click="word = w">{{ w || 'ε' }}</span>
          </div>
        </div>
      </div>
      <p class="note">共 {{ groups.length }} 组。{{ groups.length === 15 ? '每个词自成一组：h 是单射，没有任何等同——目标里“装得下”整个自由结构。' : '组数少于 15：有些不同的词被压到了一起。目标幺半群可以看作自由幺半群“多捆了一些等式”的结果。' }}</p>
    </div>
    <p class="hint">提示：点击分组中的词可以把它放进上面的计算器。自由幺半群里没有 ab = ba 这类等式；你看到的所有“等同”都来自目标幺半群。</p>
  </div>
</template>

<style scoped>
.free-monoid { max-width: 100%; }
.row { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin: 8px 0; }
.lbl { font-size: 13px; color: var(--vp-c-text-2); }
.gen { font-family: var(--vp-font-family-mono); font-size: 14px; margin-left: 6px; }
.num { width: 52px; }
.num, select, .w {
  font-size: 13px; padding: 2px 6px; border: 1px solid var(--vp-c-divider); border-radius: 6px;
  background: var(--vp-c-bg); color: var(--vp-c-text-1);
}
.w { width: 110px; font-family: var(--vp-font-family-mono); }
.note, .hint { font-size: 13px; line-height: 1.6; color: var(--vp-c-text-2); margin: 6px 0; }
.panel { border: 1px solid var(--vp-c-divider); border-radius: 10px; padding: 10px 12px; margin: 10px 0; background: var(--vp-c-bg); }
.word { display: inline-flex; gap: 4px; flex-wrap: wrap; }
.letter {
  display: inline-block; min-width: 26px; text-align: center; padding: 2px 6px; border-radius: 6px;
  border: 1px solid var(--vp-c-brand-1); color: var(--vp-c-brand-1); font-family: var(--vp-font-family-mono); font-size: 15px;
  transition: background 0.2s;
}
.letter.active { background: var(--vp-c-brand-1); color: var(--vp-c-white, #fff); }
.letter.empty { border-style: dashed; color: var(--vp-c-text-3); border-color: var(--vp-c-divider); }
.expr { overflow-x: auto; font-size: 13px; margin: 6px 0; }
.steps { font-size: 13px; margin: 6px 0; padding-left: 22px; font-family: var(--vp-font-family-mono); }
.steps li { margin: 2px 0; color: var(--vp-c-text-2); }
.steps li.last { color: var(--vp-c-text-1); }
.result { font-size: 15px; margin: 6px 0; }
.cmp { font-size: 13px; border-collapse: collapse; display: table; width: 100%; margin: 6px 0; }
.cmp th, .cmp td { border: 1px solid var(--vp-c-divider); padding: 4px 8px; text-align: center; font-family: var(--vp-font-family-mono); }
.cmp td.yes { color: var(--vp-c-warning-1); font-weight: 600; }
.cmp td.no { color: var(--vp-c-success-1, #18794e); font-weight: 600; }
.groups { display: flex; flex-wrap: wrap; gap: 8px; margin: 8px 0; }
.group { border: 2px solid; border-radius: 10px; padding: 6px 8px; min-width: 90px; max-width: 100%; }
.gval { font-family: var(--vp-font-family-mono); font-size: 12px; font-weight: 600; margin-bottom: 4px; }
.gwords { display: flex; flex-wrap: wrap; gap: 4px; }
.chip {
  font-family: var(--vp-font-family-mono); font-size: 12px; padding: 1px 6px; border-radius: 999px;
  background: var(--vp-c-bg-soft); border: 1px solid var(--vp-c-divider); cursor: pointer;
}
.chip:hover { border-color: var(--vp-c-brand-1); }
</style>
