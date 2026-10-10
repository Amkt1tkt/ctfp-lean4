<script setup>
// 项与模型：同一棵幺半群项的语法树，放进不同的模型（解释器）里求值；
// 比较等式两边在各个模型中的值，以及它们在自由幺半群中的范式。
import { computed, ref } from 'vue'

const VARS = ['x', 'y', 'z']

// ---------- 解析：x y z e，乘法写作 · 或 *，左结合，可加括号 ----------
function parse(src) {
  const toks = src.replace(/\s+/g, '').split('')
  let i = 0
  const peek = () => toks[i]
  function atom() {
    const c = peek()
    if (c === '(') {
      i++
      const t = expr()
      if (peek() !== ')') throw new Error('缺少右括号')
      i++
      return t
    }
    if (VARS.includes(c)) { i++; return { t: 'var', i: VARS.indexOf(c) } }
    if (c === 'e') { i++; return { t: 'e' } }
    throw new Error(c ? `无法识别的字符“${c}”` : '表达式不完整')
  }
  function expr() {
    let t = atom()
    while (peek() === '·' || peek() === '*' || peek() === '.') {
      i++
      t = { t: 'mul', a: t, b: atom() }
    }
    return t
  }
  const t = expr()
  if (i < toks.length) throw new Error(`多余的字符“${toks[i]}”`)
  return t
}

const show = (t, top = true) => {
  if (t.t === 'var') return VARS[t.i]
  if (t.t === 'e') return 'e'
  const s = `${show(t.a, false)}·${show(t.b, false)}`
  return top ? s : `(${s})`
}

// ---------- 模型 ----------
const MODELS = [
  { id: 'nat', name: '(ℕ, +, 0)', kind: 'num', one: 0, mul: (a, b) => a + b, fmt: String, init: [1, 2, 3] },
  { id: 'str', name: '(String, ++, "")', kind: 'str', one: '', mul: (a, b) => a + b, fmt: (s) => JSON.stringify(s), init: ['ab', 'c', 'd'] },
  { id: 'bool', name: '(Bool, &&, true)', kind: 'bool', one: true, mul: (a, b) => a && b, fmt: String, init: [true, false, true] },
  { id: 'mult', name: '(ℕ, ×, 1)', kind: 'num', one: 1, mul: (a, b) => a * b, fmt: String, init: [2, 3, 4] },
  { id: 'max', name: '(ℕ, max, 0)', kind: 'num', one: 0, mul: (a, b) => Math.max(a, b), fmt: String, init: [5, 1, 3] },
  { id: 'free', name: '自由幺半群 List', kind: 'free', one: [], mul: (a, b) => [...a, ...b], fmt: (l) => `[${l.join(', ')}]`, init: [['x'], ['y'], ['z']] },
]
const modelId = ref('str')
const M = computed(() => MODELS.find((m) => m.id === modelId.value))
const envs = ref(Object.fromEntries(MODELS.map((m) => [m.id, m.init.map((v) => (Array.isArray(v) ? [...v] : v))])))
const env = computed(() => envs.value[modelId.value])

function evalT(t, m, e) {
  if (t.t === 'var') return e[t.i]
  if (t.t === 'e') return m.one
  return m.mul(evalT(t.a, m, e), evalT(t.b, m, e))
}
const toList = (t) => (t.t === 'var' ? [VARS[t.i]] : t.t === 'e' ? [] : [...toList(t.a), ...toList(t.b)])
const eq = (a, b) => JSON.stringify(a) === JSON.stringify(b)

// ---------- 等式两边 ----------
const PRESETS = [
  { l: '(x·y)·z', r: 'x·(y·z)', note: '结合律' },
  { l: '(e·x)·(y·e)·z', r: 'x·(y·z)', note: '单位律 + 结合律' },
  { l: 'e·x', r: 'x', note: '左单位律' },
  { l: 'x·y', r: 'y·x', note: '交换律？' },
  { l: 'x·x', r: 'x', note: '幂等？' },
]
const lsrc = ref(PRESETS[0].l)
const rsrc = ref(PRESETS[0].r)
const pick = (p) => { lsrc.value = p.l; rsrc.value = p.r }

const side = (src) => {
  try { return { t: parse(src), err: null } } catch (e) { return { t: null, err: e.message } }
}
const L = computed(() => side(lsrc.value))
const R = computed(() => side(rsrc.value))
const ok = computed(() => L.value.t && R.value.t)

const nfL = computed(() => (ok.value ? toList(L.value.t) : []))
const nfR = computed(() => (ok.value ? toList(R.value.t) : []))
const sameNF = computed(() => eq(nfL.value, nfR.value))

const table = computed(() => {
  if (!ok.value) return []
  return MODELS.map((m) => {
    const e = envs.value[m.id]
    const a = evalT(L.value.t, m, e), b = evalT(R.value.t, m, e)
    return { m, a: m.fmt(a), b: m.fmt(b), same: eq(a, b) }
  })
})

const curRow = computed(() => table.value.find((r) => r.m.id === modelId.value) || { a: '', b: '' })

// ---------- 树的布局 ----------
const LEAF_W = 58, LEVEL_H = 58
function layout(t, m, e) {
  const nodes = [], edges = []
  let leaf = 0
  function go(t, depth) {
    let x
    if (t.t === 'mul') {
      const a = go(t.a, depth + 1), b = go(t.b, depth + 1)
      x = (a.x + b.x) / 2
      const n = { x, y: depth * LEVEL_H + 22, label: '·', val: m.fmt(evalT(t, m, e)), op: true }
      nodes.push(n)
      edges.push([n, a], [n, b])
      return n
    }
    x = leaf++ * LEAF_W + LEAF_W / 2
    const n = { x, y: depth * LEVEL_H + 22, label: t.t === 'var' ? VARS[t.i] : 'e', val: m.fmt(evalT(t, m, e)), op: false }
    nodes.push(n)
    return n
  }
  go(t, 0)
  const w = Math.max(leaf * LEAF_W, 80)
  const h = Math.max(...nodes.map((n) => n.y)) + 40
  return { nodes, edges, w, h }
}
const treeL = computed(() => (L.value.t ? layout(L.value.t, M.value, env.value) : null))
const treeR = computed(() => (R.value.t ? layout(R.value.t, M.value, env.value) : null))
const short = (s) => (s.length > 9 ? s.slice(0, 8) + '…' : s)

// ---------- 变量取值 ----------
function setVar(i, raw) {
  const m = M.value
  let v = raw
  if (m.kind === 'num') v = Math.max(0, Math.min(999, parseInt(raw, 10) || 0))
  if (m.kind === 'free') v = raw.split(/[\s,]+/).filter(Boolean)
  envs.value[m.id][i] = v
}
const toggleBool = (i) => (envs.value.bool[i] = !envs.value.bool[i])
function reroll() {
  const m = M.value
  const rnd = (k) => Math.floor(Math.random() * k)
  const e = envs.value[m.id]
  for (let i = 0; i < 3; i++) {
    if (m.kind === 'num') e[i] = m.id === 'mult' ? rnd(6) + 1 : rnd(20)
    if (m.kind === 'str') e[i] = 'abcdefgh'.slice(rnd(6), rnd(6) + 1 + rnd(2)) || 'q'
    if (m.kind === 'bool') e[i] = Math.random() < 0.6
    if (m.kind === 'free') e[i] = Array.from({ length: rnd(3) }, () => 'abc'[rnd(3)])
  }
}
const inputVal = (i) => (M.value.kind === 'free' ? env.value[i].join(' ') : env.value[i])
</script>

<template>
  <div class="ctfp-widget tm">
    <div class="ctfp-widget-title">项与模型：一棵语法树，许多个解释器</div>
    <p class="tm-hint">
      在两个输入框里写幺半群项（变量 <code>x y z</code>，单位元 <code>e</code>，乘法 <code>·</code> 或 <code>*</code>）。
      选一个模型，改改变量的取值，看语法树每个节点的值；下方表格同时列出所有模型中等式两边的值。
    </p>
    <div class="tm-row">
      <span class="lbl">常见等式：</span>
      <button v-for="p in PRESETS" :key="p.l + p.r" class="ctfp-btn" :class="{ on: lsrc === p.l && rsrc === p.r }" @click="pick(p)">
        {{ p.note }}
      </button>
    </div>
    <div class="tm-eq">
      <input v-model="lsrc" class="tm-input" spellcheck="false" aria-label="等式左边" />
      <span class="tm-eqsign">=</span>
      <input v-model="rsrc" class="tm-input" spellcheck="false" aria-label="等式右边" />
    </div>
    <div v-if="L.err || R.err" class="tm-err">解析错误：{{ L.err || R.err }}</div>

    <div class="tm-row">
      <span class="lbl">模型：</span>
      <button v-for="m in MODELS" :key="m.id" class="ctfp-btn" :class="{ on: modelId === m.id }" @click="modelId = m.id">{{ m.name }}</button>
    </div>
    <div class="tm-row tm-env">
      <span class="lbl">取值 env：</span>
      <label v-for="(v, i) in VARS" :key="v" class="tm-var">
        <span>{{ v }} =</span>
        <button v-if="M.kind === 'bool'" class="ctfp-btn" @click="toggleBool(i)">{{ env[i] }}</button>
        <input v-else :value="inputVal(i)" class="tm-small" :type="M.kind === 'num' ? 'number' : 'text'"
               :placeholder="M.kind === 'free' ? '空格分隔' : ''" @input="setVar(i, $event.target.value)" />
      </label>
      <button class="ctfp-btn" @click="reroll">随机换一组值</button>
    </div>

    <div v-if="ok" class="tm-trees">
      <div v-for="(tr, k) in [treeL, treeR]" :key="k" class="tm-tree">
        <div class="tm-tree-head">{{ k === 0 ? '左边' : '右边' }}：<code>{{ show(k === 0 ? L.t : R.t) }}</code></div>
        <svg :viewBox="`0 0 ${tr.w} ${tr.h}`" :width="tr.w" :style="{ maxWidth: '100%' }">
          <line v-for="(ed, j) in tr.edges" :key="'e' + j" :x1="ed[0].x" :y1="ed[0].y" :x2="ed[1].x" :y2="ed[1].y" class="tm-edge" />
          <g v-for="(n, j) in tr.nodes" :key="'n' + j">
            <circle :cx="n.x" :cy="n.y" r="13" :class="n.op ? 'tm-op' : 'tm-leaf'" />
            <text :x="n.x" :y="n.y + 5" text-anchor="middle" class="tm-lab">{{ n.label }}</text>
            <text :x="n.x" :y="n.y + 29" text-anchor="middle" class="tm-val">{{ short(n.val) }}</text>
          </g>
        </svg>
        <div class="tm-result">在 {{ M.name }} 中的值：<b>{{ k === 0 ? curRow.a : curRow.b }}</b></div>
      </div>
    </div>

    <table v-if="ok" class="tm-table">
      <thead><tr><th>模型</th><th>左边</th><th>右边</th><th></th></tr></thead>
      <tbody>
        <tr v-for="r in table" :key="r.m.id" :class="{ cur: r.m.id === modelId }">
          <td>{{ r.m.name }}</td><td><code>{{ r.a }}</code></td><td><code>{{ r.b }}</code></td>
          <td :class="r.same ? 'yes' : 'no'">{{ r.same ? '相等' : '不等' }}</td>
        </tr>
      </tbody>
    </table>

    <div v-if="ok" class="tm-verdict" :class="sameNF ? 'yes' : 'no'">
      范式（<code>toList</code>）：左 <code>[{{ nfL.join(', ') }}]</code>，右 <code>[{{ nfR.join(', ') }}]</code>。
      <template v-if="sameNF">
        范式相同，所以这条等式在<b>所有</b>幺半群、<b>所有</b>取值下都成立（定理 <code>eq_of_toList</code>）——换多少组值都不会出现“不等”。
      </template>
      <template v-else>
        范式不同，所以它在自由幺半群里不成立，<b>不是</b>幺半群理论的定律——即使某些模型（比如可交换或幂等的）碰巧让两边相等。
      </template>
    </div>
  </div>
</template>

<style scoped>
.tm-hint { font-size: 13px; color: var(--vp-c-text-2); margin: 0 0 10px; line-height: 1.7; }
.tm-row { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin: 8px 0; }
.lbl { font-size: 13px; color: var(--vp-c-text-2); margin-right: 2px; }
.tm-eq { display: flex; gap: 8px; align-items: center; flex-wrap: wrap; margin: 10px 0; }
.tm-input {
  flex: 1 1 160px; min-width: 0; font-family: var(--vp-font-family-mono); font-size: 15px;
  padding: 5px 10px; border: 1px solid var(--vp-c-divider); border-radius: 8px; background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
}
.tm-eqsign { font-size: 18px; font-weight: 600; }
.tm-err { color: var(--vp-c-danger-1); font-size: 13px; }
.tm-env { gap: 10px; }
.tm-var { display: inline-flex; align-items: center; gap: 4px; font-family: var(--vp-font-family-mono); font-size: 14px; }
.tm-small {
  width: 78px; font-family: var(--vp-font-family-mono); font-size: 13px; padding: 3px 6px;
  border: 1px solid var(--vp-c-divider); border-radius: 6px; background: var(--vp-c-bg); color: var(--vp-c-text-1);
}
.tm-trees { display: flex; flex-wrap: wrap; gap: 14px; margin: 12px 0; }
.tm-tree {
  flex: 1 1 240px; min-width: 0; border: 1px solid var(--vp-c-divider); border-radius: 10px;
  padding: 8px 10px; background: var(--vp-c-bg); overflow-x: auto;
}
.tm-tree-head { font-size: 13px; color: var(--vp-c-text-2); margin-bottom: 4px; }
.tm-tree svg { display: block; margin: 0 auto; }
.tm-edge { stroke: var(--vp-c-text-3); stroke-width: 1.4; }
.tm-op { fill: var(--vp-c-brand-soft, rgba(59, 111, 216, 0.14)); stroke: var(--vp-c-brand-1); stroke-width: 1.4; }
.tm-leaf { fill: var(--vp-c-bg-soft); stroke: var(--vp-c-text-2); stroke-width: 1.2; }
.tm-lab { font-size: 14px; font-weight: 600; fill: var(--vp-c-text-1); font-family: var(--vp-font-family-mono); }
.tm-val { font-size: 11px; fill: var(--vp-c-brand-1); font-family: var(--vp-font-family-mono); }
.tm-result { font-size: 13px; margin-top: 4px; text-align: center; }
.tm-table { width: 100%; font-size: 13px; border-collapse: collapse; margin: 8px 0; display: table; }
.tm-table th, .tm-table td { padding: 4px 8px; border: 1px solid var(--vp-c-divider); }
.tm-table tr.cur td { background: var(--vp-c-bg); font-weight: 600; }
td.yes, .tm-verdict.yes b { color: var(--vp-c-success-1, #18794e); }
td.no { color: var(--vp-c-danger-1); }
.tm-verdict { font-size: 13px; line-height: 1.75; padding: 8px 12px; border-radius: 8px; border: 1px solid var(--vp-c-divider); background: var(--vp-c-bg); }
.tm-verdict.no { border-color: var(--vp-c-danger-1); }
.tm-verdict.yes { border-color: var(--vp-c-success-1, #18794e); }
</style>
