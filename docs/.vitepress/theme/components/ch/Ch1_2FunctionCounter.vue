<script setup>
// 1.2 枚举小的有限类型之间的所有函数，直观展示“函数个数 = |B|^|A|”。
import { computed, ref } from 'vue'
import katex from 'katex'

const TYPES = {
  Empty: { name: 'Empty', elems: [] },
  Unit: { name: 'Unit', elems: ['()'] },
  Bool: { name: 'Bool', elems: ['false', 'true'] },
  Fin3: { name: 'Fin 3', elems: ['0', '1', '2'] },
}
const ORDER = ['Empty', 'Unit', 'Bool', 'Fin3']

const dom = ref('Bool')
const cod = ref('Bool')
const picked = ref(null)

const A = computed(() => TYPES[dom.value])
const B = computed(() => TYPES[cod.value])
const tex = (s) => katex.renderToString(s, { throwOnError: false })

function choose(which, key) {
  if (which === 'dom') dom.value = key
  else cod.value = key
  picked.value = null
}
function preset(a, b) {
  dom.value = a
  cod.value = b
  picked.value = null
}

const count = computed(() => B.value.elems.length ** A.value.elems.length)

// 每个函数用“值的下标数组”表示：fn[i] = A 的第 i 个元素被映到 B 的第几个元素。
const functions = computed(() => {
  const n = A.value.elems.length
  const m = B.value.elems.length
  const out = []
  for (let k = 0; k < count.value; k++) {
    const vals = []
    let r = k
    for (let i = n - 1; i >= 0; i--) {
      vals[i] = r % m
      r = Math.floor(r / m)
    }
    out.push(vals)
  }
  return out
})

function describe(vals) {
  const a = A.value
  const b = B.value
  const out = b.elems
  if (a.elems.length === 0) {
    const name = cod.value === 'Empty' ? '空函数（同时也是 id）' : '空函数（Empty.elim）'
    return { name, lean: 'fun e => nomatch e' }
  }
  const isId = dom.value === cod.value && vals.every((v, i) => v === i)
  let lean
  if (cod.value === 'Unit') lean = 'fun _ => ()'
  else if (dom.value === 'Unit') lean = `fun () => ${out[vals[0]]}`
  else if (vals.every((v) => v === vals[0])) lean = `fun _ => ${out[vals[0]]}`
  else lean = 'fun ' + a.elems.map((x, i) => `| ${x} => ${out[vals[i]]}`).join(' ')
  let name = ''
  if (cod.value === 'Unit') name = isId ? '恒等函数 id（也是 unit）' : 'unit：一切都去 ()'
  else if (isId) name = '恒等函数 id'
  else if (dom.value === 'Unit') name = `挑出元素 ${out[vals[0]]}`
  else if (dom.value === 'Bool' && cod.value === 'Bool' && vals[0] === 1 && vals[1] === 0) name = '取反 not'
  else if (vals.every((v) => v === vals[0])) name = `常值函数：总是 ${out[vals[0]]}`
  if (isId && lean !== 'fun _ => ()') lean = 'fun x => x'
  return { name, lean }
}

const cards = computed(() => functions.value.map((vals) => ({ vals, ...describe(vals) })))

const formulaHtml = computed(() => {
  const n = A.value.elems.length
  const m = B.value.elems.length
  return tex(`|\\texttt{${B.value.name}}|^{|\\texttt{${A.value.name}}|} = ${m}^{${n}} = ${count.value}`)
})

const explanation = computed(() => {
  const n = A.value.elems.length
  const m = B.value.elems.length
  if (n === 0) {
    return `定义域 Empty 里一个元素都没有，所以“给每个元素指定去处”这件事无事可做——恰好有一种做法：什么都不做。这就是为什么从 Empty 到任何类型（包括 Empty 自己）都恰有一个函数，也就是 ${m}^0 = 1。`
  }
  if (m === 0) {
    return `定义域 ${A.value.name} 里有元素，每个元素都必须被送到 Empty 里的某个元素——可 Empty 是空的，无处可去。所以一个函数也没有：0^${n} = 0。`
  }
  if (m === 1) {
    return `陪域 Unit 只有一个元素 ()，每个元素都只能去那里，没有任何选择余地：1^${n} = 1。这个唯一的函数就是 unit。`
  }
  if (n === 1) {
    return `定义域只有一个元素 ()，函数只需决定它去哪里——有 ${m} 种选法。所以从 Unit 出发的函数，和陪域的元素一一对应。`
  }
  return `${A.value.name} 的 ${n} 个元素各自独立地在 ${m} 个去处中选一个：${Array(n).fill(m).join(' × ')} = ${count.value}。`
})

const ROW = 26
function layout(vals) {
  const a = A.value.elems
  const b = B.value.elems
  const rows = Math.max(a.length, b.length, 1)
  const h = rows * ROW + 26
  const ya = (i) => 14 + (rows - a.length) * ROW / 2 + i * ROW + ROW / 2
  const yb = (j) => 14 + (rows - b.length) * ROW / 2 + j * ROW + ROW / 2
  const lines = a.map((_, i) => ({ y1: ya(i), y2: yb(vals[i]) }))
  return { h, rows, ya, yb, lines }
}
</script>

<template>
  <div class="ctfp-widget ch12-count">
    <div class="ctfp-widget-title">数一数：从 A 到 B 一共有多少个函数？</div>
    <p class="hint">选择定义域 A 和陪域 B，下面会列出<strong>所有</strong>可能的函数（左列是 A 的元素，右列是 B 的元素，箭头表示“送到哪里”）。点一张卡片可以把它高亮。</p>

    <div class="pickers">
      <div class="prow">
        <span class="plabel">A（定义域）</span>
        <button v-for="k in ORDER" :key="k" :class="['ctfp-btn', { on: dom === k }]" @click="choose('dom', k)">{{ TYPES[k].name }}</button>
      </div>
      <div class="prow">
        <span class="plabel">B（陪域）</span>
        <button v-for="k in ORDER" :key="k" :class="['ctfp-btn', { on: cod === k }]" @click="choose('cod', k)">{{ TYPES[k].name }}</button>
      </div>
      <div class="prow presets">
        <span class="plabel">常用</span>
        <button class="ctfp-btn" @click="preset('Bool', 'Bool')">Bool → Bool</button>
        <button class="ctfp-btn" @click="preset('Unit', 'Bool')">Unit → Bool</button>
        <button class="ctfp-btn" @click="preset('Bool', 'Unit')">Bool → Unit</button>
        <button class="ctfp-btn" @click="preset('Empty', 'Bool')">Empty → Bool</button>
        <button class="ctfp-btn" @click="preset('Bool', 'Empty')">Bool → Empty</button>
        <button class="ctfp-btn" @click="preset('Empty', 'Empty')">Empty → Empty</button>
      </div>
    </div>

    <div class="summary">
      <div class="formula">
        <code>{{ A.name }} → {{ B.name }}</code> 共有 <strong class="big">{{ count }}</strong> 个函数：
        <span v-html="formulaHtml" />
      </div>
      <p class="explain">{{ explanation }}</p>
    </div>

    <div v-if="count === 0" class="nofun">
      <svg viewBox="0 0 200 110" class="nofun-svg">
        <rect x="14" y="10" width="64" height="90" rx="26" class="set" />
        <rect x="122" y="10" width="64" height="90" rx="26" class="set" />
        <g v-for="(x, i) in A.elems" :key="i">
          <circle cx="46" :cy="55 - (A.elems.length - 1) * 13 + i * 26" r="4" class="dot" />
          <text x="40" :y="55 - (A.elems.length - 1) * 13 + i * 26" text-anchor="end" dominant-baseline="middle" class="el">{{ x }}</text>
          <line x1="52" :y1="55 - (A.elems.length - 1) * 13 + i * 26" x2="112" y2="55" class="lost" />
          <text x="116" y="58" class="q">?</text>
        </g>
        <text x="154" y="59" text-anchor="middle" class="emptyset">∅</text>
      </svg>
      <p>没有函数。在 Lean 中，这对应一条定理：给我一个 <code>{{ A.name }} → Empty</code>，我就能推出矛盾（<code>nomatch f x</code>）。</p>
    </div>

    <div v-else class="grid">
      <div
        v-for="(c, k) in cards"
        :key="k"
        :class="['card', { on: picked === k }]"
        @click="picked = picked === k ? null : k"
      >
        <svg :viewBox="`0 0 180 ${layout(c.vals).h}`" class="mini">
          <defs>
            <marker :id="`ch12-ah-${k}`" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">
              <path d="M0,0 L10,5 L0,10 z" fill="context-stroke" />
            </marker>
          </defs>
          <rect x="8" y="6" width="74" :height="layout(c.vals).h - 12" rx="14" class="set" />
          <rect x="98" y="6" width="74" :height="layout(c.vals).h - 12" rx="14" class="set" />
          <text v-if="!A.elems.length" x="45" :y="layout(c.vals).h / 2 + 1" text-anchor="middle" dominant-baseline="middle" class="emptyset">∅</text>
          <g v-for="(x, i) in A.elems" :key="'a' + i">
            <circle cx="64" :cy="layout(c.vals).ya(i)" r="3.5" class="dot" />
            <text x="57" :y="layout(c.vals).ya(i) + 1" text-anchor="end" dominant-baseline="middle" class="el">{{ x }}</text>
          </g>
          <g v-for="(y, j) in B.elems" :key="'b' + j">
            <circle cx="116" :cy="layout(c.vals).yb(j)" r="3.5" class="dot" />
            <text x="123" :y="layout(c.vals).yb(j) + 1" dominant-baseline="middle" class="el">{{ y }}</text>
          </g>
          <line
            v-for="(l, i) in layout(c.vals).lines"
            :key="'l' + i"
            x1="68"
            :y1="l.y1"
            x2="111"
            :y2="l.y2"
            class="map"
            :marker-end="`url(#ch12-ah-${k})`"
          />
        </svg>
        <div class="cname">{{ c.name || `函数 #${k + 1}` }}</div>
        <code class="clean">{{ c.lean }}</code>
      </div>
    </div>
  </div>
</template>

<style scoped>
.hint {
  margin: 0 0 10px;
  font-size: 13px;
  color: var(--vp-c-text-2);
  line-height: 1.7;
}
.pickers {
  display: flex;
  flex-direction: column;
  gap: 6px;
}
.prow {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
  align-items: center;
}
.plabel {
  font-size: 13px;
  color: var(--vp-c-text-2);
  min-width: 82px;
}
.presets .ctfp-btn {
  font-size: 12px;
  padding: 2px 10px;
}
.summary {
  margin: 14px 0 10px;
  padding: 10px 14px;
  border-radius: 8px;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
}
.formula {
  font-size: 15px;
  overflow-x: auto;
}
.big {
  font-size: 20px;
  color: var(--vp-c-brand-1);
}
.explain {
  margin: 6px 0 0;
  font-size: 13px;
  color: var(--vp-c-text-2);
  line-height: 1.7;
}
.grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(170px, 1fr));
  gap: 10px;
}
.card {
  border: 1px solid var(--vp-c-divider);
  border-radius: 10px;
  background: var(--vp-c-bg);
  padding: 6px 8px 8px;
  cursor: pointer;
  transition: border-color 0.2s, box-shadow 0.2s;
  min-width: 0;
}
.card:hover {
  border-color: var(--vp-c-brand-2);
}
.card.on {
  border-color: var(--vp-c-brand-1);
  box-shadow: 0 0 0 2px var(--vp-c-brand-soft);
}
.mini {
  width: 100%;
  height: auto;
  display: block;
}
.set {
  fill: var(--vp-c-bg-soft);
  stroke: var(--vp-c-divider);
}
.dot {
  fill: var(--vp-c-text-1);
}
.el {
  font-family: var(--vp-font-family-mono);
  font-size: 11px;
  fill: var(--vp-c-text-1);
}
.emptyset {
  font-size: 18px;
  fill: var(--vp-c-text-3);
}
.map {
  stroke: var(--vp-c-brand-1);
  stroke-width: 1.6;
}
.card.on .map {
  stroke-width: 2.4;
}
.cname {
  font-size: 12.5px;
  font-weight: 600;
  margin-top: 2px;
  color: var(--vp-c-text-1);
}
.clean {
  display: block;
  font-size: 11px !important;
  margin-top: 3px;
  white-space: normal;
  word-break: break-word;
  color: var(--vp-c-text-2);
}
.nofun {
  text-align: center;
  font-size: 13px;
  color: var(--vp-c-text-2);
}
.nofun-svg {
  width: 220px;
  max-width: 100%;
}
.lost {
  stroke: var(--vp-c-danger-1);
  stroke-width: 1.5;
  stroke-dasharray: 4 3;
}
.q {
  fill: var(--vp-c-danger-1);
  font-size: 14px;
  font-weight: 700;
}
</style>
