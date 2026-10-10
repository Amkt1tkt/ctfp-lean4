<script setup>
// 自然性方块（以及水平复合方块）的逐格演示：两条路径的中间值逐步出现，最后在右下角汇合（或分道扬镳）。
import { computed, ref, watch, onBeforeUnmount } from 'vue'

const props = defineProps({ mode: { type: String, default: 'naturality' } })
const horizontal = computed(() => props.mode === 'horizontal')

// ---------- 值的表示与 Lean 风格的打印 ----------
const NONE = { tag: 'none' }
const some = (v) => ({ tag: 'some', v })
const konst = (v) => ({ tag: 'const', v })
const str = (v) => ({ tag: 'str', v })

function fmt(v) {
  if (Array.isArray(v)) return `[${v.map(fmt).join(', ')}]`
  if (v === true || v === false) return String(v)
  if (typeof v === 'number') return String(v)
  if (v.tag === 'str') return `"${v.v}"`
  if (v.tag === 'none') return 'none'
  if (v.tag === 'const') return `⟨${v.v}⟩`
  return `some ${wrap(fmt(v.v))}`
}
const wrap = (s) => (s.startsWith('some ') ? `(${s})` : s)
const same = (a, b) => fmt(a) === fmt(b)

const listMap = (f, xs) => xs.map(f)
const optMap = (f, o) => (o.tag === 'none' ? NONE : some(f(o.v)))
const head = (xs) => (xs.length ? some(xs[0]) : NONE)
const last = (xs) => (xs.length ? some(xs[xs.length - 1]) : NONE)

// ---------- 自然性模式 ----------
const funcs = [
  { id: 'toString', name: 'toString', b: 'String', fn: (n) => str(String(n)) },
  { id: 'double', name: '(· * 2)', b: 'Nat', fn: (n) => n * 2 },
  { id: 'isEven', name: '(· % 2 == 0)', b: 'Bool', fn: (n) => n % 2 === 0 },
]
const trans = [
  { id: 'safeHead', name: 'safeHead', G: 'Option', Gmap: optMap, eta: (xs) => head(xs) },
  { id: 'reverse', name: 'List.reverse', G: 'List', Gmap: listMap, eta: (xs) => [...xs].reverse() },
  { id: 'length', name: 'length', G: 'Const Int', Gmap: (_f, c) => c, eta: (xs) => konst(xs.length) },
  {
    id: 'weird', name: 'weird', G: 'Option', Gmap: optMap, fake: true,
    eta: (xs, ty) => (ty === 'String' ? NONE : head(xs)),
  },
]
const inputs = [[3, 1, 2], [], [7], [5, 8, 13, 21]]

// ---------- 水平复合模式 ----------
const pickers = [
  { id: 'head', name: 'safeHead', fn: head },
  { id: 'last', name: 'last', fn: last },
]
const nestedInputs = [[[1, 2], [], [3]], [[], [4, 5]], [], [[6]], [[7, 8, 9], [10]]]

const fSel = ref('toString')
const tSel = ref('safeHead')
const inSel = ref(0)
const aSel = ref('head')
const bSel = ref('head')
const nSel = ref(0)

const sc = computed(() => {
  if (horizontal.value) {
    const al = pickers.find((p) => p.id === aSel.value)
    const be = pickers.find((p) => p.id === bSel.value)
    const x = nestedInputs[nSel.value]
    const tr = be.fn(x)
    const bl = x.map(al.fn)
    const brA = optMap(al.fn, tr)
    const brB = be.fn(bl)
    return {
      types: ['List (List Nat)', 'Option (List Nat)', 'List (Option Nat)', 'Option (Option Nat)'],
      vals: { tl: x, tr, bl, brA, brB },
      edges: {
        top: [be.name, 'β_{F a}'], right: [`Option.map ${al.name}`, "G' α_a"],
        left: [`List.map ${al.name}`, 'G α_a'], bottom: [be.name, "β_{F' a}"],
      },
      steps: [
        `上边 β_{F a}：把 ${be.name} 用在外层列表上：${be.name} ${fmt(x)} = ${fmt(tr)}`,
        `左边 G α_a：把 ${al.name} 用在每个内层列表上：List.map ${al.name} ${fmt(x)} = ${fmt(bl)}`,
        `右边 G' α_a：Option.map ${al.name} ${wrap(fmt(tr))} = ${fmt(brA)}`,
        `下边 β_{F' a}：${be.name} ${wrap(fmt(bl))} = ${fmt(brB)}`,
      ],
      pathA: "路径①  G' α_a ∘ β_{F a}（先外层，后内层）",
      pathB: "路径②  β_{F' a} ∘ G α_a（先内层，后外层）",
      okText: '两条路径汇合到同一个值：这就是水平复合 (β ∘ α)_a 在这个输入上的结果。',
      badText: '',
    }
  }
  const f = funcs.find((x) => x.id === fSel.value)
  const t = trans.find((x) => x.id === tSel.value)
  const xs = inputs[inSel.value]
  const tr = t.eta(xs, 'Nat')
  const bl = listMap(f.fn, xs)
  const brA = t.Gmap(f.fn, tr)
  const brB = t.eta(bl, f.b)
  const Gmapname = t.G === 'Option' ? 'Option.map' : t.G === 'List' ? 'List.map' : 'Functor.map'
  return {
    types: [`List Nat`, `${t.G} Nat`, `List ${f.b}`, `${t.G} ${f.b}`],
    vals: { tl: xs, tr, bl, brA, brB },
    edges: {
      top: [t.name, 'η_a'], right: [`${Gmapname} ${f.name}`, 'G f'],
      left: [`List.map ${f.name}`, 'F f'], bottom: [t.name, 'η_b'],
    },
    steps: [
      `上边 η_a：${t.name} ${fmt(xs)} = ${fmt(tr)}`,
      `左边 F f：List.map ${f.name} ${fmt(xs)} = ${fmt(bl)}`,
      `右边 G f：${Gmapname} ${f.name} ${wrap(fmt(tr))} = ${fmt(brA)}` +
        (t.G === 'Const Int' ? '（Const 的 map 什么也不做）' : ''),
      `下边 η_b：${t.name} ${wrap(fmt(bl))} = ${fmt(brB)}`,
    ],
    pathA: '路径①  G f ∘ η_a（先换容器，再改内容）',
    pathB: '路径②  η_b ∘ F f（先改内容，再换容器）',
    okText: t.fake
      ? '这次侥幸相等——可自然性要求对所有 f 都成立。换成 toString 试试。'
      : '两条路径汇合到同一个值：自然性方块交换。',
    badText: '两条路径得到了不同的值：方块不交换，weird 不是自然变换！它偷看了元素的类型。',
  }
})

// ---------- 逐步播放 ----------
const step = ref(0) // 0..5
const dot = ref(null) // { x, y, color }
let raf = 0

const W = 720
const H = 340
const BW = 212
const C = { tl: [182, 64], tr: [516, 64], bl: [182, 266], br: [516, 266] }
const BH = 58
const BRH = 84
const segs = {
  top: [[C.tl[0] + BW / 2, C.tl[1]], [C.tr[0] - BW / 2, C.tr[1]]],
  right: [[C.tr[0], C.tr[1] + BH / 2], [C.br[0], C.br[1] - BRH / 2]],
  left: [[C.tl[0], C.tl[1] + BH / 2], [C.bl[0], C.bl[1] - BH / 2]],
  bottom: [[C.bl[0] + BW / 2, C.bl[1]], [C.br[0] - BW / 2, C.br[1]]],
}
const order = ['top', 'left', 'right', 'bottom'] // 第 1~4 步各走一条边
const colorA = 'var(--vp-c-brand-1)'
const colorB = 'var(--vp-c-warning-1)'
const edgeColor = { top: colorA, right: colorA, left: colorB, bottom: colorB }

const equal = computed(() => same(sc.value.vals.brA, sc.value.vals.brB))
const shown = (k) => {
  const need = { tl: 0, tr: 1, bl: 2, brA: 3, brB: 4 }[k]
  return step.value >= need
}
const lit = (e) => step.value > order.indexOf(e)

function animate(edge, done) {
  cancelAnimationFrame(raf)
  const [[x0, y0], [x1, y1]] = segs[edge]
  const t0 = performance.now()
  const dur = 650
  const tick = (now) => {
    const t = Math.min(1, (now - t0) / dur)
    const e = t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2
    dot.value = { x: x0 + (x1 - x0) * e, y: y0 + (y1 - y0) * e, color: edgeColor[edge] }
    if (t < 1) raf = requestAnimationFrame(tick)
    else {
      dot.value = null
      done()
    }
  }
  raf = requestAnimationFrame(tick)
}

const busy = ref(false)
function next(chain = false) {
  if (busy.value || step.value >= 5) return
  if (step.value === 4) {
    step.value = 5
    return
  }
  busy.value = true
  animate(order[step.value], () => {
    step.value++
    busy.value = false
    if (chain && step.value < 5) setTimeout(() => next(true), 180)
  })
}
function playAll() {
  if (step.value >= 5) reset()
  next(true)
}
function reset() {
  cancelAnimationFrame(raf)
  busy.value = false
  dot.value = null
  step.value = 0
}
watch([fSel, tSel, inSel, aSel, bSel, nSel], reset)
onBeforeUnmount(() => cancelAnimationFrame(raf))

const mid = (e) => {
  const [[x0, y0], [x1, y1]] = segs[e]
  return [(x0 + x1) / 2, (y0 + y1) / 2]
}
</script>

<template>
  <div class="ctfp-widget ns">
    <div class="ctfp-widget-title">
      {{ horizontal ? '水平复合方块：G(F a) 到 G′(F′ a) 的两条路' : '自然性方块逐格演示' }}
    </div>

    <div class="ns-controls">
      <template v-if="!horizontal">
        <label>自然变换 η：
          <select v-model="tSel">
            <option v-for="t in trans" :key="t.id" :value="t.id">
              {{ t.name }} : List ⟹ {{ t.G }}{{ t.fake ? '（冒牌货）' : '' }}
            </option>
          </select>
        </label>
        <label>函数 f：
          <select v-model="fSel">
            <option v-for="f in funcs" :key="f.id" :value="f.id">{{ f.name }} : Nat → {{ f.b }}</option>
          </select>
        </label>
        <label>输入：
          <select v-model.number="inSel">
            <option v-for="(x, i) in inputs" :key="i" :value="i">{{ fmt(x) }}</option>
          </select>
        </label>
      </template>
      <template v-else>
        <label>α : List ⟹ Option
          <select v-model="aSel">
            <option v-for="p in pickers" :key="p.id" :value="p.id">{{ p.name }}</option>
          </select>
        </label>
        <label>β : List ⟹ Option
          <select v-model="bSel">
            <option v-for="p in pickers" :key="p.id" :value="p.id">{{ p.name }}</option>
          </select>
        </label>
        <label>输入：
          <select v-model.number="nSel">
            <option v-for="(x, i) in nestedInputs" :key="i" :value="i">{{ fmt(x) }}</option>
          </select>
        </label>
      </template>
    </div>

    <svg :viewBox="`0 0 ${W} ${H}`" class="ns-svg" role="img">
      <defs>
        <marker id="ns-ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" orient="auto">
          <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
        </marker>
      </defs>

      <!-- 边 -->
      <g v-for="e in order" :key="e">
        <line
          :x1="segs[e][0][0]" :y1="segs[e][0][1]" :x2="segs[e][1][0]" :y2="segs[e][1][1]"
          :stroke="lit(e) ? edgeColor[e] : 'var(--vp-c-text-3)'" :stroke-width="lit(e) ? 3 : 1.6"
          marker-end="url(#ns-ah)"
        />
        <text
          v-if="e === 'top' || e === 'bottom'"
          :x="mid(e)[0]" :y="mid(e)[1] + (e === 'top' ? -22 : 22)" text-anchor="middle"
          class="ns-elabel" :fill="lit(e) ? edgeColor[e] : 'var(--vp-c-text-1)'"
        >{{ sc.edges[e][0] }}</text>
        <text
          v-if="e === 'top' || e === 'bottom'"
          :x="mid(e)[0]" :y="mid(e)[1] + (e === 'top' ? -7 : 37)" text-anchor="middle" class="ns-sym"
        >{{ sc.edges[e][1] }}</text>
        <text
          v-if="e === 'left' || e === 'right'"
          :x="mid(e)[0] + (e === 'left' ? -10 : 10)" :y="mid(e)[1]" :text-anchor="e === 'left' ? 'end' : 'start'"
          class="ns-elabel" :fill="lit(e) ? edgeColor[e] : 'var(--vp-c-text-1)'"
        >{{ sc.edges[e][0] }}</text>
        <text
          v-if="e === 'left' || e === 'right'"
          :x="mid(e)[0] + (e === 'left' ? -10 : 10)" :y="mid(e)[1] + 16" :text-anchor="e === 'left' ? 'end' : 'start'"
          class="ns-sym"
        >{{ sc.edges[e][1] }}</text>
      </g>

      <!-- 四个角 -->
      <g v-for="k in ['tl', 'tr', 'bl']" :key="k">
        <rect
          :x="C[k][0] - BW / 2" :y="C[k][1] - BH / 2" :width="BW" :height="BH" rx="9"
          class="ns-box" :class="{ on: shown(k) }"
        />
        <text :x="C[k][0]" :y="C[k][1] - 7" text-anchor="middle" class="ns-type">
          {{ sc.types[['tl', 'tr', 'bl'].indexOf(k)] }}
        </text>
        <text :x="C[k][0]" :y="C[k][1] + 15" text-anchor="middle" class="ns-val"
          :fill="k === 'tr' ? colorA : k === 'bl' ? colorB : 'var(--vp-c-text-1)'">
          {{ shown(k) ? fmt(sc.vals[k]) : '?' }}
        </text>
      </g>
      <g>
        <rect
          :x="C.br[0] - BW / 2" :y="C.br[1] - BRH / 2" :width="BW" :height="BRH" rx="9"
          class="ns-box" :class="{ on: step >= 3, ok: step >= 5 && equal, bad: step >= 5 && !equal }"
        />
        <text :x="C.br[0]" :y="C.br[1] - 20" text-anchor="middle" class="ns-type">{{ sc.types[3] }}</text>
        <text :x="C.br[0]" :y="C.br[1] + 4" text-anchor="middle" class="ns-val" :fill="colorA">
          ① {{ shown('brA') ? fmt(sc.vals.brA) : '?' }}
        </text>
        <text :x="C.br[0]" :y="C.br[1] + 26" text-anchor="middle" class="ns-val" :fill="colorB">
          ② {{ shown('brB') ? fmt(sc.vals.brB) : '?' }}
        </text>
      </g>
      <text v-if="step >= 5" :x="C.br[0]" :y="C.br[1] + BRH / 2 + 22" text-anchor="middle"
        class="ns-verdict" :class="equal ? 'ok' : 'bad'">
        {{ equal ? '① = ②' : '① ≠ ②' }}
      </text>

      <circle v-if="dot" :cx="dot.x" :cy="dot.y" r="7" :fill="dot.color" />
    </svg>

    <div class="ns-buttons">
      <button class="ctfp-btn" :disabled="busy || step >= 5" @click="next()">下一步</button>
      <button class="ctfp-btn" :disabled="busy" @click="playAll">全部播放</button>
      <button class="ctfp-btn" @click="reset">重置</button>
    </div>

    <div class="ns-legend">
      <span :style="{ color: colorA }">{{ sc.pathA }}</span>
      <span :style="{ color: colorB }">{{ sc.pathB }}</span>
    </div>

    <ol class="ns-log">
      <li v-for="(s, i) in sc.steps" :key="i" v-show="step > i" :style="{ color: i === 0 || i === 2 ? colorA : colorB }">
        <code>{{ s }}</code>
      </li>
      <li v-show="step >= 5" class="ns-final" :class="equal ? 'ok' : 'bad'">
        {{ equal ? sc.okText : sc.badText }}
      </li>
    </ol>
    <div v-if="step === 0" class="ns-hint">
      点“下一步”逐格前进：上边与右边是路径①，左边与下边是路径②。
    </div>
  </div>
</template>

<style scoped>
.ns { max-width: 100%; overflow: hidden; }
.ns-controls { display: flex; flex-wrap: wrap; gap: 8px 16px; font-size: 13px; margin-bottom: 6px; }
.ns-controls select {
  margin-left: 4px; padding: 2px 6px; border: 1px solid var(--vp-c-divider); border-radius: 6px;
  background: var(--vp-c-bg); color: var(--vp-c-text-1); font-family: var(--vp-font-family-mono); font-size: 12px;
}
.ns-svg { width: 100%; max-width: 720px; display: block; margin: 0 auto; }
.ns-box { fill: var(--vp-c-bg); stroke: var(--vp-c-divider); stroke-width: 1.5; transition: all 0.3s; }
.ns-box.on { stroke: var(--vp-c-text-2); }
.ns-box.ok { stroke: var(--vp-c-success-1, #18794e); stroke-width: 3; }
.ns-box.bad { stroke: var(--vp-c-danger-1); stroke-width: 3; }
.ns-type { font-size: 12px; fill: var(--vp-c-text-2); font-family: var(--vp-font-family-mono); }
.ns-val { font-size: 14px; font-family: var(--vp-font-family-mono); font-weight: 600; }
.ns-elabel { font-size: 13px; font-family: var(--vp-font-family-mono); }
.ns-sym { font-size: 11px; fill: var(--vp-c-text-3); font-style: italic; }
.ns-verdict { font-size: 15px; font-weight: 700; }
.ns-verdict.ok { fill: var(--vp-c-success-1, #18794e); }
.ns-verdict.bad { fill: var(--vp-c-danger-1); }
.ns-buttons { display: flex; gap: 8px; justify-content: center; margin: 4px 0 8px; }
.ns-buttons button:disabled { opacity: 0.45; cursor: default; }
.ns-legend { display: flex; flex-wrap: wrap; gap: 4px 18px; justify-content: center; font-size: 12.5px; }
.ns-log { margin: 10px 0 0; padding-left: 22px; font-size: 13px; }
.ns-log li { margin: 2px 0; }
.ns-log code { white-space: pre-wrap; word-break: break-all; background: none; padding: 0; color: inherit; }
.ns-final { list-style: none; margin-left: -22px !important; margin-top: 6px !important; font-weight: 600; }
.ns-final.ok { color: var(--vp-c-success-1, #18794e); }
.ns-final.bad { color: var(--vp-c-danger-1); }
.ns-hint { text-align: center; font-size: 12.5px; color: var(--vp-c-text-2); margin-top: 4px; }
</style>
