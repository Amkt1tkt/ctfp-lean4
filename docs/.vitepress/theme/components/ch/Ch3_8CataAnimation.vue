<script setup>
import { ref, computed, onBeforeUnmount } from 'vue'

const lit = (n) => ({ op: 'lit', n, kids: [] })
const add = (a, b) => ({ op: 'add', kids: [a, b] })
const mul = (a, b) => ({ op: 'mul', kids: [a, b] })
const neg = (a) => ({ op: 'neg', kids: [a] })

const exprs = [
  { name: '(2 + 3) * 4', tree: () => mul(add(lit(2), lit(3)), lit(4)) },
  { name: '(1 + 2) * (3 + 4)', tree: () => mul(add(lit(1), lit(2)), add(lit(3), lit(4))) },
  { name: '-(5 * (2 + 1)) + 7', tree: () => add(neg(mul(lit(5), add(lit(2), lit(1)))), lit(7)) },
]

const fmt = {
  lit: (n) => `lit ${n}`,
  add: (a, b) => `add ${a} ${b}`,
  mul: (a, b) => `mul ${a} ${b}`,
  neg: (a) => `neg ${a}`,
}

const algebras = [
  {
    key: 'eval', name: '求值', carrier: 'Int',
    lit: (n) => n, add: (a, b) => a + b, mul: (a, b) => a * b, neg: (a) => -a,
    show: (v) => String(v),
    lean: ['def evalAlg : ExprF Int → Int', '  | .lit n   => n', '  | .add x y => x + y', '  | .mul x y => x * y', '  | .neg x   => -x'],
  },
  {
    key: 'print', name: '打印', carrier: 'String',
    lit: (n) => String(n), add: (a, b) => `(${a} + ${b})`, mul: (a, b) => `${a} * ${b}`, neg: (a) => `-(${a})`,
    show: (v) => JSON.stringify(v),
    lean: ['def showAlg : ExprF String → String', '  | .lit n   => toString n', '  | .add x y => "(" ++ x ++ " + " ++ y ++ ")"', '  | .mul x y => x ++ " * " ++ y', '  | .neg x   => "-(" ++ x ++ ")"'],
  },
  {
    key: 'count', name: '数节点', carrier: 'Nat',
    lit: () => 1, add: (a, b) => a + b + 1, mul: (a, b) => a + b + 1, neg: (a) => a + 1,
    show: (v) => String(v),
    lean: ['def countAlg : ExprF Nat → Nat', '  | .lit _   => 1', '  | .add x y => x + y + 1', '  | .mul x y => x + y + 1', '  | .neg x   => x + 1'],
  },
  {
    key: 'depth', name: '深度', carrier: 'Nat',
    lit: () => 1, add: (a, b) => Math.max(a, b) + 1, mul: (a, b) => Math.max(a, b) + 1, neg: (a) => a + 1,
    show: (v) => String(v),
    lean: ['def depthAlg : ExprF Nat → Nat', '  | .lit _   => 1', '  | .add x y => max x y + 1', '  | .mul x y => max x y + 1', '  | .neg x   => x + 1'],
  },
]

const exprIdx = ref(0)
const algIdx = ref(0)
const step = ref(0)
let timer = null

const layout = computed(() => {
  const root = exprs[exprIdx.value].tree()
  const nodes = []
  let leaf = 0
  let maxDepth = 0
  const walk = (t, depth) => {
    maxDepth = Math.max(maxDepth, depth)
    const kids = t.kids.map((k) => walk(k, depth + 1))
    const x = kids.length ? kids.reduce((s, k) => s + k.x, 0) / kids.length : leaf++
    const node = { ...t, kids, x, depth, id: nodes.length }
    nodes.push(node)
    return node
  }
  walk(root, 0)
  return { nodes, leaves: leaf, maxDepth }
})

const order = computed(() => layout.value.nodes)
const alg = computed(() => algebras[algIdx.value])

const values = computed(() => {
  const v = {}
  const a = alg.value
  order.value.slice(0, step.value).forEach((n) => {
    const ks = n.kids.map((k) => v[k.id])
    v[n.id] = n.op === 'lit' ? a.lit(n.n) : a[n.op](...ks)
  })
  return v
})

const current = computed(() => {
  if (step.value === 0) return null
  const n = order.value[step.value - 1]
  const a = alg.value
  const ks = n.kids.map((k) => a.show(values.value[k.id]))
  const layer = n.op === 'lit' ? fmt.lit(n.n) : fmt[n.op](...ks)
  return { layer, result: a.show(values.value[n.id]), op: n.op }
})

const done = computed(() => step.value >= order.value.length)
const W = 110, H = 78, PADX = 50, PADY = 34
const svgW = computed(() => Math.max(1, layout.value.leaves - 1) * W + PADX * 2)
const svgH = computed(() => layout.value.maxDepth * H + PADY * 2 + 26)
const pos = (n) => ({ x: PADX + n.x * W, y: PADY + n.depth * H })
const label = (n) => (n.op === 'lit' ? String(n.n) : { add: '+', mul: '×', neg: '−' }[n.op])
const isActive = (n) => step.value > 0 && order.value[step.value - 1].id === n.id
const isDone = (n) => n.id in values.value

function stopAuto() {
  if (timer) clearInterval(timer)
  timer = null
}
function next() {
  if (!done.value) step.value++
  else stopAuto()
}
function reset() {
  stopAuto()
  step.value = 0
}
function auto() {
  if (timer) return stopAuto()
  if (done.value) step.value = 0
  timer = setInterval(() => {
    if (done.value) stopAuto()
    else step.value++
  }, 900)
}
function pickExpr(i) {
  exprIdx.value = i
  reset()
}
function pickAlg(i) {
  algIdx.value = i
}
onBeforeUnmount(stopAuto)
</script>

<template>
  <div class="ctfp-widget cata">
    <div class="ctfp-widget-title">卡塔态射动画：同一棵树，不同的代数</div>
    <p class="hint">
      <code>cata alg</code> 自底向上地折叠表达式树：每一步只处理一个节点，此时它的孩子已被替换成载体中的值，
      所以代数 <code>alg</code> 面对的只是“一层” <code>ExprF a</code>。随时切换代数，看同一个递归结构的不同解释。
    </p>
    <div class="row">
      <span class="lbl">表达式：</span>
      <button v-for="(e, i) in exprs" :key="e.name" class="ctfp-btn" :class="{ on: i === exprIdx }" @click="pickExpr(i)">{{ e.name }}</button>
    </div>
    <div class="row">
      <span class="lbl">代数：</span>
      <button v-for="(a, i) in algebras" :key="a.key" class="ctfp-btn" :class="{ on: i === algIdx }" @click="pickAlg(i)">
        {{ a.name }}（载体 {{ a.carrier }}）
      </button>
    </div>
    <div class="stage">
      <svg :viewBox="`0 0 ${svgW} ${svgH}`" :width="svgW" class="tree">
        <g v-for="n in order" :key="'e' + n.id">
          <line v-for="k in n.kids" :key="k.id" :x1="pos(n).x" :y1="pos(n).y" :x2="pos(k).x" :y2="pos(k).y" class="edge" :class="{ folded: isDone(k) }" />
        </g>
        <g v-for="n in order" :key="'n' + n.id" :transform="`translate(${pos(n).x},${pos(n).y})`">
          <circle r="19" class="node" :class="{ active: isActive(n), done: isDone(n) && !isActive(n) }" />
          <text class="op" text-anchor="middle" dy="5">{{ label(n) }}</text>
          <text v-if="isDone(n)" class="val" :class="{ active: isActive(n) }" text-anchor="middle" dy="36">{{ alg.show(values[n.id]) }}</text>
        </g>
      </svg>
    </div>
    <div class="status">
      <template v-if="current">
        <span class="muted">第 {{ step }} / {{ order.length }} 步：</span>
        <code>alg ({{ current.layer }}) = {{ current.result }}</code>
        <span v-if="done" class="ok">折叠完成：cata alg 的结果就是根节点的值。</span>
      </template>
      <span v-else class="muted">还没有开始。点“下一步”从最左下的叶子开始。</span>
    </div>
    <div class="row">
      <button class="ctfp-btn" :disabled="done" @click="next">下一步</button>
      <button class="ctfp-btn" @click="auto">自动播放 / 暂停</button>
      <button class="ctfp-btn" @click="reset">重置</button>
    </div>
    <pre class="code"><code>{{ alg.lean.join('\n') }}</code></pre>
  </div>
</template>

<style scoped>
.cata { max-width: 100%; }
.hint { font-size: 0.9em; color: var(--vp-c-text-2); margin: 0.3em 0 0.6em; }
.row { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin: 6px 0; }
.lbl { font-size: 0.9em; color: var(--vp-c-text-2); }
.ctfp-btn.on { background: var(--vp-c-brand-1); color: var(--vp-c-white, #fff); border-color: var(--vp-c-brand-1); }
.stage { overflow-x: auto; display: flex; justify-content: center; padding: 6px 0; }
.tree { max-width: 100%; height: auto; }
.edge { stroke: var(--vp-c-text-3); stroke-width: 1.6; }
.edge.folded { stroke: var(--vp-c-brand-1); stroke-dasharray: 4 4; }
.node { fill: var(--vp-c-bg-soft); stroke: var(--vp-c-text-2); stroke-width: 1.6; transition: all 0.3s; }
.node.done { fill: var(--vp-c-brand-soft); stroke: var(--vp-c-brand-1); }
.node.active { fill: var(--vp-c-warning-soft); stroke: var(--vp-c-warning-1); stroke-width: 3; }
.op { font-family: var(--vp-font-family-mono); font-size: 15px; fill: var(--vp-c-text-1); font-weight: 600; }
.val { font-family: var(--vp-font-family-mono); font-size: 12px; fill: var(--vp-c-brand-1); }
.val.active { fill: var(--vp-c-warning-1); font-weight: 700; }
.status { min-height: 2.6em; font-size: 0.92em; margin: 4px 0; word-break: break-all; }
.muted { color: var(--vp-c-text-2); }
.ok { display: block; color: var(--vp-c-success-1, #18794e); margin-top: 2px; }
.code { background: var(--vp-c-bg-soft); border-radius: 6px; padding: 8px 12px; font-size: 0.85em; overflow-x: auto; margin: 8px 0 0; }
</style>
