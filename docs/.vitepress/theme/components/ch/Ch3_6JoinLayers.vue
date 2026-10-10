<script setup>
// μ 把两层压成一层：在 List / Option 上逐步演示 join 的结合律与单位律。
import { ref, computed, watch } from 'vue'

const functor = ref('list') // 'list' | 'option'
const law = ref('assoc') // 'assoc' | 'unit'
const exampleIdx = ref(0)
const randomSeed = ref(0)

// ---------- 值的表示 ----------
// { t: 'leaf', v } | { t: 'list', L, items } | { t: 'some', L, c } | { t: 'none', L }
// L 是“这一层是谁”：1/2/3 为最初的三层，'e' 为 η 新加的一层。
const leaf = (v) => ({ t: 'leaf', v })
const list = (L, items) => ({ t: 'list', L, items })
const some = (L, c) => ({ t: 'some', L, c })
const none = (L) => ({ t: 'none', L })

function lettersFrom(shape) {
  // shape: 嵌套数组（叶子为 0）→ 带字母的节点，按出现顺序编号 a, b, c…
  let k = 0
  const go = (s, depth, maxDepth) =>
    depth === maxDepth ? leaf(String.fromCharCode(97 + k++)) : list(depth + 1, s.map((x) => go(x, depth + 1, maxDepth)))
  return (s, maxDepth) => {
    k = 0
    return go(s, 0, maxDepth)
  }
}
const build = lettersFrom()

const listAssocPresets = [
  [[[0, 0], [0]], [[0]], [[], [0, 0]]],
  [[[0]], [], [[0, 0], [0]]],
  [[[0, 0, 0]], [[0], [], [0]]],
]
const listUnitPresets = [[0, 0, 0], [0], []]

const optionAssocPresets = [
  some(1, some(2, some(3, leaf('a')))),
  some(1, some(2, none(3))),
  some(1, none(2)),
  none(1),
]
const optionUnitPresets = [some(1, leaf('a')), none(1)]

function rng(seed) {
  let s = seed * 9301 + 49297
  return () => {
    s = (s * 9301 + 49297) % 233280
    return s / 233280
  }
}
function randomListShape(depth, seed) {
  const r = rng(seed)
  let budget = 8
  const go = (d) => {
    if (d === depth) return 0
    const n = d === 0 ? 1 + Math.floor(r() * 3) : Math.floor(r() * 3)
    const out = []
    for (let i = 0; i < n; i++) {
      if (d === depth - 1) {
        if (budget <= 0) break
        budget--
      }
      out.push(go(d + 1))
    }
    return out
  }
  return go(0)
}

const examples = computed(() => {
  if (functor.value === 'list') {
    const presets = law.value === 'assoc' ? listAssocPresets : listUnitPresets
    const depth = law.value === 'assoc' ? 3 : 1
    const items = presets.map((p) => build(p, depth))
    if (randomSeed.value) items.push(build(randomListShape(depth, randomSeed.value), depth))
    return items
  }
  return law.value === 'assoc' ? optionAssocPresets : optionUnitPresets
})

// ---------- 操作 ----------
function joinNode(n, keep) {
  if (n.t === 'list') return list(keep, n.items.flatMap((c) => c.items))
  if (n.t === 'none') return none(keep)
  if (n.c.t === 'none') return none(keep)
  return some(keep, n.c.c)
}
function mapNode(n, f) {
  if (n.t === 'list') return list(n.L, n.items.map(f))
  if (n.t === 'none') return n
  return some(n.L, f(n.c))
}
function pureNode(x, L) {
  return functor.value === 'list' ? list(L, [x]) : some(L, x)
}

const isList = computed(() => functor.value === 'list')

const paths = computed(() => {
  const L = isList.value
  if (law.value === 'assoc') {
    return [
      {
        name: '路径一：μ ∘ T，再 μ',
        hint: '先压外面两层',
        color: 'var(--vp-c-brand-1)',
        steps: [
          { label: 'μ ∘ T（分量 μ_Ta）', lean: L ? 'List.flatten xsss' : 'Option.join x', removes: 2,
            op: (n) => joinNode(n, 1) },
          { label: 'μ（分量 μ_a）', lean: L ? 'List.flatten _' : 'Option.join _', removes: 3,
            op: (n) => joinNode(n, 1) },
        ],
      },
      {
        name: '路径二：T ∘ μ，再 μ',
        hint: '先压里面两层',
        color: 'var(--vp-c-success-1, #18794e)',
        steps: [
          { label: 'T ∘ μ（分量 T μ_a）', lean: L ? 'List.map List.flatten xsss' : 'Option.map Option.join x', removes: 3,
            op: (n) => mapNode(n, (c) => joinNode(c, 2)) },
          { label: 'μ（分量 μ_a）', lean: L ? 'List.flatten _' : 'Option.join _', removes: 2,
            op: (n) => joinNode(n, 1) },
        ],
      },
    ]
  }
  return [
    {
      name: '路径一：η ∘ T，再 μ',
      hint: '在外面包一层',
      color: 'var(--vp-c-brand-1)',
      steps: [
        { label: 'η ∘ T（分量 η_Ta）', lean: L ? '[xs]' : 'some x', adds: true,
          op: (n) => pureNode(n, 'e') },
        { label: 'μ（分量 μ_a）', lean: L ? 'List.flatten _' : 'Option.join _', removes: 'e',
          op: (n) => joinNode(n, 1) },
      ],
    },
    {
      name: '路径二：T ∘ η，再 μ',
      hint: '在每个元素外面包一层',
      color: 'var(--vp-c-success-1, #18794e)',
      steps: [
        { label: 'T ∘ η（分量 T η_a）', lean: L ? 'List.map (fun x => [x]) xs' : 'Option.map some x', adds: true,
          op: (n) => mapNode(n, (c) => pureNode(c, 'e')) },
        { label: 'μ（分量 μ_a）', lean: L ? 'List.flatten _' : 'Option.join _', removes: 'e',
          op: (n) => joinNode(n, 1) },
      ],
    },
  ]
})

// ---------- 播放状态 ----------
// tick: 0 = 初始；每一步有两拍：奇数拍“预告”（高亮将消失的层），偶数拍“执行”。
const tick = ref(0)
const maxTick = 4
const start = computed(() => examples.value[Math.min(exampleIdx.value, examples.value.length - 1)])

const states = computed(() =>
  paths.value.map((p) => {
    const seq = [start.value]
    for (const s of p.steps) seq.push(s.op(seq[seq.length - 1]))
    return seq
  }),
)

function next() {
  if (tick.value < maxTick) tick.value++
}
function playAll() {
  tick.value = 0
  let i = 0
  const go = () => {
    if (i++ >= maxTick) return
    tick.value++
    setTimeout(go, 900)
  }
  setTimeout(go, 200)
}
function reset() {
  tick.value = 0
}
watch([functor, law], () => {
  exampleIdx.value = 0
  randomSeed.value = 0
  tick.value = 0
})
watch(exampleIdx, () => (tick.value = 0))
function randomize() {
  randomSeed.value = 1 + Math.floor(Math.random() * 100000)
  exampleIdx.value = examples.value.length - 1
  tick.value = 0
}

const stepsDone = computed(() => Math.floor(tick.value / 2))
const previewing = computed(() => tick.value % 2 === 1)

// ---------- 渲染 ----------
function tokens(n) {
  if (n.t === 'leaf') return [{ s: n.v, k: 'leaf' }]
  if (n.t === 'list') {
    const out = [{ s: '[', L: n.L, k: 'br' }]
    n.items.forEach((c, i) => {
      if (i) out.push({ s: ', ', k: 'sep' })
      out.push(...tokens(c))
    })
    out.push({ s: ']', L: n.L, k: 'br' })
    return out
  }
  if (n.t === 'none') return [{ s: 'none', L: n.L, k: 'kw' }]
  return [{ s: 'some ', L: n.L, k: 'kw' }, { s: '(', L: n.L, k: 'br' }, ...tokens(n.c), { s: ')', L: n.L, k: 'br' }]
}
const text = (n) => tokens(n).map((t) => t.s).join('')

const layerColor = {
  1: 'var(--vp-c-brand-1)',
  2: 'var(--vp-c-purple-1, #8e5cd9)',
  3: 'var(--vp-c-warning-1, #c27c0e)',
  e: 'var(--vp-c-success-1, #18794e)',
}

function rows(pi) {
  const p = paths.value[pi]
  const seq = states.value[pi]
  const out = [{ kind: 'state', node: seq[0], removes: previewing.value && stepsDone.value === 0 ? (p.steps[0].removes ?? null) : null }]
  for (let i = 0; i < p.steps.length; i++) {
    if (i >= stepsDone.value) break
    out.push({ kind: 'arrow', step: p.steps[i] })
    const pendingNext = previewing.value && stepsDone.value === i + 1 && p.steps[i + 1]
    out.push({ kind: 'state', node: seq[i + 1], removes: pendingNext ? (p.steps[i + 1].removes ?? null) : null })
  }
  if (previewing.value && stepsDone.value < p.steps.length) {
    out.push({ kind: 'arrow', step: p.steps[stepsDone.value], pending: true })
  }
  return out
}

const finished = computed(() => tick.value >= maxTick)
const same = computed(() => text(states.value[0][2]) === text(states.value[1][2]))

const layerLegend = computed(() =>
  law.value === 'assoc'
    ? [
        { L: 1, name: '第 1 层（最外）' },
        { L: 2, name: '第 2 层' },
        { L: 3, name: '第 3 层（最内）' },
      ]
    : [
        { L: 1, name: '原来的一层 T' },
        { L: 'e', name: 'η 新包上的一层' },
      ],
)
</script>

<template>
  <div class="ctfp-widget jl">
    <div class="ctfp-widget-title">μ 把两层压成一层：两条路径，同一个结果</div>
    <div class="jl-bar">
      <span class="jl-group">
        <button class="ctfp-btn" :class="{ on: functor === 'list' }" @click="functor = 'list'">T = List</button>
        <button class="ctfp-btn" :class="{ on: functor === 'option' }" @click="functor = 'option'">T = Option</button>
      </span>
      <span class="jl-group">
        <button class="ctfp-btn" :class="{ on: law === 'assoc' }" @click="law = 'assoc'">结合律（T³ → T）</button>
        <button class="ctfp-btn" :class="{ on: law === 'unit' }" @click="law = 'unit'">单位律（T → T² → T）</button>
      </span>
    </div>
    <div class="jl-bar">
      <span class="jl-label">起点：</span>
      <button
        v-for="(ex, i) in examples"
        :key="i + text(ex)"
        class="ctfp-btn jl-ex"
        :class="{ on: i === Math.min(exampleIdx, examples.length - 1) }"
        @click="exampleIdx = i"
      >
        <code>{{ text(ex) }}</code>
      </button>
      <button v-if="isList" class="ctfp-btn" @click="randomize">随机一个</button>
    </div>
    <div class="jl-legend">
      <span v-for="l in layerLegend" :key="l.L" :style="{ color: layerColor[l.L] }">■ {{ l.name }}</span>
      <span><span class="jl-vanish-demo">[ ]</span> 删除线 = 下一步要被 μ 抹掉的那层括号</span>
    </div>

    <div class="jl-cols">
      <div v-for="(p, pi) in paths" :key="pi" class="jl-col">
        <div class="jl-col-title" :style="{ color: p.color }">{{ p.name }}</div>
        <div class="jl-col-hint">{{ p.hint }}</div>
        <template v-for="(r, ri) in rows(pi)" :key="ri">
          <div v-if="r.kind === 'state'" class="jl-state">
            <code>
              <span
                v-for="(t, ti) in tokens(r.node)"
                :key="ti"
                :class="['tk', t.k, { vanish: r.removes != null && t.L !== undefined && t.L === r.removes }]"
                :style="t.L !== undefined ? { color: layerColor[t.L] } : null"
              >{{ t.s }}</span>
            </code>
          </div>
          <div v-else class="jl-arrow" :class="{ pending: r.pending }">
            <span class="jl-arrow-sym">↓</span>
            <span class="jl-arrow-label">{{ r.step.label }}</span>
            <code class="jl-arrow-lean">{{ r.step.lean }}</code>
          </div>
        </template>
      </div>
    </div>

    <div class="jl-bar jl-controls">
      <button class="ctfp-btn" :disabled="finished" @click="next">
        {{ previewing ? '执行这一步' : tick === 0 ? '开始：预告第一步' : '预告下一步' }}
      </button>
      <button class="ctfp-btn" @click="playAll">自动播放</button>
      <button class="ctfp-btn" @click="reset">重置</button>
    </div>
    <div v-if="finished" class="jl-verdict" :class="{ ok: same }">
      {{ same ? `两条路径都得到 ${text(states[0][2])}` : '结果不同？这不应该发生！' }}
      <template v-if="same && law === 'unit'">，并且就是起点本身。</template>
      <template v-else-if="same">。先压哪两层都一样，这就是结合律。</template>
    </div>
    <div v-else class="jl-tip">
      提示：点“开始”，每一步先用删除线预告哪一层括号会消失，再执行。比较左右两列。
    </div>
  </div>
</template>

<style scoped>
.jl-bar {
  display: flex;
  flex-wrap: wrap;
  gap: 8px;
  align-items: center;
  margin-bottom: 10px;
}
.jl-group {
  display: inline-flex;
  flex-wrap: wrap;
  gap: 6px;
  margin-right: 10px;
}
.jl-label {
  font-size: 13px;
  color: var(--vp-c-text-2);
}
.jl-ex code {
  background: none;
  padding: 0;
  font-size: 12px;
}
.jl-legend {
  display: flex;
  flex-wrap: wrap;
  gap: 14px;
  font-size: 12px;
  margin-bottom: 12px;
}
.jl-vanish-demo {
  color: var(--vp-c-danger-1);
  text-decoration: line-through;
}
.jl-cols {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 14px;
}
@media (max-width: 640px) {
  .jl-cols {
    grid-template-columns: 1fr;
  }
}
.jl-col {
  border: 1px solid var(--vp-c-divider);
  border-radius: 10px;
  padding: 10px 12px;
  background: var(--vp-c-bg);
  min-width: 0;
}
.jl-col-title {
  font-weight: 600;
  font-size: 14px;
}
.jl-col-hint {
  font-size: 12px;
  color: var(--vp-c-text-3);
  margin-bottom: 8px;
}
.jl-state {
  overflow-x: auto;
  padding: 4px 0;
}
.jl-state code {
  font-size: 14px;
  background: var(--vp-c-bg-soft);
  padding: 4px 8px;
  border-radius: 6px;
  white-space: normal;
  overflow-wrap: anywhere;
  display: inline-block;
}
.tk.br,
.tk.kw {
  font-weight: 700;
  transition: all 0.3s;
}
.tk.leaf {
  color: var(--vp-c-text-1);
}
.tk.sep {
  color: var(--vp-c-text-3);
}
.tk.vanish {
  color: var(--vp-c-danger-1) !important;
  text-decoration: line-through;
  opacity: 0.75;
  background: color-mix(in srgb, var(--vp-c-danger-1) 14%, transparent);
  border-radius: 3px;
}
.jl-arrow {
  display: flex;
  flex-wrap: wrap;
  align-items: baseline;
  gap: 6px;
  font-size: 12px;
  color: var(--vp-c-text-2);
  padding: 2px 0 2px 6px;
}
.jl-arrow.pending {
  opacity: 0.6;
}
.jl-arrow-sym {
  font-size: 16px;
}
.jl-arrow-lean {
  font-size: 11px;
}
.jl-controls {
  margin-top: 12px;
  margin-bottom: 4px;
}
.jl-controls button:disabled {
  opacity: 0.4;
  cursor: default;
}
.jl-verdict {
  font-size: 14px;
  padding: 8px 12px;
  border-radius: 8px;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
}
.jl-verdict.ok {
  border-color: var(--vp-c-success-1, #18794e);
  color: var(--vp-c-success-1, #18794e);
}
.jl-tip {
  font-size: 12px;
  color: var(--vp-c-text-3);
}
</style>
