<script setup>
import { ref, computed, onBeforeUnmount } from 'vue'

// goal 文本取自 Lean 4.34.1 的实际输出（在每一步之后插入 trace_state 得到）。
const PROOFS = [
  {
    key: 'imp_trans',
    title: '三段论（intro / apply / exact）',
    code: [
      'theorem imp_trans (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by',
      '  intro hp',
      '  apply hqr',
      '  apply hpq',
      '  exact hp',
    ],
    steps: [
      { lines: [0], goals: 'p q r : Prop\nhpq : p → q\nhqr : q → r\n⊢ p → r', note: '刚进入 by。定理的参数都成了横线上方的假设，横线 ⊢ 之后是要证明的目标 p → r。' },
      { lines: [1], goals: 'p q r : Prop\nhpq : p → q\nhqr : q → r\nhp : p\n⊢ r', note: '目标是“若 p 则 r”。intro hp 假设 p 成立（取名 hp，移到横线上方），目标只剩 r。' },
      { lines: [2], goals: 'p q r : Prop\nhpq : p → q\nhqr : q → r\nhp : p\n⊢ q', note: 'hqr : q → r 能产出 r。apply hqr 表示“用它来得到 r”，于是只需提供它的输入 q：目标倒退成 q。' },
      { lines: [3], goals: 'p q r : Prop\nhpq : p → q\nhqr : q → r\nhp : p\n⊢ p', note: '同理，用 hpq : p → q 得到 q，目标倒退成 p。' },
      { lines: [4], goals: '', note: 'hp 的类型正好是目标 p，exact hp 结束证明。整个证明相当于项 fun hp => hqr (hpq hp)，也就是函数复合。' },
    ],
  },
  {
    key: 'and_swap',
    title: '交换 ∧（cases / constructor）',
    code: [
      'theorem and_swap (p q : Prop) : p ∧ q → q ∧ p := by',
      '  intro h',
      '  cases h with',
      '  | intro hp hq =>',
      '    constructor',
      '    · exact hq',
      '    · exact hp',
    ],
    steps: [
      { lines: [0], goals: 'p q : Prop\n⊢ p ∧ q → q ∧ p', note: '目标是一个蕴涵。' },
      { lines: [1], goals: 'p q : Prop\nh : p ∧ q\n⊢ q ∧ p', note: 'intro h：假设 h : p ∧ q。' },
      { lines: [2, 3], goals: 'case intro\np q : Prop\nhp : p\nhq : q\n⊢ q ∧ p', note: 'p ∧ q 只有一个构造子 And.intro。cases 把 h 拆成两个分量，按 | intro hp hq 的写法分别取名 hp、hq。注意 h 消失了。' },
      { lines: [4], goals: 'case intro.left\np q : Prop\nhp : p\nhq : q\n⊢ q\n\ncase intro.right\np q : Prop\nhp : p\nhq : q\n⊢ p', note: 'constructor 把目标 q ∧ p 拆成两个子目标：先证 q（left），再证 p（right）。' },
      { lines: [5], goals: 'case intro.right\np q : Prop\nhp : p\nhq : q\n⊢ p', note: '第一个 · 分支用 exact hq 解决了 q，剩下一个目标 p。', remaining: true },
      { lines: [6], goals: '', note: '第二个分支用 exact hp 解决 p。证明完成。' },
    ],
  },
  {
    key: 'comp_assoc',
    title: '复合的结合律（funext / show / rfl）',
    code: [
      "theorem comp_assoc' {α β γ δ : Type} (f : α → β) (g : β → γ) (h : γ → δ) :",
      '    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by',
      '  funext x',
      '  show h (g (f x)) = h (g (f x))',
      '  rfl',
    ],
    steps: [
      { lines: [0, 1], goals: 'α β γ δ : Type\nf : α → β\ng : β → γ\nh : γ → δ\n⊢ h ∘ g ∘ f = (h ∘ g) ∘ f', note: '目标是两个函数相等。Lean 显示时省略了多余的括号：∘ 是右结合的，h ∘ g ∘ f 就是 h ∘ (g ∘ f)。' },
      { lines: [2], goals: 'α β γ δ : Type\nf : α → β\ng : β → γ\nh : γ → δ\nx : α\n⊢ (h ∘ g ∘ f) x = ((h ∘ g) ∘ f) x', note: 'funext x：两个函数相等，当且仅当它们在每个点 x 上的值相等。得到新变量 x : α。' },
      { lines: [3], goals: 'α β γ δ : Type\nf : α → β\ng : β → γ\nh : γ → δ\nx : α\n⊢ h (g (f x)) = h (g (f x))', note: 'show 把目标换成定义上相等的写法：展开 ∘ 之后，两边都是 h (g (f x))。' },
      { lines: [4], goals: '', note: '两边一模一样，rfl 结束。这就是“函数复合满足结合律”，第 1.1 章的核心定律之一。' },
    ],
  },
  {
    key: 'not_not',
    title: '布尔值分情况（cases）',
    code: [
      'theorem not_not_bool (b : Bool) : (!(!b)) = b := by',
      '  cases b',
      '  · rfl',
      '  · rfl',
    ],
    steps: [
      { lines: [0], goals: 'b : Bool\n⊢ (!!b) = b', note: '要对任意布尔值 b 证明“取反两次等于自己”。' },
      { lines: [1], goals: 'case false\n⊢ (!!false) = false\n\ncase true\n⊢ (!!true) = true', note: 'Bool 有两个构造子，cases b 产生两个目标，分别把 b 换成 false 和 true。' },
      { lines: [2], goals: 'case true\n⊢ (!!true) = true', note: '!!false 算出来就是 false，rfl 解决第一个目标。', remaining: true },
      { lines: [3], goals: '', note: '同理解决 true 的情况。也可以把这三行合写成 cases b <;> rfl。' },
    ],
  },
  {
    key: 'zero_add',
    title: '数学归纳法（induction / rw）',
    code: [
      "theorem zero_add' (n : Nat) : 0 + n = n := by",
      '  induction n with',
      '  | zero => rfl',
      '  | succ k ih =>',
      '    rw [Nat.add_succ]',
      '    rw [ih]',
    ],
    steps: [
      { lines: [0], goals: 'n : Nat\n⊢ 0 + n = n', note: 'n + 0 = n 可以直接算，但 0 + n = n 不行（加法按第二个参数递归定义），需要归纳法。' },
      { lines: [1], goals: 'case zero\n⊢ 0 + 0 = 0\n\ncase succ\nk : Nat\nih : 0 + k = k\n⊢ 0 + (k + 1) = k + 1', note: 'induction 产生两个目标：基础情况 n = 0；归纳步骤 n = k + 1，并附带归纳假设 ih（对 k 成立）。' },
      { lines: [2], goals: 'case succ\nk : Nat\nih : 0 + k = k\n⊢ 0 + (k + 1) = k + 1', note: '0 + 0 = 0 直接算出来，rfl 解决。剩下归纳步骤。', remaining: true },
      { lines: [3], goals: 'case succ\nk : Nat\nih : 0 + k = k\n⊢ 0 + (k + 1) = k + 1', note: '进入 succ 分支，k 和 ih 是我们给新变量起的名字。' },
      { lines: [4], goals: 'case succ\nk : Nat\nih : 0 + k = k\n⊢ (0 + k).succ = k + 1', note: 'Nat.add_succ : n + succ m = succ (n + m)。重写后，目标里出现了 0 + k，正好是归纳假设的左边。' },
      { lines: [5], goals: '', note: 'rw [ih] 把 0 + k 换成 k，目标变成 k.succ = k + 1，两边按定义相同，rw 自动用 rfl 结束。' },
    ],
  },
]

const props = defineProps({ initial: { type: String, default: 'imp_trans' } })

const sel = ref(Math.max(0, PROOFS.findIndex((p) => p.key === props.initial)))
const step = ref(0)
const playing = ref(false)
let timer = 0

const proof = computed(() => PROOFS[sel.value])
const cur = computed(() => proof.value.steps[step.value])
const prev = computed(() => (step.value > 0 ? proof.value.steps[step.value - 1] : null))
const doneLines = computed(() => {
  const s = new Set()
  for (let i = 0; i < step.value; i++) proof.value.steps[i].lines.forEach((l) => s.add(l))
  return s
})

function parseGoals(text) {
  if (!text) return []
  return text.split('\n\n').map((block) => {
    const lines = block.split('\n')
    let label = ''
    if (lines[0].startsWith('case ')) label = lines.shift().slice(5)
    return { label, hyps: lines.filter((l) => !l.startsWith('⊢')), target: lines.find((l) => l.startsWith('⊢')) || '' }
  })
}

const goals = computed(() => parseGoals(cur.value.goals))
const prevLines = computed(() => new Set((prev.value?.goals || '').split('\n')))
const isNew = (line) => step.value > 0 && !prevLines.value.has(line)

const KW = new Set(['theorem', 'by', 'with', 'fun', 'Prop', 'Type', 'Bool', 'Nat'])
const TAC = new Set(['intro', 'apply', 'exact', 'cases', 'constructor', 'funext', 'show', 'rfl', 'induction', 'rw'])
const esc = (s) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
function highlight(line) {
  return line
    .split(/(\s+|[()[\]{},:]+)/)
    .map((tok) => {
      if (KW.has(tok)) return `<span class="kw">${esc(tok)}</span>`
      if (TAC.has(tok)) return `<span class="tac">${esc(tok)}</span>`
      return esc(tok)
    })
    .join('')
}

function stop() {
  playing.value = false
  clearInterval(timer)
}
function choose(i) {
  stop()
  sel.value = i
  step.value = 0
}
function go(d) {
  stop()
  step.value = Math.min(proof.value.steps.length - 1, Math.max(0, step.value + d))
}
function first() {
  stop()
  step.value = 0
}
function autoplay() {
  if (playing.value) return stop()
  if (step.value >= proof.value.steps.length - 1) step.value = 0
  playing.value = true
  timer = setInterval(() => {
    if (step.value >= proof.value.steps.length - 1) return stop()
    step.value++
  }, 2200)
}
onBeforeUnmount(stop)
</script>

<template>
  <div class="ctfp-widget tr">
    <div class="ctfp-widget-title">tactic 证明逐步回放器：看每一步之后的 goal 状态</div>
    <div class="tabs">
      <button v-for="(p, i) in PROOFS" :key="p.key" class="ctfp-btn" :class="{ on: i === sel }" @click="choose(i)">
        {{ p.title }}
      </button>
    </div>
    <div class="panes">
      <div class="code">
        <div class="pane-head">证明脚本</div>
        <div class="src">
          <div
            v-for="(l, i) in proof.code" :key="i"
            class="ln" :class="{ active: cur.lines.includes(i), done: doneLines.has(i) && !cur.lines.includes(i) }"
          ><span class="no">{{ i + 1 }}</span><span v-html="highlight(l)" /></div>
        </div>
      </div>
      <div class="info">
        <div class="pane-head">Infoview：执行完高亮行之后<span v-if="cur.remaining">（本分支已解决，显示剩余目标）</span></div>
        <div v-if="!goals.length" class="nogoals">No goals<span>证明完成</span></div>
        <div v-else class="goals">
          <div v-for="(g, gi) in goals" :key="gi" class="goal">
            <div v-if="g.label" class="case">case {{ g.label }}</div>
            <div v-for="(h, hi) in g.hyps" :key="hi" class="hyp" :class="{ fresh: isNew(h) }">{{ h }}</div>
            <div class="target" :class="{ fresh: isNew(g.target) }">{{ g.target }}</div>
          </div>
        </div>
      </div>
    </div>
    <div class="note">{{ cur.note }}</div>
    <div class="controls">
      <button class="ctfp-btn" :disabled="step === 0" @click="first">⏮ 开头</button>
      <button class="ctfp-btn" :disabled="step === 0" @click="go(-1)">◀ 上一步</button>
      <span class="count">第 {{ step + 1 }} / {{ proof.steps.length }} 步</span>
      <button class="ctfp-btn" :disabled="step === proof.steps.length - 1" @click="go(1)">下一步 ▶</button>
      <button class="ctfp-btn" :class="{ on: playing }" @click="autoplay">{{ playing ? '⏸ 暂停' : '⏵ 自动播放' }}</button>
    </div>
    <div class="hint">提示：绿色底色的行是这一步新出现（或发生变化）的假设与目标。</div>
  </div>
</template>

<style scoped>
.tabs {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
  margin-bottom: 12px;
}
.panes {
  display: grid;
  grid-template-columns: minmax(0, 1fr);
  gap: 10px;
}
.pane-head {
  font-size: 12px;
  color: var(--vp-c-text-3);
  margin-bottom: 6px;
}
.pane-head span {
  margin-left: 4px;
}
.code,
.info {
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
  border-radius: 8px;
  padding: 10px 12px;
  min-width: 0;
}
.src {
  overflow-x: auto;
  font-family: var(--vp-font-family-mono);
  font-size: 12.5px;
  line-height: 1.7;
}
.info {
  min-height: 150px;
}
.ln {
  white-space: pre;
  padding: 0 6px;
  border-radius: 4px;
  transition: background 0.25s, opacity 0.25s;
  opacity: 0.55;
}
.ln.done {
  opacity: 0.9;
}
.ln.active {
  opacity: 1;
  background: color-mix(in srgb, var(--vp-c-brand-1) 16%, transparent);
  box-shadow: inset 3px 0 0 var(--vp-c-brand-1);
}
.no {
  display: inline-block;
  width: 1.8em;
  color: var(--vp-c-text-3);
  user-select: none;
}
.ln :deep(.kw) {
  color: var(--vp-c-purple-1, #8e5cd9);
}
.ln :deep(.tac) {
  color: var(--vp-c-brand-1);
  font-weight: 600;
}
.goals {
  display: flex;
  flex-direction: column;
  gap: 10px;
}
.goal {
  font-family: var(--vp-font-family-mono);
  font-size: 13px;
  line-height: 1.7;
  overflow-x: auto;
}
.goal + .goal {
  border-top: 1px dashed var(--vp-c-divider);
  padding-top: 8px;
}
.case {
  color: var(--vp-c-text-3);
  font-size: 12px;
}
.hyp,
.target {
  white-space: pre;
  padding: 0 4px;
  border-radius: 4px;
  transition: background 0.3s;
}
.target {
  color: var(--vp-c-brand-1);
  font-weight: 600;
}
.fresh {
  background: color-mix(in srgb, var(--vp-c-green-1, #18794e) 18%, transparent);
}
.nogoals {
  font-family: var(--vp-font-family-mono);
  color: var(--vp-c-green-1, #18794e);
  font-weight: 600;
  padding: 8px 4px;
}
.nogoals span {
  margin-left: 10px;
  font-family: var(--vp-font-family-base);
  font-weight: 400;
  font-size: 13px;
  color: var(--vp-c-text-2);
}
.note {
  margin-top: 12px;
  font-size: 14px;
  line-height: 1.75;
  color: var(--vp-c-text-1);
  min-height: 3.5em;
}
.controls {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 8px;
  margin-top: 8px;
}
.controls button:disabled {
  opacity: 0.4;
  cursor: default;
}
.count {
  font-size: 13px;
  color: var(--vp-c-text-2);
  font-variant-numeric: tabular-nums;
}
.hint {
  margin-top: 8px;
  font-size: 12px;
  color: var(--vp-c-text-3);
}
</style>
