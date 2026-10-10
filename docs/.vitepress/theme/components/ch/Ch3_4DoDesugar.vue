<script setup>
import { ref, computed, watch } from 'vue'

// 每个例子是一串“帧”，每帧是若干行 [文本, 颜色编号|null] 加一段说明。
const EXAMPLES = [
  {
    name: 'Writer：process',
    frames: [
      {
        note: '原始的 do 块。每一行都有自己的颜色。',
        lines: [
          ['def process (s : String) : Writer String (List String) := do', null],
          ['  let upStr ← upCase s', 0],
          ['  tell "toWords "', 1],
          ['  return words upStr', 2],
        ],
      },
      {
        note: '第 1 行 `let x ← e` 变成 `e >>= fun x =>`，后面的所有行都进入这个 lambda 的函数体（仍是一个 do 块）。',
        lines: [
          ['def process (s : String) : Writer String (List String) :=', null],
          ['  upCase s >>= fun upStr => do', 0],
          ['    tell "toWords "', 1],
          ['    return words upStr', 2],
        ],
      },
      {
        note: '第 2 行的结果没有名字（是 ()），于是变成 `e >>= fun () =>`：结果被丢弃，但它的效应（往日志里追加）被保留。',
        lines: [
          ['def process (s : String) : Writer String (List String) :=', null],
          ['  upCase s >>= fun upStr =>', 0],
          ['    tell "toWords " >>= fun () => do', 1],
          ['      return words upStr', 2],
        ],
      },
      {
        note: '最后一行的 `return e` 就是 `pure e`。脱糖完成：一串嵌套的 bind 和 lambda。Lean 中两者满足 `rfl`。',
        lines: [
          ['def process (s : String) : Writer String (List String) :=', null],
          ['  upCase s >>= fun upStr =>', 0],
          ['    tell "toWords " >>= fun () =>', 1],
          ['      pure (words upStr)', 2],
        ],
      },
    ],
  },
  {
    name: 'Option：parseAndAdd',
    frames: [
      {
        note: '一个 Option 单子中的 do 块：任何一步得到 none，整个结果就是 none。',
        lines: [
          ['def parseAndAdd (a b : String) : Option Nat := do', null],
          ['  let x ← a.toNat?', 0],
          ['  let y ← b.toNat?', 1],
          ['  return x + y', 2],
        ],
      },
      {
        note: '第 1 行变成 bind。如果 a.toNat? 是 none，Option 的 bind 根本不会调用这个 lambda——“短路”就藏在 bind 里。',
        lines: [
          ['def parseAndAdd (a b : String) : Option Nat :=', null],
          ['  a.toNat? >>= fun x => do', 0],
          ['    let y ← b.toNat?', 1],
          ['    return x + y', 2],
        ],
      },
      {
        note: '第 2 行同理。注意 x 在内层 lambda 中仍然可见：这就是“后面的行可以使用前面引入的名字”。',
        lines: [
          ['def parseAndAdd (a b : String) : Option Nat :=', null],
          ['  a.toNat? >>= fun x =>', 0],
          ['    b.toNat? >>= fun y => do', 1],
          ['      return x + y', 2],
        ],
      },
      {
        note: '完成。对照 Rust：a.parse().ok().and_then(|x| b.parse().ok().and_then(|y| Some(x + y)))。',
        lines: [
          ['def parseAndAdd (a b : String) : Option Nat :=', null],
          ['  a.toNat? >>= fun x =>', 0],
          ['    b.toNat? >>= fun y =>', 1],
          ['      pure (x + y)', 2],
        ],
      },
    ],
  },
  {
    name: '嵌套动作 (← e)',
    frames: [
      {
        note: '表达式中间的 (← e) 表示“先执行 e，把结果放这儿”。',
        lines: [
          ['def addBoth (x y : Option Nat) : Option Nat := do', null],
          ['  return (← x) + (← y)', 3],
        ],
      },
      {
        note: '第一步：Lean 把嵌套动作按从左到右的顺序“提升”到当前语句之前，各起一个新名字。',
        lines: [
          ['def addBoth (x y : Option Nat) : Option Nat := do', null],
          ['  let a ← x', 0],
          ['  let b ← y', 1],
          ['  return a + b', 3],
        ],
      },
      {
        note: '之后就和普通 do 块一样，逐行变成 bind。',
        lines: [
          ['def addBoth (x y : Option Nat) : Option Nat :=', null],
          ['  x >>= fun a =>', 0],
          ['    y >>= fun b =>', 1],
          ['      pure (a + b)', 3],
        ],
      },
    ],
  },
  {
    name: 'let mut + for',
    frames: [
      {
        note: '看起来是命令式代码：一个可变变量和一个循环。',
        lines: [
          ['def sumSquares (xs : List Nat) : Nat := Id.run do', null],
          ['  let mut acc := 0', 0],
          ['  for x in xs do', 1],
          ['    acc := acc + x * x', 2],
          ['  return acc', 3],
        ],
      },
      {
        note: '`for` 变成对 forIn 的调用。可变变量 acc 的初值成为 forIn 的初始状态；循环体变成一个函数：接收元素 x 和当前状态 acc，返回 ForInStep.yield 新状态。',
        lines: [
          ['def sumSquares (xs : List Nat) : Nat := Id.run do', null],
          ['  let acc ← forIn xs 0 fun x acc =>', 1],
          ['    pure (ForInStep.yield (acc + x * x))', 2],
          ['  return acc', 3],
        ],
      },
      {
        note: '最后照常脱糖成 bind。在 Id 单子里 `m >>= pure` 就是 `m`，于是整个函数就是一次 forIn——本质上是 foldl。',
        lines: [
          ['def sumSquares (xs : List Nat) : Nat := Id.run (', null],
          ['  forIn xs 0 (fun x acc =>', 1],
          ['    pure (ForInStep.yield (acc + x * x)))', 2],
          ['  >>= fun acc => pure acc)', 3],
        ],
      },
    ],
  },
]

const ex = ref(0)
const frame = ref(0)
watch(ex, () => (frame.value = 0))
const cur = computed(() => EXAMPLES[ex.value])
const fr = computed(() => cur.value.frames[frame.value])
const last = computed(() => cur.value.frames.length - 1)

function fmt(s) {
  const esc = s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
  return esc
    .replace(/(&gt;&gt;=)/g, '<b class="bind">$1</b>')
    .replace(/\b(fun|do|def|let|mut|for|in|return|pure)\b/g, '<span class="kw">$1</span>')
}
const noteHtml = computed(() => fr.value.note.replace(/`([^`]+)`/g, '<code>$1</code>'))
</script>

<template>
  <div class="ctfp-widget dd">
    <div class="ctfp-widget-title">do 记法脱糖器：一行一行地变成 bind</div>
    <div class="row">
      <button v-for="(e, i) in EXAMPLES" :key="i" class="ctfp-btn" :class="{ on: ex === i }" @click="ex = i">{{ e.name }}</button>
    </div>
    <pre class="code"><div v-for="(l, i) in fr.lines" :key="ex + '-' + frame + '-' + i" class="ln" :class="l[1] === null ? '' : 'c' + l[1]" v-html="fmt(l[0]) || ' '"></div></pre>
    <div class="note" v-html="noteHtml" />
    <div class="row">
      <button class="ctfp-btn" :disabled="frame === 0" @click="frame--">上一步</button>
      <span class="cnt">第 {{ frame }} / {{ last }} 步</span>
      <button class="ctfp-btn" :disabled="frame === last" @click="frame++">下一步</button>
      <button class="ctfp-btn" @click="frame = 0">重置</button>
    </div>
  </div>
</template>

<style scoped>
.dd, .dd * { font-variant-ligatures: none; font-feature-settings: "liga" 0, "calt" 0; }
.row { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; margin: 8px 0; }
.code { margin: 10px 0; padding: 10px 0; background: var(--vp-c-bg); border-radius: 8px; border: 1px solid var(--vp-c-divider); font-family: var(--vp-font-family-mono); font-size: 13px; line-height: 1.75; overflow-x: auto; white-space: pre; }
.ln { padding: 0 14px; animation: fade 0.35s ease; border-left: 4px solid transparent; }
@keyframes fade { from { opacity: 0.2; transform: translateX(-4px); } to { opacity: 1; transform: none; } }
.c0 { background: color-mix(in srgb, #3b82f6 14%, transparent); border-left-color: #3b82f6; }
.c1 { background: color-mix(in srgb, #16a34a 14%, transparent); border-left-color: #16a34a; }
.c2 { background: color-mix(in srgb, #ea580c 14%, transparent); border-left-color: #ea580c; }
.c3 { background: color-mix(in srgb, #9333ea 14%, transparent); border-left-color: #9333ea; }
.code :deep(.kw) { color: var(--vp-c-brand-1); font-weight: 600; }
.code :deep(.bind) { color: #dc2626; }
.note { font-size: 13px; color: var(--vp-c-text-2); line-height: 1.7; min-height: 3.4em; }
.note :deep(code) { font-size: 12px; }
.cnt { font-size: 13px; color: var(--vp-c-text-2); }
button:disabled { opacity: 0.4; cursor: default; }
</style>
