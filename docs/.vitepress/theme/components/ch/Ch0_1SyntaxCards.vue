<script setup>
import { ref, computed } from 'vue'

const CARDS = [
  {
    topic: '函数',
    sec: '§3',
    rust: 'fn add(x: u64, y: u64) -> u64 {\n    x + y\n}\n\nlet five = add(2, 3);',
    lean: 'def add (x y : Nat) : Nat :=\n  x + y\n\n#guard add 2 3 == 5',
    note: '参数写成 (名字 : 类型)；函数体是表达式，没有 return；调用不需要括号和逗号。',
  },
  {
    topic: '闭包与柯里化',
    sec: '§3–4',
    rust: 'let inc = |x: u64| x + 1;\nlet add2 = move |y| add(2, y);\nv.iter().map(|x| x * 10)',
    lean: 'def inc := fun (x : Nat) => x + 1\ndef add2 := add 2      -- 部分应用\n[1, 2, 3].map (· * 10)',
    note: 'fun x => e 就是 |x| e。多参数函数天生柯里化：add 2 本身就是一个函数。',
  },
  {
    topic: '结构体',
    sec: '§5',
    rust: '#[derive(Debug, PartialEq)]\nstruct Point { x: i64, y: i64 }\n\nlet p = Point { x: 3, y: 4 };\nlet q = Point { y: 10, ..p };',
    lean: 'structure Point where\n  x : Int\n  y : Int\nderiving Repr, BEq\n\ndef p : Point := ⟨3, 4⟩\ndef q : Point := { p with y := 10 }',
    note: 'deriving Repr, BEq ≈ derive(Debug, PartialEq)。⟨3, 4⟩ 是匿名构造子。',
  },
  {
    topic: '方法',
    sec: '§5',
    rust: 'impl Point {\n    fn norm_sq(&self) -> i64 {\n        self.x * self.x + self.y * self.y\n    }\n}\np.norm_sq()',
    lean: 'def Point.normSq (p : Point) : Int :=\n  p.x * p.x + p.y * p.y\n\n#eval p.normSq   -- 25',
    note: '在命名空间 Point 下定义函数，就能用点记号调用。',
  },
  {
    topic: '枚举',
    sec: '§6',
    rust: 'enum Shape {\n    Circle { r: f64 },\n    Rect { w: f64, h: f64 },\n}\nenum Tree<T> {\n    Leaf,\n    Node(Box<Tree<T>>, T, Box<Tree<T>>),\n}',
    lean: 'inductive Shape where\n  | circle (r : Float)\n  | rect (w h : Float)\n\ninductive Tree (α : Type) where\n  | leaf : Tree α\n  | node : Tree α → α → Tree α → Tree α',
    note: 'inductive ≈ enum。递归类型不需要 Box。',
  },
  {
    topic: '模式匹配',
    sec: '§7',
    rust: 'fn area(s: &Shape) -> f64 {\n    match s {\n        Shape::Circle { r } => 3.14 * r * r,\n        Shape::Rect { w, h } => w * h,\n    }\n}',
    lean: 'def Shape.area : Shape → Float\n  | .circle r => 3.14 * r * r\n  | .rect w h => w * h',
    note: '同样有穷尽性检查。可以省略 match s with，直接按情况定义。',
  },
  {
    topic: '泛型',
    sec: '§9',
    rust: 'fn swap<A, B>(p: (A, B)) -> (B, A) {\n    (p.1, p.0)\n}\nswap::<u32, &str>((1, "a"))',
    lean: 'def swap {α β : Type} (p : α × β) : β × α :=\n  (p.2, p.1)\n\n#eval @swap Nat String (1, "a")',
    note: '{α : Type} 是隐式参数 ≈ <T>。@ 让隐式参数变显式 ≈ turbofish。',
  },
  {
    topic: 'trait 与类型类',
    sec: '§10',
    rust: 'trait Monoid {\n    fn empty() -> Self;\n    fn op(self, o: Self) -> Self;\n}\nimpl Monoid for u64 { /* ... */ }\nfn mconcat<M: Monoid>(xs: Vec<M>) -> M',
    lean: 'class Monoid (α : Type) where\n  empty : α\n  op : α → α → α\n\ninstance : Monoid Nat where\n  empty := 0\n  op := (· + ·)\n\ndef mconcat [Monoid α] (xs : List α) : α',
    note: 'class ≈ trait，instance ≈ impl，[Monoid α] ≈ trait bound。类型类还可以包含定律的证明。',
  },
  {
    topic: '高阶类型（HKT）',
    sec: '§10.4',
    rust: '// 不合法：Rust 不能对 Option 本身抽象\ntrait Functor<F<_>> {\n    fn fmap<A, B>(fa: F<A>, f: impl Fn(A) -> B)\n        -> F<B>;\n}',
    lean: 'class Functor (f : Type → Type) where\n  map : {α β : Type} → (α → β) → f α → f β\n\ninstance : Functor Option where\n  map g\n    | none => none\n    | some a => some (g a)',
    note: 'List、Option 的类型是 Type → Type，可以直接作为类型类的参数。这是本书的基石。',
  },
  {
    topic: 'Option 链式调用',
    sec: '§16',
    rust: 'fn compute(a: u64, b: u64) -> Option<u64> {\n    let x = safe_div(a, b)?;\n    let y = safe_div(x, 2)?;\n    Some(x + y)\n}',
    lean: 'def compute (a b : Nat) : Option Nat := do\n  let x ← safeDiv a b\n  let y ← safeDiv x 2\n  return x + y',
    note: 'do 中的 ← ≈ ?。但 do 对任何单子都有效，不只是 Option 和 Result。',
  },
  {
    topic: '错误处理',
    sec: '§16',
    rust: 'fn parse(s: &str) -> Result<u32, String> {\n    let Some(n) = s.parse().ok() else {\n        return Err(format!("{s} 不是数字"));\n    };\n    Ok(n)\n}',
    lean: 'def parse (s : String) : Except String Nat := do\n  let some n := s.toNat?\n    | throw s!"{s} 不是数字"\n  return n',
    note: 'Except ε α ≈ Result<α, ε>（错误类型在前）。throw ≈ return Err。',
  },
  {
    topic: '模块',
    sec: '§11',
    rust: 'mod geometry {\n    pub fn unit_area() -> u64 { 1 }\n}\nuse geometry::*;',
    lean: 'namespace Geometry\ndef unitArea : Nat := 1\nend Geometry\n\nopen Geometry',
    note: 'namespace 只管名字，默认公开；可以随时重新打开。',
  },
  {
    topic: '测试与断言',
    sec: '§2',
    rust: '#[test]\nfn t() {\n    assert_eq!(add(2, 3), 5);\n}',
    lean: '#guard add 2 3 == 5\nexample : add 2 3 = 5 := rfl\ntheorem add_comm\' (a b : Nat) :\n    add a b = add b a := by\n  unfold add; omega',
    note: '#guard 在编译期检查；example 和 theorem 不是“测一次”，而是对所有输入的证明。',
  },
  {
    topic: '程序入口',
    sec: '§17',
    rust: 'fn main() {\n    println!("你好");\n}',
    lean: 'def main : IO Unit := do\n  IO.println "你好"',
    note: '副作用写在类型里：只有 IO 中的代码才能做输入输出。',
  },
]

const sel = ref(0)
const mode = ref('both')
const card = computed(() => CARDS[sel.value])
</script>

<template>
  <div class="ctfp-widget sc">
    <div class="ctfp-widget-title">Rust ↔ Lean 语法对照卡（点击主题切换）</div>
    <div class="layout">
      <div class="topics">
        <button v-for="(c, i) in CARDS" :key="c.topic" class="topic" :class="{ on: i === sel }" @click="sel = i">
          {{ c.topic }}<span>{{ c.sec }}</span>
        </button>
      </div>
      <div class="body">
        <div class="modes">
          <button class="ctfp-btn" :class="{ on: mode === 'both' }" @click="mode = 'both'">并排</button>
          <button class="ctfp-btn" :class="{ on: mode === 'rust' }" @click="mode = 'rust'">只看 Rust</button>
          <button class="ctfp-btn" :class="{ on: mode === 'lean' }" @click="mode = 'lean'">只看 Lean</button>
        </div>
        <div class="cols" :class="mode">
          <div v-if="mode !== 'lean'" class="col">
            <div class="lang rust">Rust</div>
            <div class="codebox">{{ card.rust }}</div>
          </div>
          <div v-if="mode !== 'rust'" class="col">
            <div class="lang lean">Lean 4</div>
            <div class="codebox">{{ card.lean }}</div>
          </div>
        </div>
        <div class="note">{{ card.note }}<span class="sec">详见本章 {{ card.sec }}</span></div>
      </div>
    </div>
  </div>
</template>

<style scoped>
.layout {
  display: flex;
  flex-direction: column;
  gap: 12px;
}
.topics {
  display: flex;
  flex-wrap: wrap;
  gap: 5px;
}
.topic {
  font-size: 13px;
  padding: 3px 10px;
  border-radius: 999px;
  border: 1px solid var(--vp-c-divider);
  background: transparent;
  color: var(--vp-c-text-2);
  cursor: pointer;
  display: inline-flex;
  align-items: baseline;
  gap: 6px;
  transition: all 0.2s;
}
.topic span {
  color: var(--vp-c-text-3);
  font-size: 11px;
}
.topic:hover {
  color: var(--vp-c-brand-1);
}
.topic.on {
  border-color: var(--vp-c-brand-1);
  color: var(--vp-c-brand-1);
  background: var(--vp-c-bg);
}
.body {
  min-width: 0;
}
.modes {
  display: flex;
  gap: 6px;
  margin-bottom: 10px;
  flex-wrap: wrap;
}
.cols {
  display: grid;
  gap: 10px;
}
.cols.both {
  grid-template-columns: minmax(0, 1fr) minmax(0, 1fr);
}
@media (max-width: 640px) {
  .cols.both {
    grid-template-columns: minmax(0, 1fr);
  }
}
.col {
  min-width: 0;
  display: flex;
  flex-direction: column;
}
.lang {
  font-size: 11px;
  font-weight: 600;
  letter-spacing: 0.05em;
  margin-bottom: 4px;
}
.lang.rust {
  color: #c4572f;
}
.lang.lean {
  color: var(--vp-c-brand-1);
}
.codebox {
  white-space: pre;
  overflow-x: auto;
  font-family: var(--vp-font-family-mono);
  font-size: 12px;
  line-height: 1.65;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
  border-radius: 8px;
  padding: 10px 12px;
  flex: 1;
}
.note {
  margin-top: 10px;
  font-size: 14px;
  line-height: 1.7;
  color: var(--vp-c-text-1);
}
.sec {
  margin-left: 8px;
  font-size: 12px;
  color: var(--vp-c-text-3);
}
</style>
