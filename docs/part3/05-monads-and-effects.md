# 3.5 单子与副作用

```lean hidden
deriving instance BEq for Except
```

既然我们已经知道了单子是干什么用的——它让我们能够复合修饰函数——那么真正有意思的问题是：为什么修饰函数在函数式编程里如此重要？我们已经见过一个例子，`Writer` 单子：修饰让我们得以在多次函数调用之间创建并累积一份日志。一个原本要靠不纯的函数（比如访问和修改某个全局状态）才能解决的问题，用纯函数就解决了。

## 问题

下面是一份类似问题的简短清单，抄自 Eugenio Moggi 那篇开创性的论文[^moggi]。传统上，这些问题全都是靠放弃函数的纯粹性来解决的。

[^moggi]: Eugenio Moggi，[Notions of Computation and Monads](https://doi.org/10.1016/0890-5401(91)90052-4)，Information and Computation 93(1): 55–92 (1991)。

- **偏函数性**（partiality）：可能不终止的计算
- **非确定性**（nondeterminism）：可能返回多个结果的计算
- **副作用**（side effect）：访问或修改状态的计算
  - 只读状态，也就是“环境”
  - 只写状态，也就是“日志”
  - 可读可写的状态
- **异常**（exception）：可能失败的偏函数
- **延续**（continuation）：能保存程序的状态，并在需要时恢复它
- **交互式输入**
- **交互式输出**

真正令人拍案叫绝的是：所有这些问题，都能用同一个巧妙的花招来解决——求助于修饰函数。当然，每种情况下的修饰方式完全不同。

你得意识到，在这个阶段，并没有要求修饰必须是单子式的。只有当我们坚持要**复合**——也就是能把一个修饰函数拆成若干更小的修饰函数——的时候，我们才需要单子。同样，因为每种修饰都不一样，单子复合的实现也各不相同，但总体模式是一致的。这是个非常简单的模式：满足结合律、并配有恒等元的复合。

下一节满是代码示例（原书是 Haskell，本书换成了 Lean 4）。如果你急着回到范畴论，或者早已熟悉单子在函数式语言中的实现，可以略读甚至跳过。不过对 Lean 学习者来说，这一节恰恰是最实用的部分：你会在这里认识 Lean 核心库里几乎所有常用的单子。

::: tip 本章的 Lean 约定
每一种单子，我们都先在命名空间 `My` 里**从零实现一遍**（并证明它满足 `LawfulMonad`），再对照 Lean 核心库中的现成版本（`Option`、`Except`、`ReaderM`、`StateM`、`IO`……）。所有 `#guard` 都经过机器检验。
:::

## 解决方案

首先，我们来分析一下当初是怎么使用 `Writer` 单子的。我们从一个完成某项任务的纯函数出发——给定参数，它产生某个输出。然后我们用另一个函数替换它，新函数把原来的输出和一个字符串配成一对，从而修饰了原来的输出。这就是我们对日志问题的解决方案。

我们不能止步于此，因为一般来说，我们不想和铁板一块的解决方案打交道。我们需要能把一个产生日志的函数，拆成若干更小的、同样产生日志的函数。正是这些小函数的复合，把我们引向了单子的概念。

真正惊人的是，“修饰函数返回类型”的这一模式，适用于大量原本需要放弃纯粹性才能解决的问题。我们沿着清单逐一走一遍，找出适用于每个问题的修饰方式。

### 偏函数性

我们修改每一个可能不终止的函数的返回类型，把它变成一个“**提升**”（lifted）类型——这种类型包含原类型的所有值，外加一个特殊的“**底**”值 $\bot$。比如，作为集合，`Bool` 类型包含两个元素：`true` 和 `false`。提升后的 `Bool` 包含三个元素。返回提升 `Bool` 的函数可以产生 `true` 或 `false`，也可以永远执行下去。

::: info 数学小课堂：提升集合
给集合 $A$ 加上一个新元素 $\bot$（读作“底”，bottom），得到 $A_\bot = A \cup \{\bot\}$。$\bot$ 代表“这个计算没有给出结果”（比如死循环了）。于是一个可能不终止的函数 $f : X \to Y$，可以看成一个**全**函数 $f : X \to Y_\bot$：它在不终止的输入上取值 $\bot$。

这是“把副作用编码进返回类型”的第一个例子：原本“可能卡住”这种行为，被变成了返回值里的一个普通元素。
:::

有趣的是，在 Haskell 这样的惰性语言里，一个永不结束的函数居然可以“返回”一个值，而且这个值还能传给下一个函数。我们把这个特殊值叫作底。只要这个值不被显式地需要（比如被模式匹配、或者作为输出打印），它就可以四处传递，而不会让程序卡住。由于每个 Haskell 函数都**可能**不终止，Haskell 中所有的类型都被假定为提升的。这就是为什么我们常常谈论 Haskell（提升）类型与函数的范畴 **Hask**，而不是更简单的 $\mathbf{Set}$。不过，**Hask** 到底是不是一个真正的范畴，其实并不清楚（参见 [Andrej Bauer 的这篇文章](http://math.andrej.com/2016/08/06/hask-is-not-a-category/)）。

**Lean 走的是另一条路**。Lean 是严格求值、全函数的语言：一个普通的 `def` 必须被证明会终止，否则编译不过。所以 Lean 的类型**没有**被提升，`Bool` 就只有两个值——Lean 的类型和函数是 $\mathbf{Set}$ 的一个好得多的模型。代价是，那些“可能不终止”的函数要么用 `partial def` 标记（编译器允许它，但在逻辑里把它当作一个看不见内部的常量，你没法对它的行为做任何证明），要么就得显式地把“不终止”编码进返回类型——这正是本节的主题。

```lean
-- partial def：可以运行，但不能对它做证明
partial def collatz (n : Nat) : Nat :=
  if n ≤ 1 then 0 else 1 + collatz (if n % 2 == 0 then n / 2 else 3 * n + 1)

#guard collatz 27 == 111

-- 显式修饰：给一份“燃料”，燃料耗尽就返回 none，扮演 ⊥ 的角色
def collatzFuel : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, n =>
    if n ≤ 1 then some 0
    else (· + 1) <$> collatzFuel fuel (if n % 2 == 0 then n / 2 else 3 * n + 1)

#guard collatzFuel 200 27 == some 111
#guard collatzFuel 50 27 == none     -- 燃料不够：“没算完”
```

`collatzFuel` 是一个返回 `Option Nat` 的全函数，`none` 就是我们手造的 $\bot$。`Option` 正是下文“异常”一节里的那个单子。

::: tip Lean 深入：为什么 `partial def` 无法证明
如果 Lean 允许你把 `partial def f (n : Nat) : Nat := f n + 1` 当作普通定义展开，就能推出 `f n = f n + 1`，进而推出 `0 = 1`——逻辑就崩了。所以 Lean 只保证 `partial def` 的类型“有居民”（这里 `Nat` 显然有），然后把函数体藏起来，仅供编译后的代码运行。这就是 Lean 把“可能不终止”的计算和“可证明”的数学世界隔离开的方法。
:::

### 非确定性

如果一个函数可以返回许多不同的结果，那它不妨一次性把它们全部返回。从语义上说，一个非确定性函数等价于一个返回结果列表的函数。在一门惰性、带垃圾回收的语言里，这非常合理。比如，如果你只需要一个值，就取列表的头，尾巴永远不会被求值。如果你需要一个随机值，就用随机数生成器挑出第 n 个元素。惰性甚至允许你返回一个无限的结果列表。

（Lean 是严格求值的，`List` 必须是有限的，取头也会先把整个列表算出来。这一点我们在讲勾股数时会再碰到。）

在列表单子——Haskell 对非确定性计算的实现——中，`join` 被实现为 `concat`（Lean 里叫 `List.flatten`）。还记得吗，`join` 的职责是把“容器的容器”压扁——`concat` 正是把列表的列表拼接成单个列表。`return` 则创建一个单元素列表。

::: warning 易错点：Lean 核心库没有 `Monad List` 实例
在 Lean 4 核心库里写 `#check (inferInstance : Monad List)` 会报错：找不到实例。这是一个有意的设计选择——在严格求值的语言里，列表单子会把所有分支都老老实实地算出来，很容易写出意外低效的程序，所以核心库宁可不提供（Mathlib 提供了这个实例）。本章是自包含的，我们自己补上。
:::

```lean
instance : Monad List where
  map := List.map
  pure x := [x]
  bind xs k := xs.flatMap k
```

列表单子的 bind 由一般公式给出：先 `map`，后 `join`。在这里就是：

```lean
example (xs : List α) (k : α → List β) : xs >>= k = (xs.map k).flatten := List.flatMap_def
```

这里，本身就产生列表的函数 `k` 被作用到列表 `xs` 的每个元素上，结果是一个列表的列表，再用 `flatten` 压平。核心库把“先 map 再 flatten”这个组合直接叫作 `flatMap`——Rust 程序员一定觉得眼熟。

既然自己写了实例，就要对它负责——证明它满足单子定律：

```lean
instance : LawfulMonad List := LawfulMonad.mk'
  -- id <$> xs = xs
  (id_map := by intro α xs; simp [Functor.map])
  -- [x].flatMap f = f x
  (pure_bind := by intro α β x f; simp [pure, bind])
  -- (xs.flatMap f).flatMap g = xs.flatMap (fun x => (f x).flatMap g)
  (bind_assoc := by intro α β γ xs f g; simp [bind, List.flatMap_assoc])
  -- xs.flatMap (fun y => [f y]) = xs.map f，用归纳法证明
  (bind_pure_comp := by
    intro α β f xs
    show xs.flatMap (fun y => [f y]) = xs.map f
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih])
```

::: tip Lean 深入：`induction`
`induction xs with | nil => … | cons x xs ih => …` 对列表做**结构归纳**：先证空列表的情形，再在“假设对 `xs` 成立（归纳假设 `ih`）”的前提下证明对 `x :: xs` 成立。这和数学课上的“数学归纳法”是一回事，只是归纳的对象从自然数换成了列表。
:::

从程序员的角度看，使用列表要比在循环里调用一个非确定性函数、或者实现一个返回迭代器的函数容易得多（尽管在[现代 C++](http://ericniebler.com/2014/04/27/range-comprehensions/) 里，返回一个惰性 range 几乎就等价于在 Haskell 里返回一个列表；在 Rust 里则是返回一个 `impl Iterator`）。

创造性地运用非确定性的一个好例子是游戏编程。比如电脑和人下国际象棋时，它没法预测对手的下一步，但它可以生成所有可能走法的列表，一个一个地分析。类似地，一个非确定性的解析器可以为给定表达式生成所有可能的解析结果。

尽管我们可以把返回列表的函数解释为非确定性的，列表单子的应用其实广泛得多。这是因为，把产生列表的计算缝合在一起，恰好是命令式编程中迭代结构——循环——的完美函数式替代品。单个循环常常可以用 `map` 改写，把循环体作用到列表的每个元素上。而列表单子中的 `do` 记法，可以用来替代复杂的嵌套循环。

我最喜欢的例子是生成**勾股数**（毕达哥拉斯三元组）的程序——能构成直角三角形三条边的正整数三元组。原书的 Haskell 版本从无限列表 `[1..]` 里取 `z`；Lean 的列表是有限的，所以我们给 `z` 一个上界 `n`：

```lean
instance : Alternative List where
  failure := []
  orElse xs ys := xs ++ ys ()

def triples (n : Nat) : List (Nat × Nat × Nat) := do
  let z ← List.range' 1 n            -- z 取 1, 2, …, n
  let x ← List.range' 1 z            -- x 取 1, 2, …, z
  let y ← List.range' x (z - x + 1)  -- y 取 x, x+1, …, z
  guard (x ^ 2 + y ^ 2 = z ^ 2)
  return (x, y, z)

#guard triples 20 ==
  [(3, 4, 5), (6, 8, 10), (5, 12, 13), (9, 12, 15), (8, 15, 17), (12, 16, 20)]
```

第一行告诉我们，`z` 从 1 到 `n` 的列表中取得一个元素（`List.range' a k` 是从 `a` 开始的 `k` 个连续自然数）。然后 `x` 从 1 到 `z` 之间的（有限）列表中取一个元素。最后 `y` 从 `x` 到 `z` 之间的列表中取一个元素。于是我们手上有了三个数 $1 \leqslant x \leqslant y \leqslant z$。函数 `guard` 接受一个条件，返回一个由单位值组成的列表：

```lean
example : (guard True : List Unit) = [()] := rfl
example : (guard False : List Unit) = [] := rfl
```

这个函数（它属于一个更大的类，Haskell 叫 `MonadPlus`，Lean 里对应的是 `Alternative`——这就是上面我们先补了一个 `Alternative List` 实例的原因）在这里被用来过滤掉不是勾股数的三元组。确实，看一下 bind 的实现（或者相关的 `*>`）你就会发现：给它一个空列表，它产生空列表——后面的代码一次也不会运行。另一方面，给它一个非空列表（这里是只含一个单位值的列表 `[()]`），bind 就会调用延续，这里是 `return (x, y, z)`，它产生一个只含一个已验证勾股数的单元素列表。所有这些单元素列表会被外层的 bind 拼接起来，得到最终的结果。在 Haskell 里结果是无限的；当然，`triples` 的调用者永远不可能消费完整个列表，但这不要紧，因为 Haskell 是惰性的。

::: tip Lean 深入：在严格语言里“要前 k 个”
Lean 是严格的，没法“先构造无限列表、再按需取用”。一个地道的替代是用 `for` 循环加提前 `return`（上一章讲过，它们都脱糖为 bind 与 `forIn`）。`[a:b]` 是 Lean 的区间记法，表示 $a \le i < b$：

```lean
def firstTriples (k : Nat) : List (Nat × Nat × Nat) := Id.run do
  let mut found := []
  for z in [1:10000] do
    for x in [1:z+1] do
      for y in [x:z+1] do
        if x ^ 2 + y ^ 2 = z ^ 2 then
          found := found ++ [(x, y, z)]
          if found.length = k then return found
  return found

#guard firstTriples 3 == [(3, 4, 5), (6, 8, 10), (5, 12, 13)]
```

注意这其实把问题绕回了“三重嵌套循环”——只是在 Lean 里它依然是纯函数。而 Rust 的迭代器是**惰性**的，可以直接写出“无限版本”：

```rust
pub fn triples() -> impl Iterator<Item = (u64, u64, u64)> {
    (1u64..).flat_map(|z| {
        (1..=z).flat_map(move |x| {
            (x..=z).filter(move |&y| x * x + y * y == z * z)
                   .map(move |y| (x, y, z))
        })
    })
}
// triples().take(3).collect::<Vec<_>>() == [(3,4,5), (6,8,10), (5,12,13)]
```

这里每个 `flat_map` 就是列表单子的一个 bind，`filter` 扮演 `guard` 的角色。
:::

下面的组件把列表单子的非确定性“展开树”画了出来：每个 `←` 都是一次分叉，`guard` 把失败的分支剪掉，最后 bind 把所有存活的叶子按顺序拼接起来。

<div class="ctfp-widget-host"><Ch3_5ListTree /></div>

一个原本需要三重嵌套循环的问题，在列表单子和 `do` 记法的帮助下被大大简化了。好像这还不够似的，Haskell 还允许你用**列表推导式**（list comprehension）把代码进一步简化：

```lean no-check
-- Haskell 原文的写法（Lean 核心不支持）
triples = [(x, y, z) | z <- [1..], x <- [1..z], y <- [x..z], x^2 + y^2 == z^2]
```

这只是列表单子（严格地说，是 `MonadPlus`）的又一层语法糖。

Lean 没有内置列表推导式——但 Lean 有一样 Haskell 没有的东西：**卫生宏**，你可以在库里给语言**加语法**。几行代码就能自制一个：

```lean
declare_syntax_cat compClause
syntax ident " ← " term : compClause
syntax "if " term : compClause
syntax "[" term " | " compClause,+ "]" : term

macro_rules
  | `([ $e | $x:ident ← $xs ]) => `(List.flatMap (fun $x => [$e]) $xs)
  | `([ $e | if $p ]) => `(if $p then [$e] else [])
  | `([ $e | $x:ident ← $xs, $cs,* ]) => `(List.flatMap (fun $x => [ $e | $cs,* ]) $xs)
  | `([ $e | if $p, $cs,* ]) => `(if $p then [ $e | $cs,* ] else [])

def triples' (n : Nat) : List (Nat × Nat × Nat) :=
  [(x, y, z) | z ← List.range' 1 n, x ← List.range' 1 z, y ← List.range' x (z - x + 1),
               if x ^ 2 + y ^ 2 = z ^ 2]

#guard triples' 20 == triples 20
```

::: tip Lean 深入：`syntax` 与 `macro_rules`
`declare_syntax_cat` 声明一个新的语法类别（这里是推导式的“子句”）；`syntax` 规定新语法长什么样；`macro_rules` 规定它展开成什么。每条规则左边是一个**语法模式**（`$x:ident` 匹配一个标识符，`$cs,*` 匹配逗号分隔的剩余子句），右边是展开结果。展开是递归的：每遇到一个 `x ← xs` 子句就套一层 `flatMap`（也就是列表单子的 bind），每遇到一个 `if` 子句就做一次过滤（也就是 `guard`）。这再一次说明了：列表推导式只不过是 bind 的另一种写法。
:::

你也许在别的函数式或命令式语言里，以生成器和协程的面目见过类似的构造（Python 的推导式和 `yield`、Rust 的迭代器适配器链，都是同一个思想）。

### 只读状态

一个对某个外部状态（或者叫**环境**）有只读访问权的函数，总可以替换成一个把这个环境当作额外参数的函数。一个纯函数 `(α × e) → β`（其中 `e` 是环境的类型）乍一看不像是 Kleisli 箭头。但只要把它柯里化成 `α → (e → β)`，我们就认出了这个修饰：它是我们的老朋友 **Reader 函子**：

```lean
namespace My

structure Reader (e : Type) (α : Type) where
  run : e → α
```

你可以把一个返回 `Reader` 的函数理解为生产出一个“迷你可执行程序”：一个**动作**（action），只要给它一个环境，它就产出想要的结果。有一个辅助函数 `runReader` 用来执行这样的动作：

```lean
def runReader (r : Reader e α) (env : e) : α := r.run env
```

对不同的环境值，它可能产生不同的结果。

注意，返回 `Reader` 的函数，以及 `Reader` 动作本身，都是纯的。

要实现 `Reader` 单子的 bind，首先注意到你必须产出一个函数，它接受环境 `e`，产生一个 `β`：

```lean no-check
bind ra k := ⟨fun env => _⟩
```

在这个 lambda 里面，我们可以执行动作 `ra`，得到一个 `α`：

```lean no-check
bind ra k := ⟨fun env =>
  let a := runReader ra env
  _⟩
```

然后把这个 `a` 交给延续 `k`，得到一个新的动作 `rb`：

```lean no-check
bind ra k := ⟨fun env =>
  let a := runReader ra env
  let rb := k a
  _⟩
```

最后，用环境 `env` 运行动作 `rb`：

```lean no-check
bind ra k := ⟨fun env =>
  let a := runReader ra env
  let rb := k a
  runReader rb env⟩
```

至于 `pure`，我们创建一个忽略环境、原样返回值的动作。

把这些拼在一起，稍加简化，就得到下面的定义：

```lean
instance : Monad (Reader e) where
  pure x := ⟨fun _ => x⟩
  bind ra k := ⟨fun env => runReader (k (runReader ra env)) env⟩
```

Reader 的单子定律证明出奇地简单：三条全都是 `rfl`——它们在**定义上**就成立，Lean 只需展开定义就能看出两边相同。

```lean
instance : LawfulMonad (Reader e) := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun _ _ _ => rfl)
```

一个用法示例。`ask` 是一个“取得整个环境”的动作：

```lean
def ask : Reader e e := ⟨id⟩

structure Config where
  verbose : Bool
  name : String

def greet : Reader Config String := do
  let cfg ← ask
  return s!"Hello, {cfg.name}" ++ (if cfg.verbose then "! Nice to meet you." else ".")

#guard runReader greet ⟨true, "Lean"⟩ == "Hello, Lean! Nice to meet you."
#guard runReader greet ⟨false, "Rust"⟩ == "Hello, Rust."
```

::: tip Rust 视角：依赖注入
Reader 单子就是函数式的**依赖注入**：与其把 `&Config` 一层层显式地传给每个函数，不如让每个函数返回“一个等着 `Config` 的计算”，最后在最外层一次性喂进去。Rust 里你通常会把 `&Config` 作为参数传下去，或者放进某个上下文结构体；Reader 单子做的是同一件事，只是把“传参”这件苦差事藏进了 bind。
:::

### 只写状态

这就是我们最初的日志例子。修饰由 `Writer` 函子给出（我们需要先把 `Monoid` 类再定义一遍——每章的代码都是自包含的）：

```lean
class Monoid (w : Type) where
  mempty : w
  mappend : w → w → w
  mempty_mappend : ∀ x : w, mappend mempty x = x
  mappend_mempty : ∀ x : w, mappend x mempty = x
  mappend_assoc : ∀ x y z : w, mappend (mappend x y) z = mappend x (mappend y z)

instance : Monoid String where
  mempty := ""
  mappend := (· ++ ·)
  mempty_mappend _ := String.empty_append
  mappend_mempty _ := String.append_empty
  mappend_assoc _ _ _ := String.append_assoc

structure Writer (w : Type) (α : Type) where
  run : α × w
```

为了完整，还有一个平凡的辅助函数 `runWriter`，把数据构造子拆开：

```lean
def runWriter (x : Writer w α) : α × w := x.run
```

我们之前已经看到，要让 `Writer` 可复合，`w` 必须是一个幺半群。下面是用 bind 写成的 `Writer` 单子实例：

```lean
instance [Monoid w] : Monad (Writer w) where
  pure a := ⟨(a, Monoid.mempty)⟩
  bind x k :=
    let (a, w) := runWriter x
    let (a', w') := runWriter (k a)
    ⟨(a', Monoid.mappend w w')⟩

instance [Monoid w] : LawfulMonad (Writer w) := LawfulMonad.mk'
  (id_map := by
    intro α x
    show (⟨(x.run.1, Monoid.mappend x.run.2 Monoid.mempty)⟩ : Writer w α) = x
    rw [Monoid.mappend_mempty])
  (pure_bind := by
    intro α β a f
    show (⟨((f a).run.1, Monoid.mappend Monoid.mempty (f a).run.2)⟩ : Writer w β) = f a
    rw [Monoid.mempty_mappend])
  (bind_assoc := by
    intro α β γ x f g
    show (⟨_, Monoid.mappend (Monoid.mappend x.run.2 _) _⟩ : Writer w γ)
      = ⟨_, Monoid.mappend x.run.2 (Monoid.mappend _ _)⟩
    rw [Monoid.mappend_assoc]
    rfl)

def tell (s : w) : Writer w Unit := ⟨((), s)⟩

def logged : Writer String Nat := do
  tell "start "
  let x := 6 * 7
  tell s!"computed {x} "
  return x

#guard runWriter logged == (42, "start computed 42 ")
```

（这一次我们没有单独写 `Functor` 实例，于是 `map` 由 `bind` 和 `pure` 自动生成——所以连 `id_map` 也要用到幺半群的右单位律。）

::: tip Lean 核心库里的 Writer？
Lean 4 核心库**没有** `Writer`/`WriterT`。实践中，人们通常直接用 `StateM`（下一节）来模拟它：把日志当作状态，`tell s` 就是 `modify (· ++ s)`。只写状态本来就是读写状态的一个特例。
:::

### 状态

对状态有读写权限的函数，结合了 `Reader` 和 `Writer` 两种修饰。你可以把它们看作纯函数：把状态当作额外参数，结果是一个“值/状态”对：`(α × s) → (β × s)`。柯里化以后，我们把它们写成 Kleisli 箭头的形式 `α → (s → (β × s))`，修饰被抽象为 **State 函子**：

```lean
structure State (s : Type) (α : Type) where
  run : s → α × s
```

同样，我们可以把一个 Kleisli 箭头看作返回一个动作，这个动作可以用辅助函数执行：

```lean
def runState (st : State s α) (s₀ : s) : α × s := st.run s₀
```

不同的初始状态不仅可能产生不同的结果，还可能产生不同的终态。

`State` 单子 bind 的实现和 `Reader` 单子非常相似，只是要小心地在每一步传递**正确的**状态：

```lean no-check
bind sa k := ⟨fun s =>
  let (a, s') := runState sa s     -- 用当前状态 s 运行 sa，得到值 a 和新状态 s'
  let sb := k a
  runState sb s'⟩                  -- 用新状态 s'（而不是 s！）运行下一个动作
```

完整的实例如下：

```lean
instance : Monad (State s) where
  pure a := ⟨fun s => (a, s)⟩
  bind sa k := ⟨fun s =>
    let (a, s') := runState sa s
    runState (k a) s'⟩

instance : LawfulMonad (State s) := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun _ _ _ => rfl)
```

（和 Reader 一样，三条定律全是 `rfl`。）

还有两个辅助的 Kleisli 箭头，用来操纵状态。一个取出状态以供检查：

```lean
def get : State s s := ⟨fun s => (s, s)⟩
```

另一个用一个全新的状态替换掉它：

```lean
def put (s' : s) : State s Unit := ⟨fun _ => ((), s')⟩
```

用它们写一个“取号机”：返回当前号码，并把号码加一。

```lean
def counter : State Nat Nat := do
  let n ← get
  put (n + 1)
  return n

#guard runState (do let a ← counter; let b ← counter; return a + b) 10 == (21, 12)
```

::: tip Lean 深入：`get` 和 `put` 的代数定律
除了单子定律，`get`/`put` 还满足几条自己的定律，它们刻画了“状态”到底是什么。在我们的实现里，它们全都是 `rfl`：

```lean
-- 读出来再原样写回去，等于什么都没做
theorem get_put : (do let s ← get; put s : State σ Unit) = pure () := rfl
-- 连写两次，只有第二次算数
theorem put_put (a b : σ) : (do put a; put b : State σ Unit) = put b := rfl
-- 写完立刻读，读到的就是刚写的
theorem put_get (a : σ) : (do put a; get : State σ σ) = (do put a; pure a) := rfl
```

在后面讲 Lawvere 理论的章节里，你会看到“一个单子 = 一组操作 + 一组等式”这一观点的范畴论版本。
:::

下面的组件把 State 单子里那条“看不见的管道”画了出来：左边是你写的 `do` 代码，右边是状态在每一步之间怎样被悄悄地传递。点“显示隐藏的管道”，可以看到 bind 实际替你写了哪些代码。

<div class="ctfp-widget-host"><Ch3_5StatePipeline /></div>

**Lean 核心库**中，状态单子叫 `StateM σ`（它是单子变换器 `StateT σ Id` 的简写，变换器见本章结论）。`get`、`set`（就是我们的 `put`）、`modify`、`getModify` 都已备好，`.run s₀` 返回“值和终态”，`.run' s₀` 只返回值：

```lean
end My

def counterCore : StateM Nat Nat := do
  let n ← get
  set (n + 1)
  return n

#guard Id.run ((do
    let a ← counterCore
    modify (· * 10)
    let b ← counterCore
    return (a, b)).run 3) == ((3, 40), 41)
```

（`StateM` 的 `.run` 结果包在 `Id` 里，所以外面再套一层 `Id.run` 取出来。`modify f` 等价于 `do let s ← get; set (f s)`。）

::: tip Lean 深入：`let mut` 也是状态单子
上一章我们看到，`do` 块里的 `let mut` 变量会被脱糖为“在 bind 之间传递的额外参数”。这和 State 单子做的是**同一件事**——只不过 `let mut` 的状态是编译器在局部替你传的，而 `StateM` 的状态是 bind 替你传的，可以跨越函数边界。
:::

### 异常

一个会抛异常的命令式函数，实际上是一个偏函数——在某些参数值上它没有定义。用纯的全函数来实现异常，最简单的做法是用 Maybe 函子（Lean 中叫 `Option`）。偏函数被扩展成一个全函数：在有意义的地方返回 `some a`，没有意义的地方返回 `none`。如果还想返回一些关于失败原因的信息，可以改用 Either 函子（Lean 中叫 `Except ε`，第一个类型参数固定为错误类型，比如 `String`）。

下面是 Maybe 的单子实例。为了不和核心库的 `Option` 混淆，我们自己定义一个 `Maybe`：

```lean
namespace My

inductive Maybe (α : Type) where
  | nothing : Maybe α
  | just : α → Maybe α

open Maybe

instance : Monad Maybe where
  pure a := just a
  bind
    | nothing, _ => nothing
    | just a, k => k a

instance : LawfulMonad Maybe := LawfulMonad.mk'
  (id_map := by intro α x; cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := by intro α β γ x f g; cases x <;> rfl)
```

注意，一旦检测到错误，Maybe 的单子复合会正确地**短路**整个计算（延续 `k` 永远不会被调用）。这正是我们期待异常具有的行为。

（定律的证明需要 `cases x`：只有知道 `x` 是 `nothing` 还是 `just a`，bind 的模式匹配才能“算下去”。）

核心库的 `Option` 与 `Except` 是同样的东西，而且 `Except` 还配有 `throw` 和 `tryCatch`：

```lean
end My

def divE (x y : Nat) : Except String Nat :=
  if y == 0 then throw s!"不能用 0 去除 {x}" else pure (x / y)

def calc3 : Except String Nat := do
  let a ← divE 100 5
  let b ← divE a 0          -- 在这里“抛出异常”
  return a + b              -- 这一行永远不会执行

#guard calc3 == .error "不能用 0 去除 20"
#guard (tryCatch calc3 fun _ => pure 0) == .ok 0
```

::: tip Rust 视角：`Result` 与 `?`
`Except ε α` 就是 Rust 的 `Result<α, ε>`（注意参数顺序相反）。Rust 的 `?` 正是 `Except` 单子的 bind：遇到 `Err` 就提前返回，否则取出 `Ok` 里的值继续。`tryCatch` 对应 `match`/`or_else`。区别还是那一条：Rust 为这一种效应专门发明了 `?`，Lean 的 `do` 则对所有单子通用。
:::

### 延续

这是面试之后你常会遇到的那种“别打给我们，我们会打给你！”的情形。你得不到一个直接的答复，而是需要提供一个处理器（handler），一个将来会被以结果调用的函数。当结果在调用时还未知——比如它正在被另一个线程计算，或者要从某个远程网站送达——这种编程风格特别有用。这时，Kleisli 箭头返回的是一个接受处理器的函数，处理器代表“计算的其余部分”：

```lean
namespace My

structure Cont (r : Type) (α : Type) where
  run : (α → r) → r
```

处理器 `α → r` 最终被调用时会产生一个 `r` 类型的结果，这个结果在最后被返回。延续以结果类型为参数。（实践中，它往往是某种状态指示码。）

还有一个辅助函数，用来执行 Kleisli 箭头返回的动作。它接收处理器，并把它交给延续：

```lean
def runCont (k : Cont r α) (h : α → r) : r := k.run h
```

延续的复合是出了名的难，所以通过单子、尤其是 `do` 记法来处理它，优势巨大。

我们来推导 bind 的实现。先看去掉包装后的签名：

```lean no-check
bind : ((α → r) → r) → (α → (β → r) → r) → ((β → r) → r)
```

我们的目标是构造一个函数，它接受处理器 `(β → r)`，产出结果 `r`。这就是我们的起点：

```lean no-check
bind ka kab := ⟨fun hb => _⟩
```

在 lambda 内部，我们要用恰当的处理器去调用函数 `ka`，这个处理器代表计算的其余部分。我们把这个处理器实现为一个 lambda：

```lean no-check
runCont ka (fun a => _)
```

这里，“计算的其余部分”包括：先用 `a` 调用 `kab`，再把 `hb` 交给得到的动作 `kb`：

```lean no-check
runCont ka (fun a =>
  let kb := kab a
  runCont kb hb)
```

你看，延续是**由内而外**复合的。最终的处理器 `hb` 是在计算的最内层被调用的。完整的实例如下：

```lean
instance : Monad (Cont r) where
  pure a := ⟨fun ha => ha a⟩
  bind ka kab := ⟨fun hb => runCont ka (fun a => runCont (kab a) hb)⟩

instance : LawfulMonad (Cont r) := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun _ _ _ => rfl)
```

（又是三个 `rfl`！Reader、State、Cont 这些“由函数构成”的单子，定律在定义上就成立；而 Maybe、List 这些“由数据构成”的单子，则需要分情况或归纳。）

延续的威力在于：既然“计算的其余部分”被具体化成了一个函数，我们就能操纵它——比如**不调用它**，提前跳出；或者调用它好几次。经典的操作是 `callCC`（call with current continuation，“以当前延续调用”）：它把“当前延续”作为一个可以随时调用的“逃生出口”交给你。

```lean
def callCC (f : (α → Cont r β) → Cont r α) : Cont r α :=
  ⟨fun h => runCont (f fun a => ⟨fun _ => h a⟩) h⟩

def safeDiv (x y : Nat) : Cont r (Except String Nat) := callCC fun exit => do
  if y == 0 then exit (.error "除以零")   -- 直接跳到最外层，后面的代码被跳过
  return .ok (x / y)

#guard runCont (safeDiv 10 2) id == .ok 5
#guard runCont (safeDiv 10 0) id == .error "除以零"

end My

example : My.runCont (do let a ← pure 1; let b ← pure 2; return a + b : My.Cont Nat Nat) id = 3 := rfl
```

`exit` 被调用时，它**丢弃**了自己的延续 `_`（也就是 `do` 块里后面的那几行），直接把结果交给最外层的处理器 `h`。这就是用纯函数实现的“提前返回”乃至“异常”。

::: tip Lean 核心库里的延续
Lean 核心库没有通用的 `ContT`，但有两个“用延续实现”的单子变换器：`StateCpsT` 和 `ExceptCpsT`。它们对外的接口和 `StateT`、`ExceptT` 完全一样，内部却是 CPS（延续传递风格）的，在某些场景下更快——Lean 编译器自己就在用它们。
:::

::: tip Rust 视角：回调与 `async`
在 Rust 里，“提供一个处理器”就是传一个闭包 `impl FnOnce(A) -> R`。层层嵌套的回调就是“回调地狱”，而 `async`/`await` 正是把它压平的语法：编译器把 `.await` 之后的代码变成一个状态机——本质上是延续的一种高效表示。上一章说过，C++ 的 future 构成一个延续单子；Rust 的 `Future` 也一样。
:::

### 交互式输入

这是最棘手的问题，也是许多困惑的源头。显然，像 `getChar` 这样的函数，如果它要返回键盘上敲入的字符，就不可能是纯的。但如果它把字符装在一个**容器**里返回呢？只要没有办法把字符从这个容器里取出来，我们就可以宣称这个函数是纯的。每次调用 `getChar`，它都会返回**一模一样**的容器。从概念上说，这个容器里装的是所有可能字符的叠加态。

如果你熟悉量子力学，理解这个类比应该毫无困难。它就像那个装着薛定谔的猫的盒子——只不过没有任何办法打开盒子、或者往里偷看。这个盒子是用特殊的、内建的 `IO` 函子定义的。在我们的例子里，`getChar` 可以被声明为一个 Kleisli 箭头：

```lean no-check
getChar : Unit → IO Char
```

（实际上，由于从单位类型出发的函数等价于挑出返回类型中的一个值，`getChar` 的声明简化为 `getChar : IO Char`。在 Lean 里，读取一行输入是 `(← IO.getStdin).getLine : IO String`。）

作为一个函子，`IO` 允许你用 `map` 操纵它的内容。而且作为函子，它可以存放任何类型的内容，不只是字符。当你想到 `IO` 是一个**单子**时，这种做法的真正价值就显露出来了。这意味着你能够复合那些产生 `IO` 对象的 Kleisli 箭头。

```lean
def askName : IO String := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  return line.trimAscii.toString
```

你可能以为 Kleisli 复合能让你偷看 `IO` 对象里的内容（如果继续量子的类比，那就是“让波函数坍缩”）。确实，你可以把 `getChar` 和另一个 Kleisli 箭头复合，后者接受一个字符，比如说把它转换成整数。问题在于，这第二个 Kleisli 箭头只能把这个整数作为 `IO Int` 返回。你又一次得到了所有可能整数的叠加态。如此循环往复。薛定谔的猫永远出不了口袋。一旦进入 `IO` 单子，就再也出不去了。对 `IO` 单子来说，没有 `runState` 或 `runReader` 的等价物。**没有 `runIO`！**

::: warning Lean 深入：真的出不去吗？
Lean 核心库里其实有 `unsafeBaseIO : BaseIO α → α` 和 `unsafeIO : IO α → Except IO.Error α`。但它们被标记为 `unsafe def`：任何用到它们的定义也必须标记为 `unsafe`，而 `unsafe` 的定义**不能出现在任何证明里**，也不能被普通的 `def` 调用。所以在“纯的、可证明的”Lean 世界里，`IO` 依然是一条单行道。（这对应原书提到的 Haskell `unsafePerformIO`——“那是另一个故事了”。）
:::

那么，除了把它和另一个 Kleisli 箭头复合之外，你还能拿 Kleisli 箭头的结果——`IO` 对象——做什么呢？嗯，你可以从 `main` 里返回它。在 Lean 中，`main` 的签名是：

```lean no-check
def main : IO Unit
-- 或者需要命令行参数和退出码时：
def main (args : List String) : IO UInt32
```

你完全可以把它看作一个 Kleisli 箭头：

```lean no-check
main : Unit → IO Unit
```

从这个角度看，一个程序不过是 `IO` 单子中的一个大大的 Kleisli 箭头。你可以用单子复合，把它由许多更小的 Kleisli 箭头拼装起来。至于拿得到的 `IO` 对象（也叫 `IO` 动作）去做什么，那是运行时系统的事。

注意，箭头本身是一个纯函数——一路往下全是纯函数。脏活儿被下放给了系统。当系统最终执行 `main` 返回的 `IO` 动作时，它会干各种龌龊的事：读取用户输入、修改文件、打印烦人的消息、格式化硬盘，诸如此类。程序本身从不弄脏自己的手（好吧，除了调用 `unsafePerformIO` 的时候，但那是另一个故事了）。

当然，因为 Haskell 是惰性的，`main` 几乎立即返回，脏活儿随即开始。正是在执行 `IO` 动作的过程中，纯计算的结果才被按需请求和求值。所以实际上，程序的执行是纯的（Haskell）代码和脏的（系统）代码的交错。（Lean 是严格的，没有这种按需求值的交错：但 `IO` 动作本身仍然是一个**值**，只有当运行时把它“跑起来”时，效应才会发生——下面马上会看到 Lean 里这个值究竟是什么。）

`IO` 单子还有另一种解读，它更加离奇，但作为数学模型却完全说得通。它把**整个宇宙**当作程序中的一个对象。注意，从概念上说，命令式模型把宇宙看作一个外部的全局对象，所以执行 I/O 的过程之所以有副作用，正是因为它们和这个对象发生了交互。它们既能读取、也能修改宇宙的状态。

我们已经知道在函数式编程里怎样处理状态——用状态单子。然而，和简单的状态不同，宇宙的状态没法用标准数据结构轻易描述。不过我们也不需要描述它，只要我们从不直接和它打交道就行。只需假设存在一个类型 `RealWorld`，并且凭借某种宇宙工程的奇迹，运行时能够提供一个这种类型的对象。一个 `IO` 动作就只是一个函数：

```lean no-check
IO α  ≈  RealWorld → (α × RealWorld)
```

或者，用 `State` 单子的话说：

```lean no-check
IO  ≈  State RealWorld
```

然而，`IO` 单子的 `>=>` 和 `pure` 必须内建在语言里。

**在 Lean 里，这不是比喻，而是字面上的定义。** Lean 4 的 `IO` 就是这样实现的，我们可以用 `rfl` 一层一层地验证：

```lean
-- IO 是“可能抛出 IO.Error 的” EIO
example (α : Type) : IO α = EIO IO.Error α := rfl
-- EIO 是以 IO.RealWorld 为状态的 EST（带异常的状态单子）
example (ε α : Type) : EIO ε α = EST ε IO.RealWorld α := rfl
-- EST 就是一个“吃进世界、吐出结果和新世界”的函数
example (ε σ α : Type) : EST ε σ α = (Void σ → EST.Out ε σ α) := rfl
-- 不会失败的 IO 叫 BaseIO，它就是 ST IO.RealWorld
example (α : Type) : BaseIO α = ST IO.RealWorld α := rfl
```

这里 `EST.Out ε σ α` 有两个构造子：`ok (a : α) (s : Void σ)` 和 `error (e : ε) (s : Void σ)`——也就是“结果（或错误）加上新的世界状态”。`IO.RealWorld` 本身是一个**不透明**的类型：你没有任何办法构造它的值、查看它的内容，只有运行时能提供它。Lean 的 `IO` 正是原书所说的“`State RealWorld`，再加上异常”。而 bind 的实现（`EST.bind`）在核心库里由编译器特殊处理，这对应原书那句“必须内建在语言里”。

::: tip Lean 深入：`#eval` 能运行 `IO`
如果你 `#eval` 一个类型为 `IO α` 的项，Lean 不会只是把这个“动作值”打印出来，而是会**执行**它——Lean 的编辑器/编译器前端本身就运行在 `IO` 里，它扮演了“运行时系统”的角色，提供了那个世界状态。这就是为什么你能在编辑器里直接看到 `IO.println` 的输出。但请注意，这只在 `#eval` 这个**元层面**的命令里发生；在你的定义和证明里，`IO` 动作依然只是一个不可打开的值。
:::

### 交互式输出

同一个 `IO` 单子也用来封装交互式输出。`RealWorld` 被认为包含了所有的输出设备。你可能会好奇，为什么我们不能直接从程序里调用输出函数，然后假装它们什么都没做？比如，为什么是：

```lean no-check
IO.print : String → IO Unit
```

而不是更简单的：

```lean no-check
IO.print : String → Unit
```

原书给了两个理由。第一，Haskell 是惰性的，它永远不会去调用一个输出——这里是单位对象——不被任何地方使用的函数。第二，即便它不是惰性的，它仍然可以自由地改变这类调用的顺序，从而把输出搞乱。在 Haskell 里，强制两个函数顺序执行的唯一办法是**数据依赖**：一个函数的输入必须依赖另一个函数的输出。让 `RealWorld` 在 `IO` 动作之间传递，就强制了顺序。

Lean 是严格的，第一个理由看似不成立了——但第二个理由在 Lean 里**同样成立**，而且还多了一条：既然 `String → Unit` 是一个纯函数，编译器就有权假设“调用它两次和调用一次没有区别”、“结果没被用到就可以不调用”，甚至在证明里，`print "a"` 和 `print "b"` 都等于 `()`，于是**相等**！一旦允许纯函数有副作用，等式推理就全盘崩溃了。（Lean 确实有一个刻意破坏这条规则的调试工具 `dbg_trace`，它的文档明确说它只用于调试，输出何时出现、是否出现都没有保证。）

从概念上说，在下面这个程序里：

```lean
def main : IO Unit := do
  IO.print "Hello "
  IO.println "World!"

#eval main
```

打印 `"World!"` 的那个动作，接收到的输入是一个屏幕上已经有了 `"Hello "` 的宇宙。它输出一个新的宇宙，屏幕上显示着 `"Hello World!"`。

（在本书的校验脚本里，`#eval main` 真的会打印出 `Hello World!`——编译器替我们扮演了宇宙。）

## 结论

当然，我只是触及了单子编程的皮毛。单子不仅用纯函数完成了命令式编程中通常靠副作用完成的事，而且做得高度可控、类型安全。不过它们也不是没有缺点。对单子最主要的抱怨是：它们彼此之间不容易复合。诚然，借助**单子变换器**（monad transformer）库，你可以把大多数基本单子组合起来。构造一个结合了比如状态和异常的“单子栈”相对容易，但并不存在一个能把任意单子堆叠起来的通用公式。

::: tip Lean 深入：单子变换器
Lean 核心库自带了一套变换器：`StateT σ m`、`ReaderT ρ m`、`ExceptT ε m`、`OptionT m`。`StateM σ` 不过是 `StateT σ Id`，`ReaderM ρ` 是 `ReaderT ρ Id`。下面把“状态”叠在“异常”之上：

```lean
abbrev Calc := StateT Nat (Except String)

def step (d : Nat) : Calc Unit := do
  let n ← get
  if d == 0 then throw "除以零"      -- 来自内层的 Except
  set (n / d)                        -- 来自外层的 StateT

#guard (do step 2; step 5 : Calc Unit).run 100 == .ok ((), 10)
#guard (do step 2; step 0; step 5 : Calc Unit).run 100 == .error "除以零"
```

注意 `throw` 是内层单子 `Except` 的操作，却可以直接在 `Calc` 里使用：这要归功于类型类 `MonadLift` 和 `MonadExcept`，Lean 会自动把内层的操作“提升”到外层。至于“为什么任意两个单子不能随便复合”，我们在后面讲范畴论视角下的单子时还会回到这个问题。
:::

## 练习（本书补充）

原书本章没有挑战题。下面几道练习帮助你巩固本章内容。

1. 用核心库的 `StateM` 实现一个栈机：`push : Nat → StateM (List Nat) Unit` 和 `pop : StateM (List Nat) (Option Nat)`，并计算 `push 1; push 2; let a ← pop; push 3; pop` 的结果和终态。
2. 给 `My.Reader` 写一个 `local`（Lean 核心叫 `withReader`）：`local (f : e → e) (r : Reader e α) : Reader e α`，它在一个被修改过的环境中运行 `r`。证明 `local id r = r`。
3. 用列表单子写出 `[1, 2, 3]` 的所有排列 `perms : List Nat → List (List Nat)`，并用 `#guard` 检查 `perms [1, 2, 3]` 的长度为 6。

::: details 参考答案
```lean
-- 1
def push (n : Nat) : StateM (List Nat) Unit := modify (n :: ·)

def pop : StateM (List Nat) (Option Nat) := do
  match (← get) with
  | [] => return none
  | x :: xs => set xs; return some x

#guard Id.run ((do push 1; push 2; let _ ← pop; push 3; pop).run []) == (some 3, [1])

-- 2
def My.Reader.local (f : e → e) (r : My.Reader e α) : My.Reader e α := ⟨fun env => r.run (f env)⟩

theorem My.Reader.local_id (r : My.Reader e α) : My.Reader.local id r = r := rfl

-- 3（partial：递归时列表在变短，但我们这里不想费事证明终止性）
partial def perms : List Nat → List (List Nat)
  | [] => [[]]
  | xs => do
    let x ← xs
    let rest ← perms (xs.erase x)
    return x :: rest

#guard (perms [1, 2, 3]).length == 6
#guard perms [1, 2, 3] == [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]]
```
:::

## 本章小结

- Moggi 的清单：偏函数性、非确定性、只读/只写/读写状态、异常、延续、交互式输入输出——传统上都要放弃纯粹性，但都能用“修饰返回类型”来解决；当我们要求**复合**时，修饰就成了单子。
- 偏函数性：Haskell 把所有类型提升（加 ⊥）；Lean 是全函数语言，用 `partial def` 隔离不终止的计算，或用 `Option` 显式表示“没算完”。
- 非确定性：列表单子，`pure x = [x]`，bind 是 `flatMap`，`join` 是 `flatten`；`guard` 负责剪枝。Lean 核心库刻意不提供 `Monad List`，本章自己实现并证明了定律；列表推导式可以用 Lean 宏自制。
- 只读状态是 Reader（`e → α`），只写状态是 Writer（`α × w`，`w` 是幺半群），读写状态是 State（`s → α × s`）。核心库有 `ReaderM`、`StateM` 及 `get`/`set`/`modify`，没有 Writer。
- 异常：`Option` 和 `Except`，bind 负责短路；Rust 的 `?` 就是它们的 bind。
- 延续：`Cont r α = (α → r) → r`，由内而外复合；`callCC` 能把“计算的其余部分”当作值来操纵。
- 由函数构成的单子（Reader、State、Cont）的定律都是 `rfl`；由数据构成的单子（Maybe、List、Writer）的定律要靠分情况、归纳或幺半群定律。
- `IO`：一旦进入就出不来（没有安全的 `runIO`）；Lean 的 `IO` 在字面上就是以不透明的 `IO.RealWorld` 为状态的“状态 + 异常”单子，`#eval` 由编译器扮演运行时来执行它。
- 单子不容易彼此复合；单子变换器（`StateT`、`ExceptT`……）能解决常见的组合。
