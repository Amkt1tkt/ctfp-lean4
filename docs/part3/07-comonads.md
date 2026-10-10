# 3.7 余单子

单子已经讲完了。接下来我们可以坐享对偶性的红利：把所有箭头掉个头、换到对偶范畴里去工作，余单子就几乎白送到手上。

先回忆单子最本质的用途：复合 Kleisli 箭头。一支 Kleisli 箭头长这样：

```lean no-check
a → m b
```

其中 `m` 是一个单子函子。余单子习惯用字母 `w` 表示（把 `m` 倒过来写），**co-Kleisli 箭头**就是把上面的箭头反过来——修饰从“结果”挪到了“参数”上：

```lean no-check
w a → b
```

Kleisli 箭头的“鱼”运算符 `>=>` 在这里也有一个对偶版本，写作 `=>=`：

```lean no-check
(=>=) : (w a → b) → (w b → c) → (w a → c)
```

co-Kleisli 箭头要构成范畴，还得有恒等箭头。这个恒等 co-Kleisli 箭头叫 `extract`：

```lean no-check
extract : w a → a
```

它是 `pure` 的对偶：`pure` 把一个值**放进**容器，`extract` 把一个值**取出来**。此外还要求 `=>=` 满足结合律，`extract` 满足左右单位律。把这些拼在一起，可以先写出余单子的“第一版”定义：

```lean
namespace FirstTry

/-- 以 co-Kleisli 复合和 extract 为原语的余单子（第一版）。 -/
class Comonad (w : Type → Type) extends Functor w where
  cokleisli : (w α → β) → (w β → γ) → (w α → γ)
  extract : w α → α

end FirstTry
```

实践中我们会换一套稍有不同的原语，马上就会看到。

那么问题来了：余单子在编程里到底有什么用？

## 用余单子编程

把单子和余单子并排比一比。

单子提供了一种**往容器里放值**的方法：`pure`。它可没承诺你能把值拿出来。当然，某些实现了单子的数据结构恰好允许你访问内容（比如 `List` 可以取第一个元素），但那是额外福利，不是单子接口的一部分：单子没有统一的“取出”接口。`IO` 就是个极端例子——它以从不暴露内部为荣，你永远拿不到一个“裸”的 `IO` 结果。

余单子恰恰相反：它提供了**取出一个值**的方法（`extract`），却不提供放入值的方法。如果非要把余单子想成容器，那它总是**出厂就装满了**，你能做的是往里看。

Kleisli 箭头接收一个值，产出一个带修饰的结果——它给结果附加了上下文。co-Kleisli 箭头则接收**一个值连同它的整个上下文**，产出一个结果。它是**上下文计算**（contextual computation）的化身。

::: tip Rust 视角
可以这样粗略类比：单子像 `Option::Some`、`Vec::from([x])`、`Box::new`——各种“包起来”的构造方式；余单子像一个**永远非空、带游标的视图**，比如

```rust
struct Zipper<T> {
    left: Vec<T>,  // 游标左边的元素（逆序存放）
    focus: T,      // 游标所在的元素——永远存在
    right: Vec<T>, // 游标右边的元素
}

impl<T: Clone> Zipper<T> {
    /// extract：直接读出游标处的值，不会失败
    fn extract(&self) -> T {
        self.focus.clone()
    }
}
```

当然，你也能从单个值造出一个 Zipper（左右都为空），但余单子接口并不要求这种能力。它真正关心的是：**站在游标处，结合周围的元素算出点什么**。
:::

## 积余单子

还记得 Reader 单子吗？我们引入它，是为了处理那些需要访问某个只读环境 `e` 的计算。这样的计算可以表示成纯函数：

```lean no-check
(a × e) → b
```

当时我们用柯里化把它们变成了 Kleisli 箭头：

```lean no-check
a → (e → b)
```

但请注意：这些函数**本来就已经是** co-Kleisli 箭头的形状了。只要把参数整理成更方便的函子形式就行：

```lean
/-- 积余单子（也常被叫作 Env 余单子）：一个值，外加一份环境。 -/
structure Product (e a : Type) where
  env : e
  val : a

instance : Functor (Product e) where
  map f p := ⟨p.env, f p.val⟩
```

复合运算很好定义：让参与复合的两支箭头看到**同一份**环境即可：

```lean
/-- 积余单子的 co-Kleisli 复合：先用 f 算出 b，再把 b 和原来的环境一起交给 g。 -/
def Product.cokleisli (f : Product e a → b) (g : Product e b → c) : Product e a → c :=
  fun p =>
    let b := f p
    let c := g ⟨p.env, b⟩
    c
```

`extract` 则干脆无视环境：

```lean
def Product.extract (p : Product e a) : a := p.val
```

积余单子能完成的计算，和 Reader 单子一模一样，这毫不奇怪。从某种意义上说，用余单子来实现“环境”更自然——它贴合“在上下文中计算”的精神。另一方面，单子自带 `do` 记法这样方便的语法糖。

::: tip Lean 深入：“一模一样”是一条定理
我们可以把上面那句话写成一条 Lean 定理：用柯里化把 co-Kleisli 箭头转成 Reader 的 Kleisli 箭头，**复合也随之对应**：

```lean
/-- co-Kleisli 箭头 Product e a → b  ↦  Reader 风格的 Kleisli 箭头 a → (e → b) -/
def toReaderK (f : Product e a → b) : a → e → b := fun x env => f ⟨env, x⟩

/-- Reader 单子的 Kleisli 复合：把同一个环境传给两支箭头 -/
def readerFish (f : a → e → b) (g : b → e → c) : a → e → c := fun x env => g (f x env) env

theorem toReaderK_cokleisli (f : Product e a → b) (g : Product e b → c) :
    toReaderK (Product.cokleisli f g) = readerFish (toReaderK f) (toReaderK g) := rfl
```
:::

Reader 单子和积余单子之间的联系还要更深一层，这和“Reader 函子是积函子的右伴随”这一事实有关（本章后面的 Store 余单子会再次用到这对伴随）。不过一般来说，余单子覆盖的计算概念和单子并不相同。后面我们会看到更多例子。

把 `Product` 余单子推广到任意积类型（包括多元组和记录，也就是 Lean 的 `structure`）是很容易的事。

## 剖析复合

沿着对偶化的路子继续走，我们可以直接把单子的 bind 和 join 对偶过来。不过我觉得更有启发性的做法，是重复当初研究单子时的套路：解剖“鱼”运算符。

出发点是这样一个认识：复合运算必须产出一支 co-Kleisli 箭头，它接收 `w a`、产出 `c`。而要产出 `c`，**唯一**的办法是把第二支箭头作用在一个 `w b` 类型的参数上：

```lean no-check
def cokleisli (f : w a → b) (g : w b → c) : w a → c :=
  fun x => g ...   -- 这里需要一个 w b
```

可是上哪儿去弄一个 `w b` 交给 `g` 呢？手头只有类型为 `w a` 的参数和函数 `f : w a → b`。解决办法是定义 bind 的对偶，叫 **extend**：

```lean no-check
extend : (w a → b) → w a → w b
```

有了 `extend`，复合就水到渠成：

```lean no-check
f =>= g = g ∘ extend f
```

接下来能不能再解剖 `extend`？你也许会想：把函数 `w a → b` 作用在参数 `w a` 上不就行了？但很快就会发现，这样得到的是一个 `b`，而你没有任何办法把 `b` 变成 `w b`——别忘了，余单子不提供“放入”值的方法。在单子的对应构造里，此时我们用的是 `fmap`（Lean 里是 `<$>`）。要在这里用上 `<$>`，前提是手里有一个 `w (w a)`。要是能把 `w a` 变成 `w (w a)` 就好了。巧的是，这恰恰就是 `join` 的对偶，我们叫它 **duplicate**：

```lean no-check
duplicate : w a → w (w a)
```

于是，和单子的情形一样，余单子也有三种等价的定义方式：用 co-Kleisli 箭头、用 `extend`、或者用 `duplicate`。下面是 Lean 版的定义，它照搬了 Haskell `Control.Comonad` 库的结构：

```lean
class Comonad (w : Type → Type) extends Functor w where
  extract : w α → α
  duplicate : w α → w (w α) := fun x => extend id x
  extend : (w α → β) → w α → w β := fun f x => f <$> duplicate x

export Comonad (extract duplicate extend)

/-- co-Kleisli 复合：先 f 后 g。 -/
def cokleisli [Comonad w] (f : w α → β) (g : w β → γ) : w α → γ :=
  g ∘ extend f

infixr:55 " =>= " => cokleisli
```

`duplicate` 和 `extend` 都带有用对方表示的默认实现，所以写实例时只需覆盖其中一个。

::: tip Lean 深入：互相引用的默认实现
类字段可以有默认值（`:= …`），默认值里还可以引用别的字段。这里 `duplicate` 的默认值用到 `extend`，`extend` 的默认值又用到 `duplicate`——互相引用。

在 Haskell 里，如果你两个都忘了写，程序照样能编译，运行时却会陷入无限循环。Lean 更严格：如果一个实例既不提供 `duplicate` 也不提供 `extend`，编译器会直接报错 `Fields missing: 'duplicate', 'extend'`，因为它发现无法用有限步把默认值解开。
:::

这些函数背后的直觉是这样的：一般而言，余单子可以想成一个装满了 `a` 类型值的容器（积余单子是只装一个值的特例）。容器里有一个“当前”值的概念，可以用 `extract` 轻松拿到。co-Kleisli 箭头执行的计算**以当前值为焦点**，但它能看到周围所有的值。

想想 Conway 的生命游戏。每个格子里有一个值（通常就是 `true` 或 `false`）。与生命游戏对应的余单子，是一张聚焦在“当前”格子上的网格。

那么 `duplicate` 做了什么？它接收一个余单子容器 `w a`，产出一个“容器的容器” `w (w a)`。这里的想法是：内层的每个容器都聚焦在原容器中**不同的**那个 `a` 上。在生命游戏里，你会得到一张“网格的网格”：外层网格的每个格子里装着一整张内层网格，各自聚焦在不同的格子上。

再看 `extend`。它接收一支 co-Kleisli 箭头和一个装满 `a` 的余单子容器 `w a`，把计算作用到所有这些 `a` 上，把它们一一替换成 `b`，结果是装满 `b` 的余单子容器。`extend` 的做法是把焦点从一个 `a` 挪到另一个 `a`，轮流对每个焦点施加 co-Kleisli 箭头。在生命游戏里，co-Kleisli 箭头负责计算当前格子的下一个状态；为此它要观察上下文——大概就是它最近的邻居。`extend` 的默认实现把这个过程表达得很清楚：先调用 `duplicate` 产生所有可能的焦点，再对每个焦点调用 `f`。

### 补充：余单子定律，以及它们为什么让 co-Kleisli 箭头成为范畴

把定律写成一个 Lean 类型类。前三条是用 `extend` 表述的余单子定律（它们正是 bind 定律的镜像），后两条保证 `extend` 与 `duplicate` 两套原语彼此一致：

```lean
class LawfulComonad (w : Type → Type) [Comonad w] extends LawfulFunctor w where
  /-- 用 extract 去 extend，什么也不变 -/
  extend_extract : ∀ {α} (x : w α), extend extract x = x
  /-- extend f 之后再 extract，等于直接用 f -/
  extract_extend : ∀ {α β} (f : w α → β) (x : w α), extract (extend f x) = f x
  /-- 连续两次 extend 可以合成一次 -/
  extend_extend : ∀ {α β γ} (f : w α → β) (g : w β → γ) (x : w α),
    extend g (extend f x) = extend (g ∘ extend f) x
  /-- extend 与 duplicate 的关系 -/
  extend_def : ∀ {α β} (f : w α → β) (x : w α), extend f x = f <$> duplicate x
  duplicate_def : ∀ {α} (x : w α), duplicate x = extend id x
```

有了这些定律，co-Kleisli 箭头确实构成一个范畴：`extract` 是恒等箭头，`=>=` 满足结合律。每条证明都只有一行：

```lean
namespace LawfulComonad
variable {w : Type → Type} [Comonad w] [LawfulComonad w]

theorem cokleisli_extract_left (f : w α → β) : (extract =>= f) = f := by
  funext x; simp [cokleisli, extend_extract]

theorem cokleisli_extract_right (f : w α → β) : (f =>= extract) = f := by
  funext x; simp [cokleisli, extract_extend]

theorem cokleisli_assoc (f : w α → β) (g : w β → γ) (h : w γ → δ) :
    ((f =>= g) =>= h) = (f =>= (g =>= h)) := by
  funext x; simp [cokleisli, extend_extend]

end LawfulComonad
```

积余单子当然满足这些定律，而且全都是 `rfl`：

```lean
instance : Comonad (Product e) where
  extract p := p.val
  duplicate p := ⟨p.env, p⟩          -- 外层环境不变，内层就是原来的整个 p
  extend f p := ⟨p.env, f p⟩

instance : LawfulComonad (Product e) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
  extend_extract _ := rfl
  extract_extend _ _ := rfl
  extend_extend _ _ _ := rfl
  extend_def _ _ := rfl
  duplicate_def _ := rfl
```

## 流余单子

把焦点从容器的一个元素挪到另一个元素的这个过程，最好用无限流的例子来演示。这样的流就像列表，只是没有表示“空”的那个构造子。照抄 Haskell 的定义，在 Lean 里会写成：

```lean
inductive BadStream (α : Type) where
  | cons : α → BadStream α → BadStream α
```

可惜这个名字里的 `Bad` 不是白起的：在 Lean 里，这样定义出来的类型一个值都没有。所以我们实际使用的是下面补充小节里的 `Stream'`。

### 补充：Lean 里怎样表示无限流

上面那句定义，Lean 并不会拒绝，但它定义出来的是一个**空类型**！Lean 的 `inductive` 只允许**有限**深度的值：每个值都必须能由构造子在有限步内搭出来。而 `cons` 要求先有一个 `BadStream` 才能造出下一个，没有起点，于是一个值也造不出来。用归纳法可以证明这一点：

```lean
theorem BadStream.isEmpty (s : BadStream α) : False := by
  induction s with
  | cons _ _ ih => exact ih     -- 尾巴是空的，所以整个也是空的
```

Haskell 能用这个定义，靠的是**惰性求值**：`Cons 1 ones` 中的尾部是一个尚未求值的 thunk，它可以“指回自己”。代价是 Haskell 的类型里处处潜伏着 ⊥（不终止的值），类型系统没法区分“真正的无限流”和“算到一半就卡死的东西”。

那么 Lean 4 有没有**余归纳类型**（codata）呢？我在本书使用的 Lean 4.34.1 上实际检查过：

- Lean 有 `coinductive` 关键字，但**只能用来定义命题（谓词）**，不能定义数据类型。尝试写
  `coinductive Stream' (α : Type) : Type where | cons : α → Stream' α → Stream' α`
  会得到报错：`` `coinductive` keyword can only be used to define predicates ``。
- 把 `inductive` 的尾巴包进 `Thunk`（或 `Unit → …`）同样无济于事：类型依然是归纳定义的，依然是空的。想用 `partial def ones := cons 1 (fun _ => ones)` 硬造一个值也不行——`partial def` 要求返回类型有 `Inhabited` 实例，而一个空类型根本拿不出这样的实例。
- 核心库里的 `Std.Stream` 是另一回事：它是“能不断 `next?` 的迭代器”协议，可以结束，也不是余单子。

所以在 Lean 里，我们用一种完全不依赖惰性的表示：**流就是从自然数到值的函数**。第 `n` 个元素就是 `get n`。这其实是数学上最直接的定义（Mathlib 里的 `Stream'` 也正是这么定义的）。它天生是“惰性”的：函数在被调用之前不会计算任何元素。

```lean
/-- 无限流：第 n 个元素是 get n。 -/
structure Stream' (α : Type) where
  get : Nat → α

namespace Stream'
def head (s : Stream' α) : α := s.get 0
/-- 去掉第一个元素（命令式语言里的 advance） -/
def tail (s : Stream' α) : Stream' α := ⟨fun n => s.get (n + 1)⟩
def cons (a : α) (s : Stream' α) : Stream' α := ⟨fun | 0 => a | n + 1 => s.get n⟩
/-- 一次去掉前 k 个元素 -/
def drop (k : Nat) (s : Stream' α) : Stream' α := ⟨fun n => s.get (k + n)⟩
/-- 取前 n 个元素做成列表，方便查看 -/
def take : Nat → Stream' α → List α
  | 0, _ => []
  | n + 1, s => s.head :: take n s.tail
def nats : Stream' Nat := ⟨id⟩
end Stream'

#guard Stream'.nats.take 5 == [0, 1, 2, 3, 4]
#guard (Stream'.cons 42 Stream'.nats).take 3 == [42, 0, 1]
```

::: tip Lean 深入：余归纳谓词确实可用
虽然没有余归纳**数据**，Lean 4.34.1 的 `coinductive` **谓词**是能用的，它非常适合描述“永远成立”的性质。例如“流里每个元素都满足 `p`”：

```lean
coinductive Always (p : α → Prop) : Stream' α → Prop where
  | step : p s.head → Always p s.tail → Always p s

def evens : Stream' Nat := ⟨fun n => 2 * n⟩

/-- 偶数流里永远是偶数。用余归纳原理 `Always.coinduct` 证明：
找一个“不变式” pred，证明它在头部成立并且能传给尾部。 -/
theorem evens_always_even : Always (fun n => n % 2 = 0) evens := by
  apply Always.coinduct _ (fun s => ∀ n, s.get n % 2 = 0)
  · intro s h
    exact ⟨h 0, fun n => h (n + 1)⟩   -- 头部满足；尾部仍满足不变式
  · intro n; show 2 * n % 2 = 0; omega
```

`omega` 是一个能自动证明整数/自然数线性算术命题的 tactic。
:::

### 流是余单子

流显然是一个 `Functor`：

```lean
instance : Functor Stream' where
  map f s := ⟨fun n => f (s.get n)⟩
```

流的焦点是它的第一个元素，所以 `extract` 的实现是：

```lean
def streamExtract (s : Stream' α) : α := s.head
```

`duplicate` 产出一条“流的流”，其中每条流聚焦在不同的元素上：

```lean
def streamDuplicate (s : Stream' α) : Stream' (Stream' α) := ⟨fun k => s.drop k⟩
```

第一个元素是原来的流本身，第二个元素是原流的尾巴，第三个元素是尾巴的尾巴，如此类推，直到永远。（用我们的表示，第 `k` 条就是 `drop k s`。）

完整的实例如下：

```lean
instance : Comonad Stream' where
  extract := streamExtract
  duplicate := streamDuplicate
  extend f s := ⟨fun k => f (s.drop k)⟩

-- duplicate 的第 3 条流从原流的第 3 个元素开始
#guard ((duplicate Stream'.nats).get 3).take 3 == [3, 4, 5]
```

定律的证明归结为 `0 + n = n` 和加法结合律：

```lean
instance : LawfulComonad Stream' where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
  extend_extract s := by
    show (⟨fun k => (s.drop k).get 0⟩ : Stream' _) = s
    simp [Stream'.drop]               -- k + 0 = k
  extract_extend f s := by
    show f (s.drop 0) = f s
    simp [Stream'.drop]               -- drop 0 s = s
  extend_extend f g s := by
    show (⟨fun k => g ⟨fun j => f (s.drop (k + j))⟩⟩ : Stream' _)
       = ⟨fun k => g ⟨fun j => f ((s.drop k).drop j)⟩⟩
    simp [Stream'.drop, Nat.add_assoc] -- drop j (drop k s) = drop (k + j) s
  extend_def _ _ := rfl
  duplicate_def _ := rfl
```

这是一种非常“函数式”的看流方式。在命令式语言里，我们大概会从一个把流前进一格的 `advance` 方法开始；而这里，`duplicate` 一口气产生了**所有**前进过的流。Haskell 的惰性让这件事可行，甚至令人乐于这么做；在 Lean 里，我们的“流 = 函数”表示同样做到了：`duplicate s` 只是一个函数，并不会真的把无穷多条流都算出来。当然，为了让 `Stream'` 实用，我们还会实现 `advance` 的对应物（前面补充小节里已经定义过了）：

```lean
example : Stream' α → Stream' α := Stream'.tail
example (s : Stream' α) : s.tail.get 0 = s.get 1 := rfl
```

但它从来不是余单子接口的一部分。

如果你做过数字信号处理，马上就会看出：流上的 co-Kleisli 箭头不过是一个**数字滤波器**，而 `extend` 产出的是滤波后的流。

举个简单的例子，我们实现移动平均滤波器。先写一个对流的前 `n` 个元素求和的函数：

```lean
def sumS (n : Nat) (s : Stream' Float) : Float :=
  (s.take n).foldl (· + ·) 0
```

再写一个计算流前 `n` 个元素平均值的函数：

```lean
def average (n : Nat) (s : Stream' Float) : Float :=
  sumS n s / n.toFloat
```

部分应用的 `average n` 就是一支 co-Kleisli 箭头（类型 `Stream' Float → Float`），所以可以把它 `extend` 到整条流上：

```lean
def movingAvg (n : Nat) : Stream' Float → Stream' Float :=
  extend (average n)

-- 0, 1, 2, 3, … 的 2 项移动平均
#guard (movingAvg 2 ⟨fun k => k.toFloat⟩).take 4 == [0.5, 1.5, 2.5, 3.5]
```

结果就是一条“滑动平均值”组成的流。

下面这个小工具把 `duplicate` 和 `extend` 画了出来：每一行是 `duplicate s` 中的一条流（焦点依次右移），右边一列是 co-Kleisli 箭头作用在这一行上的结果；底部那一行把这些结果排成一条新流——它就是 `extend f s`。换几个滤波器试试，特别是 `extract`：你会看到 `extend extract s = s`，这正是第一条余单子定律。

<div class="ctfp-widget-host"><Ch3_7StreamExtend /></div>

::: tip Rust 视角
对有限的数据，Rust 程序员每天都在写“extend”：

```rust
fn moving_avg(xs: &[f64], n: usize) -> Vec<f64> {
    // windows(n) 就是“所有焦点处的长度为 n 的上下文”（有限版的 duplicate），
    // map(...) 就是在每个焦点上运行同一个滤波器
    xs.windows(n)
        .map(|w| w.iter().sum::<f64>() / n as f64)
        .collect()
}
```

区别在于，有限切片的末尾窗口会“不够长”，所以 `windows` 产出的元素比输入少；无限流没有末尾，`extend` 总能保持形状不变。
:::

流是单向、一维余单子的例子。它很容易改成双向的（把 `Nat` 换成 `Int`），或者推广到二维乃至更高维（把下标换成 `Int × Int`……）。本章后面的 Store 余单子会把这个想法做到底。

## 范畴论视角下的余单子

在范畴论里定义余单子，就是一道直截了当的对偶化练习。和单子一样，我们从一个自函子 $T$ 出发。定义单子的两个自然变换 $\eta$ 和 $\mu$，在余单子这里被简单地反过来：

$$
\begin{aligned}
\varepsilon &:: T \to I \\
\delta &:: T \to T^2
\end{aligned}
$$

这两个变换的分量分别对应 `extract` 和 `duplicate`。余单子定律是单子定律的镜像，没什么意外：

```diagram
T: (0, 0) "T"
T2a: (2.6, 0) "T^2"
T2b: (0, 1.9) "T^2"
T3: (2.6, 1.9) "T^3"
d1: T -> T2a "\delta"
d2: T -> T2b "\delta" side=right
dT: T2a -> T3 "\delta \circ T"
Td: T2b -> T3 "T \circ \delta" side=right
path "δ 再 δ∘T（复制外层）": d1 dT
path "δ 再 T∘δ（复制内层）": d2 Td color=green
caption: 余单子的余结合律：(δ∘T) ∘ δ = (T∘δ) ∘ δ。和单子的结合律相比，所有箭头都反了过来。
```

```diagram
T: (2.2, 0) "T"
IT: (0, 1.7) "I \circ T"
TT: (2.2, 1.7) "T^2"
TI: (4.4, 1.7) "T \circ I"
d: T -> TT "\delta"
eT: TT -> IT "\varepsilon \circ T"
Te: TT -> TI "T \circ \varepsilon" side=right
idl: T -> IT "\mathrm{id}_T" side=right
idr: T -> TI "\mathrm{id}_T"
path "δ 再 ε∘T": d eT
path "直接 id（左）": idl color=green
path "δ 再 T∘ε": d Te color=orange
path "直接 id（右）": idr color=purple
caption: 余单子的两条余单位律：(ε∘T) ∘ δ = id_T = (T∘ε) ∘ δ。
```

把分量写出来：$(\varepsilon\circ T)_a = \varepsilon_{Ta}$ 就是作用在外层的 `extract`，$(T\circ\varepsilon)_a = T(\varepsilon_a)$ 就是 `extract <$> ·`；$(\delta\circ T)_a = \delta_{Ta}$ 是 `duplicate`（作用在外层），$(T\circ\delta)_a$ 是 `duplicate <$> ·`。这三张图对应的三条等式，可以从我们的 `LawfulComonad` 推出来：

```lean
namespace LawfulComonad
variable {w : Type → Type} [Comonad w] [LawfulComonad w]

/-- 左余单位律：ε_{T a} ∘ δ_a = id -/
theorem extract_duplicate (x : w α) : extract (duplicate x) = x := by
  rw [duplicate_def, extract_extend]; rfl

/-- 右余单位律：T(ε_a) ∘ δ_a = id -/
theorem map_extract_duplicate (x : w α) : extract <$> duplicate x = x := by
  rw [← extend_def, extend_extract]

/-- 余结合律：δ_{T a} ∘ δ_a = T(δ_a) ∘ δ_a -/
theorem duplicate_duplicate (x : w α) : duplicate (duplicate x) = duplicate <$> duplicate x := by
  rw [← extend_def, duplicate_def (duplicate x), duplicate_def x, extend_extend]
  congr 1
  funext y
  exact (duplicate_def y).symm

end LawfulComonad
```

接下来是“由伴随得到单子”的对偶。对偶会把伴随反过来：左伴随变成右伴随，反之亦然。既然复合 $R \circ L$ 定义了一个单子，那么 $L \circ R$ 必定定义一个余单子。伴随的余单位

$$\varepsilon :: L \circ R \to I$$

正是余单子定义里的那个 $\varepsilon$——写成分量，就是 `extract`。我们还可以用伴随的单位

$$\eta :: I \to R \circ L$$

在 $L \circ R$ 的中间插入一个 $R \circ L$，得到 $L \circ R \circ L \circ R$。从 $T$ 造出 $T^2$，这就定义了 $\delta$：

$$\delta = L \circ \eta \circ R$$

余单子的定义就此完成。

### 余幺半群

我们还看到，单子是一个幺半群。这句话的对偶需要用到**余幺半群**（comonoid）。那么什么是余幺半群呢？

“幺半群是单对象范畴”这个原始定义，对偶之后得不到什么有趣的东西：把所有自态射的方向反过来，你得到的还是一个幺半群。不过回忆一下，在讨论单子时，我们用的是更一般的定义：幺半群是幺半范畴中的一个对象，配上两个态射：

$$
\begin{aligned}
\mu &:: m \otimes m \to m \\
\eta &:: i \to m
\end{aligned}
$$

把这两个态射反过来，就得到幺半范畴中的余幺半群：

$$
\begin{aligned}
\delta &:: m \to m \otimes m \\
\varepsilon &:: m \to i
\end{aligned}
$$

在 Lean 里也可以写出余幺半群的定义（这里的张量积是 `×`，单位对象是 `Unit`）：

```lean
class Comonoid (m : Type) where
  split : m → m × m
  destroy : m → Unit
```

但这个定义相当平凡。显然，`destroy` 只能无视它的参数——到 `Unit` 的函数只有一个：

```lean
theorem destroy_unique (d : m → Unit) : d = fun _ => () := funext fun _ => rfl
```

`split` 不过是一对函数：

```lean no-check
split x = (f x, g x)
```

现在来看与幺半群单位律对偶的余幺半群定律：

```lean
def lambda : Unit × α → α := Prod.snd
def rho : α × Unit → α := Prod.fst

class LawfulComonoid (m : Type) [Comonoid m] : Prop where
  /-- λ ∘ (destroy × id) ∘ split = id -/
  left_counit : lambda ∘ Prod.map Comonoid.destroy id ∘ Comonoid.split = (id : m → m)
  /-- ρ ∘ (id × destroy) ∘ split = id -/
  right_counit : rho ∘ Prod.map id Comonoid.destroy ∘ Comonoid.split = (id : m → m)
```

这里的 `lambda` 和 `rho` 分别是左单位子和右单位子（见上一章[幺半范畴](/part3/06-monads-categorically#幺半范畴)的定义）。第一条定律画成图就是：先复制、再把左边那份“销毁”、最后用左单位子吃掉单位对象，结果等于什么也没做：

```diagram
M: (0, 0) "m"
MM: (2.2, 0) "m \otimes m"
IM: (4.4, 0) "i \otimes m"
M2: (2.2, 1.5) "m"
d: M -> MM "\delta"
e: MM -> IM "\varepsilon \otimes \mathrm{id}"
l: IM -> M2 "\lambda"
id: M -> M2 "\mathrm{id}" side=right
path "δ，ε⊗id，λ": d e l
path "直接 id": id color=green
caption: 余幺半群的左余单位律：λ ∘ (ε ⊗ id) ∘ δ = id。
```

把定义代进去，得到：

```lean
theorem left_counit_expand (f g : m → m) (x : m) :
    lambda (Prod.map (fun _ => ()) id ((fun y => (f y, g y)) x)) = g x :=
  calc lambda (Prod.map (fun _ => ()) id ((fun y => (f y, g y)) x))
      = lambda (Prod.map (fun _ => ()) id (f x, g x)) := rfl
    _ = lambda ((), g x) := rfl
    _ = g x := rfl
```

这就证明了 `g = id`。同理，第二条定律展开后得到 `f = id`。结论是：

```lean
/-- 在 Type 中，余幺半群的 split 只能是“复制”：split x = (x, x)。 -/
theorem comonoid_split_diag [Comonoid m] [LawfulComonoid m] (x : m) :
    Comonoid.split x = (x, x) := by
  have h1 : (Comonoid.split x).2 = x := congrFun LawfulComonoid.left_counit x    -- g = id
  have h2 : (Comonoid.split x).1 = x := congrFun LawfulComonoid.right_counit x   -- f = id
  exact Prod.ext h2 h1
```

反过来，“复制”也确实满足余幺半群定律，所以每个类型都恰好有一个余幺半群结构：

```lean
@[reducible] def diagComonoid (m : Type) : Comonoid m where
  split x := (x, x)
  destroy _ := ()

theorem diagComonoid_lawful (m : Type) : @LawfulComonoid m (diagComonoid m) :=
  @LawfulComonoid.mk m (diagComonoid m) rfl rfl
```

::: tip Lean 深入：`calc`
`calc` 把一串等式链接起来：每一行写 `_ = 下一个式子 := 理由`，Lean 会自动用传递性把它们拼成首尾相等的结论。这里每一步都只是展开定义，所以理由都是 `rfl`；写成 `calc` 是为了让读者看清楚每一步发生了什么。
:::

这说明：在 Lean 的类型范畴里（一般地，在 $\mathbf{Set}$ 中），每个对象都是一个平凡的余幺半群。

::: info 数学小课堂：为什么在 Set 里余幺半群这么无聊？
关键在于 $\times$ 是真正的**积**：一个映到 $m \times m$ 的函数，完全由它的两个分量（两个投影）决定；而余单位律恰好把这两个分量都钉死成了恒等函数。
换句话说，“复制”这件事在集合的世界里是免费且唯一的——你总可以把一个值抄两份。只有在“不能随便复制”的幺半范畴里（例如线性逻辑、量子计算中的范畴），余幺半群才变得有意思。
:::

幸运的是，还有别的、更有趣的幺半范畴可以用来定义余幺半群，其中之一就是自函子范畴。事实证明，就像单子是自函子范畴中的幺半群一样，

> 余单子是自函子范畴中的余幺半群。

在那里，张量积是函子复合，“复制”$\delta : T \to T\circ T$ 不再是免费的——它恰恰是 `duplicate`，需要每个余单子自己提供。

## Store 余单子

余单子的另一个重要例子是 State 单子的对偶。它叫做 **costate 余单子**，也叫 **store 余单子**。

我们之前看到，State 单子是由定义指数对象的那个伴随生成的：

$$
\begin{aligned}
L\, z &= z \times s \\
R\, a &= s \Rightarrow a
\end{aligned}
$$

我们用同一个伴随来定义 costate 余单子。余单子由复合 $L \circ R$ 定义：

$$L (R\, a) = (s \Rightarrow a) \times s$$

翻译成 Lean：我们从左边的积函子与右边的 Reader 函子之间的伴随出发。积函子 $L$ 恰好就是本章前面的 `Product s`（把一个值和一个 `s` 配成对）；Reader 函子我们在这里再定义一次：

```lean
/-- R a = s → a -/
structure Reader (s a : Type) where
  run : s → a
```

把 `Product` 复合在 `Reader` 之后，等价于下面这个定义：

```lean
/-- Store 余单子：一个“按 s 索引取值”的函数，外加当前位置。 -/
structure Store (s a : Type) where
  peek : s → a
  pos : s

instance : Functor (Store s) where
  map f w := ⟨f ∘ w.peek, w.pos⟩

/-- Store s a 与 Product s (Reader s a) 只是换了个包装 -/
def Store.toPR (w : Store s a) : Product s (Reader s a) := ⟨w.pos, ⟨w.peek⟩⟩
def Store.ofPR (p : Product s (Reader s a)) : Store s a := ⟨p.val.run, p.env⟩
theorem Store.of_to (w : Store s a) : Store.ofPR w.toPR = w := rfl
theorem Store.to_of (p : Product s (Reader s a)) : (Store.ofPR p).toPR = p := rfl
```

伴随的余单位在对象 $a$ 处的分量是态射

$$\varepsilon_a :: ((s \Rightarrow a) \times s) \to a$$

用 Lean 记号写就是：

```lean
/-- 伴随的余单位：L (R a) → a，也就是拿配对里的 s 去调用 Reader 里的函数 -/
def adjCounit (p : Product s (Reader s a)) : a := p.val.run p.env
```

它就成了我们的 `extract`：

```lean
def storeCounit (w : Store s a) : a := w.peek w.pos

theorem storeCounit_eq (w : Store s a) : storeCounit w = adjCounit w.toPR := rfl
```

伴随的单位：

```lean
/-- 伴随的单位：a → R (L a) -/
def adjUnit (x : a) : Reader s (Product s a) := ⟨fun s' => ⟨s', x⟩⟩
```

可以改写成部分应用的数据构造子。在构造 $\delta$ 时，我们需要的是 $\eta$ 在对象 $R\,a = s \Rightarrow a$ 处的分量，也就是让 `adjUnit` 作用在一个函数 `f : s → a` 上。它把 `f` 变成 `fun s' => (f, s')`——这正是**部分应用的构造子** `Store.mk f : s → Store s a`：

```lean
/-- 伴随的单位，作用在 R a 上：把 f 变成“等着接收一个位置的 Store” -/
def storeUnit (f : s → a) : s → Store s a := Store.mk f

theorem storeUnit_eq (f : s → a) (s' : s) :
    storeUnit f s' = Store.ofPR ((adjUnit (s := s) (Reader.mk f)).run s') := rfl
```

$\delta$（也就是 `duplicate`）由横向复合构造：

$$
\begin{aligned}
\delta &:: L \circ R \to L \circ R \circ L \circ R \\
\delta &= L \circ \eta \circ R
\end{aligned}
$$

我们要把 $\eta$ “偷运”过最左边的 $L$——也就是积函子。这意味着用 $\eta$（即 `Store.mk f`）作用在二元组的左分量上（积函子的 `map` 恰好会这么做）。得到：

```lean
def storeDuplicate (w : Store s a) : Store s (Store s a) := ⟨storeUnit w.peek, w.pos⟩
```

（别忘了，在 $\delta$ 的公式里，$L$ 和 $R$ 代表的是恒等自然变换，它们的分量都是恒等态射。）

下面是 `Store` 余单子的完整定义，以及定律的证明——全部是 `rfl`：

```lean
instance : Comonad (Store s) where
  extract := storeCounit
  duplicate := storeDuplicate
  extend f w := ⟨fun s' => f ⟨w.peek, s'⟩, w.pos⟩

instance : LawfulComonad (Store s) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
  extend_extract _ := rfl
  extract_extend _ _ := rfl
  extend_extend _ _ _ := rfl
  extend_def _ _ := rfl
  duplicate_def _ := rfl
```

你可以把 `Store` 的 Reader 部分想成一个广义的 `a` 的容器，它用 `s` 类型的元素做键（下标）。例如，如果 `s` 是 `Int`，那么 `Int → a` 就是一条**双向无限**的 `a` 流。`Store` 把这个容器和一个键类型的值配成一对。比如 `Int → a` 和一个 `Int` 配对，此时 `extract` 用这个整数去流里取值。你可以把 `Store` 的第二个分量理解为**当前位置**。

接着这个例子说，`duplicate` 会创建一条新的、以 `Int` 为下标的无限流，它的元素本身也是流。具体来说，在当前位置上，它装的就是原来那条流；而如果你用别的 `Int`（正的或负的）做键，得到的就是一条**平移**过、定位在那个新下标上的流。

```lean
def zs : Store Int Int := ⟨fun i => i * i, 3⟩     -- 平方数的双向流，焦点在 3

#guard extract zs == 9                              -- 当前位置的值
#guard extract ((duplicate zs).peek (-2)) == 4     -- 把焦点挪到 -2 的那条流
#guard (extract (duplicate zs)).pos == 3            -- 当前位置上装的就是原流
```

一般来说，你可以说服自己：`extract` 作用在 `duplicate` 过的 `Store` 上，会得到原来的 `Store`（事实上，余单子的恒等律正是说 `extract ∘ duplicate = id`，我们在上一节已经对一切合法余单子证明了 `extract_duplicate`）。

下面的小工具把 Store 余单子用到了一个经典场景：一维**元胞自动机**。纸带是 `Store (Fin 63) Bool`（首尾相接的 63 个格子），`peek` 是这一代所有格子的状态，`pos` 是焦点。co-Kleisli 箭头只看焦点和左右两个邻居，按规则表决定焦点下一代的状态；`extend` 则把焦点依次挪到每个格子上，把这个**局部规则推广到整条纸带**，产生下一代。点“慢动作”看焦点扫过纸带；试试 Rule 90（谢尔宾斯基三角形）和 Rule 30（看起来像随机数）。

<div class="ctfp-widget-host"><Ch3_7StoreAutomaton /></div>

### Store 与透镜

`Store` 余单子是 `lens` 库的理论基础，扮演着重要角色。从概念上说，`Store s a` 余单子封装了这样一个想法：以 `s` 类型为“下标”，**聚焦**（像透镜一样）在数据类型 `a` 的某个特定子结构上。具体来说，一个类型为

```lean no-check
a → Store s a
```

的函数，等价于一对函数：

```lean no-check
set : a → s → a
get : a → s
```

如果 `a` 是一个积类型，`set` 可以实现为“设置 `a` 内部那个 `s` 类型的字段，返回修改后的 `a`”；`get` 则可以实现为读出 `a` 中那个 `s` 类型字段的值。在 Lean 里，这个等价写起来只有几行，两个方向的往返都是 `rfl`：

```lean
/-- 透镜：把 a 聚焦到一个 s 类型的部分上。 -/
def Lens (a s : Type) := a → Store s a

def Lens.get (l : Lens a s) (x : a) : s := (l x).pos
def Lens.set (l : Lens a s) (x : a) (v : s) : a := (l x).peek v
def Lens.ofGetSet (get : a → s) (set : a → s → a) : Lens a s := fun x => ⟨set x, get x⟩

theorem Lens.ofGetSet_get_set (l : Lens a s) : Lens.ofGetSet l.get l.set = l := rfl
theorem Lens.get_ofGetSet (get : a → s) (set : a → s → a) : (Lens.ofGetSet get set).get = get := rfl
theorem Lens.set_ofGetSet (get : a → s) (set : a → s → a) : (Lens.ofGetSet get set).set = set := rfl
```

举个例子：

```lean
structure Point where
  x : Int
  y : Int

/-- 聚焦到 x 字段的透镜：pos 是当前的 x，peek v 是“把 x 换成 v 之后的点”。 -/
def Point.xL : Lens Point Int := fun p => ⟨fun v => { p with x := v }, p.x⟩

#guard Point.xL.get ⟨1, 2⟩ == 1
#guard (Point.xL.set ⟨1, 2⟩ 10).x == 10
#guard (Point.xL.set ⟨1, 2⟩ 10).y == 2
```

::: tip Rust 视角
在 Rust 里，透镜就是一对 getter/setter，只不过 setter 是“函数式”的：消耗旧值、返回新值，而不是 `&mut self` 原地修改。

```rust
#[derive(Clone, Copy, Debug, PartialEq)]
struct Point { x: i64, y: i64 }

/// get/set 形式的透镜
struct Lens<A, S> {
    get: fn(&A) -> S,
    set: fn(A, S) -> A,
}

fn x_lens() -> Lens<Point, i64> {
    Lens { get: |p| p.x, set: |p, v| Point { x: v, ..p } }
}

/// Store 形式：同一个透镜，写成 A -> Store<S, A>
struct Store<S, A> {
    peek: Box<dyn Fn(S) -> A>,
    pos: S,
}

fn x_store(p: Point) -> Store<i64, Point> {
    Store { peek: Box::new(move |v| Point { x: v, ..p }), pos: p.x }
}
```

`x_store(p)` 把“当前的 x”和“换掉 x 的办法”打包在一起：它聚焦在 `p` 的 `x` 字段上。
:::

一个“好”的透镜还应满足三条定律：读你写的（`get (set x v) = v`）、写你读的（`set x (get x) = x`）、后写覆盖先写（`set (set x v) v' = set x v'`）。对 `Point.xL`，它们都是 `rfl`：

```lean
theorem xL_get_set (p : Point) (v : Int) : Point.xL.get (Point.xL.set p v) = v := rfl
theorem xL_set_get (p : Point) : Point.xL.set p (Point.xL.get p) = p := rfl
theorem xL_set_set (p : Point) (v v' : Int) :
    Point.xL.set (Point.xL.set p v) v' = Point.xL.set p v' := rfl
```

::: details 补充：透镜定律 = Store 余单子的“余代数”定律
有一个漂亮的事实：上面三条透镜定律，恰好等价于说 `l : a → Store s a` 与余单子结构相容，即

- `extract (l x) = x`（就是“写你读的”），
- `duplicate (l x) = l <$> l x`（合起来就是另外两条）。

满足这两条的 `l` 叫做 Store 余单子的**余代数**（coalgebra）。我们会在 [3.9 单子的代数](/part3/09-algebras-for-monads)里系统地讨论（余）代数。对 `Point.xL`，这两条也是 `rfl`：

```lean
theorem xL_coalg_extract (p : Point) : extract (Point.xL p) = p := rfl
theorem xL_coalg_duplicate (p : Point) : duplicate (Point.xL p) = Point.xL <$> Point.xL p := rfl
```
:::

这些想法我们会在后面的章节里进一步展开。

## 挑战

1. 用 `Store` 余单子实现 Conway 的生命游戏。提示：`s` 选什么类型？

以下是补充的 Lean 练习：

2. 用 `Store Int Bool` 实现一维元胞自动机 Rule 90（新状态 = 左邻居 xor 右邻居），从“只有 0 号格子为真”出发，验证前 4 代画出谢尔宾斯基三角形的开头。
3. **Traced 余单子**（Writer 单子的对偶）：取幺半群 `(Nat, +, 0)`，定义 `structure Traced (α : Type) where run : Nat → α`，其中 `extract t = t.run 0`，`duplicate t` 的第 `m` 个元素是 `fun m' => t.run (m + m')`。为它写出 `Comonad` 与 `LawfulComonad` 实例。你注意到它和哪个余单子长得一模一样了吗？

::: details 参考答案
**1. 生命游戏**

`s` 取二维整数坐标 `Int × Int`：`Store (Int × Int) Bool` 是一张无限大的网格（`peek`），外加一个焦点格子（`pos`）。co-Kleisli 箭头只看焦点和它的八个邻居，`extend` 把它推广到整张网格：

```lean
abbrev Cell := Int × Int

def neighbors (c : Cell) : List Cell :=
  [(-1,-1), (-1,0), (-1,1), (0,-1), (0,1), (1,-1), (1,0), (1,1)].map
    fun (dx, dy) => (c.1 + dx, c.2 + dy)

/-- 局部规则：活格子有 2 或 3 个活邻居则存活；死格子恰有 3 个活邻居则复活。 -/
def lifeRule (g : Store Cell Bool) : Bool :=
  let n := (neighbors g.pos).countP g.peek
  if extract g then n == 2 || n == 3 else n == 3

def lifeStep : Store Cell Bool → Store Cell Bool := extend lifeRule

def fromCells (cs : List Cell) : Store Cell Bool := ⟨fun c => cs.contains c, (0, 0)⟩

/-- 把以原点为中心、半径 r 的方块画成字符串 -/
def render (g : Store Cell Bool) (r : Int) : List String :=
  (List.range (2 * r.toNat + 1)).map fun i =>
    String.ofList <| (List.range (2 * r.toNat + 1)).map fun j =>
      if g.peek (Int.ofNat j - r, Int.ofNat i - r) then '#' else '.'

/-- 滑翔机 -/
def glider := fromCells [(0,-1), (1,0), (-1,1), (0,1), (1,1)]

def shifted (g : Store Cell Bool) (dx dy : Int) : Store Cell Bool :=
  ⟨fun (x, y) => g.peek (x - dx, y - dy), g.pos⟩

#guard render glider 2 == [".....", "..#..", "...#.", ".###.", "....."]
-- 4 代之后，滑翔机向右下方平移了一格
#guard render (Nat.repeat lifeStep 4 glider) 3 == render (shifted glider 1 1) 3
```

`Nat.repeat f n x` 把 `f` 连续作用 `n` 次。

这个实现有一个性能陷阱：`extend` 产生的新 `peek` 是一个**闭包**，它在被询问时才去询问上一代的 `peek`；而每个格子要问 9 个格子，于是第 `k` 代的一次查询会引发约 $9^k$ 次底层查询。Haskell 有惰性但没有自动记忆化，同样会遇到这个问题。解决办法是每一代之后把有限区域内的结果**制表**（缓存到数组里）：

```lean
/-- 把半径 r 以内的格子算一遍存进数组；范围外视为死格子。 -/
def tabulate (r : Int) (g : Store Cell Bool) : Store Cell Bool :=
  let n := 2 * r.toNat + 1
  let arr := Array.ofFn (n := n * n) fun i =>
    g.peek (Int.ofNat (i.val % n) - r, Int.ofNat (i.val / n) - r)
  ⟨fun (x, y) =>
    if -r ≤ x ∧ x ≤ r ∧ -r ≤ y ∧ y ≤ r then arr[((y + r) * n + (x + r)).toNat]! else false,
   g.pos⟩

def lifeStepFast (r : Int) : Store Cell Bool → Store Cell Bool := tabulate r ∘ lifeStep

-- 20 代后，滑翔机平移了 5 格；有了制表，这一行瞬间就能算完
#guard render (Nat.repeat (lifeStepFast 12) 20 glider) 8 == render (shifted glider 5 5) 8
```

这也正是 Rust 程序员会写的“双缓冲”：一块数组读、一块数组写。余单子给出的是**规范**（局部规则 + `extend`），制表是**实现**上的优化。

**2. Rule 90**

```lean
def rule90 (w : Store Int Bool) : Bool := w.peek (w.pos - 1) != w.peek (w.pos + 1)

def seed : Store Int Bool := ⟨fun i => i == 0, 0⟩

def row (w : Store Int Bool) (r : Int) : String :=
  String.ofList <| (List.range (2 * r.toNat + 1)).map fun j =>
    if w.peek (Int.ofNat j - r) then '#' else '.'

#guard (List.range 4).map (fun k => row (Nat.repeat (extend rule90) k seed) 4) ==
  ["....#....",
   "...#.#...",
   "..#...#..",
   ".#.#.#.#."]
```

**3. Traced**

```lean
structure Traced (α : Type) where
  run : Nat → α

instance : Functor Traced where
  map f t := ⟨f ∘ t.run⟩

instance : Comonad Traced where
  extract t := t.run 0                                -- 用幺半群的单位 0 去查询
  duplicate t := ⟨fun m => ⟨fun m' => t.run (m + m')⟩⟩ -- 用幺半群的乘法 + 组合两次查询
  extend f t := ⟨fun m => f ⟨fun m' => t.run (m + m')⟩⟩

instance : LawfulComonad Traced where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
  extend_extract t := by
    show (⟨fun m => t.run (m + 0)⟩ : Traced _) = t
    simp                                               -- 右单位律 m + 0 = m
  extract_extend f t := by
    show f ⟨fun m' => t.run (0 + m')⟩ = f t
    simp                                               -- 左单位律 0 + m = m
  extend_extend f g t := by
    show (⟨fun m => g ⟨fun m' => f ⟨fun m'' => t.run (m + m' + m'')⟩⟩⟩ : Traced _)
       = ⟨fun m => g ⟨fun m' => f ⟨fun m'' => t.run (m + (m' + m''))⟩⟩⟩
    simp [Nat.add_assoc]                               -- 结合律
  extend_def _ _ := rfl
  duplicate_def _ := rfl
```

三条余单子定律恰好用到了幺半群的三条定律。而且，`Traced`（以 `(Nat, +, 0)` 为幺半群）和我们的 `Stream'` 一模一样：`run` 就是 `get`，`duplicate` 的第 `m` 条就是 `drop m`。流余单子不过是 Traced 余单子的一个特例！
:::

## 本章小结

- 余单子是单子的对偶：co-Kleisli 箭头 `w a → b` 接收“值 + 上下文”，`extract : w a → a` 是恒等箭头，`f =>= g = g ∘ extend f` 是复合。
- 余单子能“取出”值却不能“放入”值：它像一个出厂就装满、带有焦点的容器，适合描述**上下文计算**。
- 三套等价的原语：co-Kleisli 复合、`extend`、`duplicate`；`extend f = (f <$> ·) ∘ duplicate`，`duplicate = extend id`。Lean 能在编译期发现“两个都没实现”的错误。
- 积余单子 `Product e a` 和 Reader 单子做的是同一件事；我们证明了柯里化把 co-Kleisli 复合精确地变成 Reader 的 Kleisli 复合。
- 流余单子：`duplicate` 产生所有后缀，`extend` 就是数字滤波器（如移动平均）。Lean 4.34.1 的 `coinductive` 只支持谓词、不支持余归纳数据，所以我们用 `Nat → α` 表示流，并用余归纳谓词证明了“永远成立”的性质。
- 范畴论中，余单子是自函子 $T$ 加 $\varepsilon : T \to I$、$\delta : T \to T^2$，满足余结合律与余单位律；伴随 $L \dashv R$ 给出余单子 $L \circ R$，$\delta = L\circ\eta\circ R$。
- 在 (**Set**, ×, 1) 中每个对象都只有平凡的余幺半群结构（复制 + 丢弃）；余单子是自函子范畴中的余幺半群。
- Store 余单子 `(s → a) × s` 来自积–指数伴随，是 State 单子的对偶；`a → Store s a` 正是透镜（getter + setter）。`extend` 把局部规则推广到整个空间，元胞自动机和生命游戏就是它最直观的例子。
