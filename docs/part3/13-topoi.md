# 3.13 拓扑斯

我意识到，我们也许正在远离编程，一头扎进硬核数学。但你永远不知道编程的下一场大革命会带来什么，也不知道理解它需要什么样的数学。
眼下就有一些非常有意思的想法在流传：比如带有连续时间的函数式响应式编程（FRP）、用依值类型扩展 Haskell 的类型系统，
以及在编程中探索同伦类型论（homotopy type theory）。

::: tip Lean 视角：其中一场“革命”你已经身在其中
原书写于 2015 年前后，“给类型系统加上依值类型”还是一个前沿话题。而你现在用的 Lean 4 **就是**一门依值类型语言：
类型可以依赖于值（`Vector α n`、`{x : Nat // x > 0}`），命题就是类型，证明就是程序。本章讲的拓扑斯与逻辑，
恰恰是理解“为什么 Lean 里的 `Prop` 长成这个样子”的钥匙。
:::

到目前为止，我一直随意地把类型等同于值的**集合**。严格说来这并不正确，因为这种做法没有考虑到：在编程中我们是**计算**出值的，
而计算是一个耗费时间的过程，在极端情况下，它甚至可能不终止。发散的计算是每一门图灵完备语言的一部分。

::: tip Lean 深入：Lean 里的类型更像集合
Lean 是一门**全函数**语言：普通的 `def` 必须能证明终止（结构递归或良基递归），否则编译器会拒绝。
可能不终止的函数要显式标记为 `partial def`，而且这类函数不能参与证明。所以，在 Lean 的“逻辑部分”里，
把类型看成集合、把函数看成集合之间的函数，比在 Haskell 里要准确得多——这正是本书选择 Lean 的原因之一。
:::

还有一些基础层面的原因，让集合论未必是计算机科学乃至数学本身的最佳基础。一个不错的类比是：集合论就像绑定在某种特定架构上的汇编语言。
如果你想让你的数学在不同的架构上运行，就得用更一般的工具。

一种可能是用**空间**代替集合。空间带有更多结构，而且可以不借助集合来定义。人们通常把拓扑与空间联系在一起，拓扑是定义连续性之类概念所必需的。
而拓扑的传统做法嘛，你猜对了，正是通过集合论。尤其是，**子集**的概念是拓扑学的核心。
毫不意外，范畴论学者把这个想法推广到了 $\mathbf{Set}$ 以外的范畴。恰好具备合适性质、可以替代集合论的那一类范畴叫做**拓扑斯**（topos，复数 topoi），
它提供的东西之一，就是一个推广了的子集概念。

## 子对象分类子

我们先试着用函数而不是元素来表达子集的概念。从某个集合 $a$ 到 $b$ 的任意函数 $f$ 都定义了 $b$ 的一个子集——$a$ 在 $f$ 下的像。
可是有许多函数定义的是同一个子集，我们得更具体一些。首先，我们可以只关注**单射**的函数——不会把多个元素“挤”成一个的函数。
单射函数把一个集合“注入”另一个集合。对有限集合，你可以把单射函数想象成一组平行的箭头，把一个集合的元素连到另一个集合的元素上。
当然，第一个集合不能比第二个大，否则箭头必然会汇聚到一起。

::: info 数学小课堂：像、单射
- 函数 $f \colon a \to b$ 的**像**（image）是 $b$ 中“被 $f$ 打到”的那些元素：$\{f(x) \mid x \in a\}$。
  例：$f \colon \{1, 2, 3\} \to \mathbb{N}$，$f(x) = 2x$，像是 $\{2, 4, 6\}$。
- $f$ 是**单射**（injective），如果不同的输入一定给出不同的输出：$f(x) = f(y) \Rightarrow x = y$。
  例：$x \mapsto 2x$ 是单射；$x \mapsto x \bmod 2$ 不是（$1$ 和 $3$ 都被送到 $1$）。
- 单射的直观图像：从 $a$ 到 $b$ 的箭头**互不相撞**。所以有限集合之间存在单射 $a \to b$，必须 $a$ 的元素个数不超过 $b$ 的。
:::

不过仍有一点含糊之处：可能存在另一个集合 $a'$ 和另一个从它到 $b$ 的单射 $f'$，挑出的是同一个子集。
但你很容易说服自己：这样的集合必定与 $a$ 同构。我们可以利用这一事实，把子集定义为一族单射函数，它们通过各自定义域之间的同构联系在一起。
更准确地说，我们称两个单射函数

$$f \colon a \to b \qquad\qquad f' \colon a' \to b$$

是**等价**的，如果存在一个同构

$$h \colon a \to a'$$

使得：

$$f = f' \circ h$$

这样一族等价的单射就定义了 $b$ 的一个子集。

![子集作为一族等价的单射](/img/3.13/subsetinjection.jpg "两个单射 f : a → b 与 f' : a' → b 挑出 b 中同一块子集；它们通过定义域之间的同构 h : a → a' 联系起来。")

举个 Lean 里的小例子：`Bool` 到 `Nat` 有两个单射，一个把 `false ↦ 0, true ↦ 1`，另一个反过来 `false ↦ 1, true ↦ 0`。
它们挑出的是同一个子集 $\{0, 1\}$，并且相差一个同构——`Bool` 上的取反 `not`：

```lean
def f₁ : Bool → Nat := fun b => if b then 1 else 0
def f₂ : Bool → Nat := fun b => if b then 0 else 1

-- not 是 Bool 到自身的同构（它是自己的逆）
example : ∀ b : Bool, (!(!b)) = b := by decide

-- f₁ = f₂ ∘ not：两个单射相差一个定义域上的同构，所以代表同一个子集
example : f₁ = f₂ ∘ not := by
  funext b
  cases b <;> rfl
```

这个定义可以推广到任意范畴：只要把单射函数换成**单态射**（monomorphism）。提醒一下，从 $a$ 到 $b$ 的单态射 $m$ 是由它的泛性质定义的：
对任意对象 $c$ 和任意一对态射

$$g \colon c \to a \qquad\qquad g' \colon c \to a$$

只要满足

$$m \circ g = m \circ g'$$

就必然有 $g = g'$。

![单态射](/img/3.13/monomorphism.jpg "单态射 m : a → b：任意两个从 c 出发的态射 g、g'，只要后接 m 之后相同，它们本身就相同。")

```diagram
C: (0, 0) "c"
A: (2, 0) "a"
B: (4, 0) "b"
g: C -> A "g" bend=22
g2: C -> A "g'" bend=-22 side=right
m: A -> B "m"
path "m ∘ g": g m
path "m ∘ g'": g2 m color=green
caption: 单态射：如果两条路线 m∘g 与 m∘g' 相同，那么 g = g'。m 是“可以从左边消去”的。
```

在集合上，如果我们想想“函数 $m$ **不是**单态射”意味着什么，这个定义就更好理解了。那意味着它会把 $a$ 中两个不同的元素映到 $b$ 中同一个元素。
于是我们可以找到两个函数 $g$ 和 $g'$，它们只在那两个元素上不同；而后接 $m$ 会把这个差别掩盖掉。

![不是单态射的函数](/img/3.13/notmono.jpg "m 把 a 中的 x 与 y 送到 b 中同一点。g 把 z 送到 x，g' 把 z 送到 y：g ≠ g'，可是 m ∘ g = m ∘ g'。")

在 Lean 里，我们把单态射写成一个命题，然后证明它和单射是一回事（在类型的范畴里）：

```lean
/-- m 是单态射：可以从左边消去 -/
def Mono {a b : Type} (m : a → b) : Prop :=
  ∀ {c : Type} (g g' : c → a), m ∘ g = m ∘ g' → g = g'

def Injective {a b : Type} (f : a → b) : Prop :=
  ∀ x y, f x = f y → x = y

/-- 单射 ⟹ 单态射 -/
theorem mono_of_injective {a b : Type} {m : a → b} (hm : Injective m) : Mono m := by
  intro c g g' h
  funext z
  -- 在每个 z 上，m (g z) = m (g' z)，用单射性去掉 m
  exact hm _ _ (congrFun h z)

/-- 单态射 ⟹ 单射：取 c = Unit，用两个常函数“探测”a 中的两个元素 -/
theorem injective_of_mono {a b : Type} {m : a → b} (hm : Mono m) : Injective m := by
  intro x y h
  have := hm (c := Unit) (fun _ => x) (fun _ => y) (funext fun _ => h)
  exact congrFun this ()
```

::: tip Lean 深入：`congrFun` 与具名参数
- `congrFun : f = g → ∀ x, f x = g x`：两个函数相等，那么它们在每个点上的值相等。`funext` 是它的反方向。
- `hm (c := Unit) …`：用**具名参数**语法显式指定隐式参数 `c` 的值。这里我们要“用单元素类型去探测”，所以把 `c` 指定为 `Unit`。
  这个技巧——用从单元素集合出发的函数来代表“元素”——本章还会反复出现。
:::

定义子集还有另一种方式：用一个叫做**特征函数**（characteristic function）的函数。它是从集合 $b$ 到一个二元素集合 $\Omega$ 的函数 $\chi$。
这个集合中的一个元素被指定为“真”，另一个为“假”。这个函数给 $b$ 中属于子集的元素赋值“真”，给不属于的赋值“假”。

还剩一件事要说明：把 $\Omega$ 中的一个元素“指定为真”是什么意思。我们可以用那个标准技巧：用一个从单元素集合到 $\Omega$ 的函数。我们称这个函数为 $\mathit{true}$：

$$\mathit{true} \colon 1 \to \Omega$$

![true 箭头](/img/3.13/true.jpg "true : 1 → Ω 把单元素集合的唯一元素送到 Ω 中被指定为“真”的那个元素。")

在 Lean 里，$\Omega$ 先取 `Bool`，单元素集合是 `Unit`：

```lean
def trueB : Unit → Bool := fun () => true

/-- 偶数子集的特征函数 -/
def χEven : Nat → Bool := fun n => n % 2 == 0

#guard χEven 4 == true
#guard χEven 7 == false
```

::: tip Rust 视角
你天天都在用特征函数：`Iterator::filter` 接受的那个闭包 `impl Fn(&T) -> bool`，就是一个特征函数 $\chi \colon T \to \Omega$；
`filter` 返回的东西就是它所定义的子集。

```rust
/// 用特征函数 chi 从集合 b 中“切出”子集
fn subset<T: Clone>(b: &[T], chi: impl Fn(&T) -> bool) -> Vec<T> {
    b.iter().filter(|x| chi(x)).cloned().collect()
}

pub fn demo() -> Vec<u32> {
    subset(&[0, 1, 2, 3, 4, 5, 6, 7], |n| n % 2 == 0) // [0, 2, 4, 6]
}
```
:::

这些定义可以结合起来，不仅定义什么是子对象，还能不谈元素地定义那个特殊对象 $\Omega$。思路是：我们想让态射 $\mathit{true}$ 代表一个“泛型”子对象。
在 $\mathbf{Set}$ 中，它从二元素集合 $\Omega$ 中挑出一个单元素子集。这已经泛得不能再泛了。它显然是一个真子集，因为 $\Omega$ 还有一个元素**不**在这个子集里。

在更一般的情形下，我们把 $\mathit{true}$ 定义为从终对象到**分类对象** $\Omega$（classifying object）的一个单态射。
**子对象分类子**（subobject classifier）由 $\Omega$ 和 $\mathit{true}$ 共同组成。但我们还得定义这个分类对象。我们需要一个把它和特征函数联系起来的泛性质。
事实证明，在 $\mathbf{Set}$ 中，$\mathit{true}$ 沿特征函数 $\chi$ 的**拉回**，既定义了子集 $a$，也定义了把它嵌入 $b$ 的单射函数。下面是这个拉回图：

![拉回图](/img/3.13/pullback.jpg "子对象分类子的拉回图：a 经 unit 到 1、经 f 到 b；1 经 true 到 Ω，b 经 χ 到 Ω。")

```diagram
A: (0, 0) "a"
One: (2.2, 0) "1"
B: (0, 1.8) "b"
Om: (2.2, 1.8) "\Omega"
unit: A -> One "\mathit{unit}"
tru: One -> Om "\mathit{true}"
f: A -> B "f" side=right
chi: B -> Om "\chi" side=right
path "true ∘ unit": unit tru
path "χ ∘ f": f chi color=green
caption: 拉回方块：两条从 a 到 Ω 的路线相等。点击按钮看看——两条路都把 a 的每个元素送到“真”。
```

我们来分析这个图。拉回的方程是：

$$\mathit{true} \circ \mathit{unit} = \chi \circ f$$

函数 $\mathit{true} \circ \mathit{unit}$ 把 $a$ 的每个元素都映到“真”。所以 $f$ 必须把 $a$ 的所有元素映到 $b$ 中那些使 $\chi$ 为“真”的元素上。
按定义，这些正是特征函数 $\chi$ 所指定的子集中的元素。所以 $f$ 的像确实就是我们说的那个子集。拉回的泛性质则保证了 $f$ 是单射。

::: info 数学小课堂：拉回
给定两个箭头 $\chi \colon b \to \Omega$ 和 $\mathit{true} \colon 1 \to \Omega$，它们指向同一个对象。它们的**拉回**（pullback）是一个对象 $a$ 加上两个箭头
$f \colon a \to b$、$\mathit{unit} \colon a \to 1$，使方块交换；并且它是“最好的”这样的方块：任何别的交换方块 $(c, h, \ldots)$ 都**唯一地**经过它。

在集合中，拉回有一个非常具体的公式：$\{(x, y) \in b \times 1 \mid \chi(x) = \mathit{true}(y)\}$。因为 $1$ 只有一个元素，这就是
$\{x \in b \mid \chi(x) = \text{真}\}$——恰好是 $\chi$ 定义的子集。
:::

下面这个组件让你亲手搭一个子集。点选元素，左边是子集，中间是特征函数的表格，右边是拉回图里每一个元素的去向：

<div>
<Ch3_13SubsetChi />
</div>

### 在 Lean 中：子类型就是拉回

Lean 有一个专门的语法表示“满足某个性质的元素”：**子类型**（subtype）`{x : b // p x}`。它的元素是一对东西：一个 `x : b`，外加一个 `p x` 的证明。
`Subtype.val` 把证明丢掉，只取出 `x`——这正是那个嵌入 $f \colon a \hookrightarrow b$。

我们把“$f$ 是 $\mathit{true}$ 沿 $\chi$ 的拉回”写成一个结构体，并对任意的 $\Omega$ 和 $\mathit{true}$ 都适用（等会儿我们会用 `Bool` 和 `Prop` 两种 $\Omega$）：

```lean
/-- 拉回方块（终对象是 Unit，所以 unit 是唯一的那个函数 fun _ => ()）：
    f : a → b 是 tru : Unit → Ω 沿 χ : b → Ω 的拉回 -/
structure IsPullbackOfTrue {Ω : Type} (tru : Unit → Ω) {a b : Type} (χ : b → Ω) (f : a → b) : Prop where
  /-- 方块交换：χ ∘ f = true ∘ unit -/
  comm : χ ∘ f = tru ∘ (fun _ => ())
  /-- 泛性质：任何别的交换方块 (c, h) 都唯一地经过 a -/
  univ : ∀ {c : Type} (h : c → b), χ ∘ h = tru ∘ (fun _ => ()) →
    ∃ u : c → a, f ∘ u = h ∧ ∀ u' : c → a, f ∘ u' = h → u' = u

/-- 子类型 {x // χ x = true} 连同 Subtype.val，就是 trueB 沿 χ 的拉回 -/
theorem subtype_isPullback {b : Type} (χ : b → Bool) :
    IsPullbackOfTrue trueB χ (Subtype.val : {x // χ x = true} → b) where
  comm := by
    funext ⟨x, hx⟩      -- 子类型的元素是一对：值 x 和证明 hx : χ x = true
    exact hx
  univ := by
    intro c h hh
    -- 存在性：每个 h z 都满足 χ (h z) = true，于是可以“装进”子类型
    refine ⟨fun z => ⟨h z, congrFun hh z⟩, rfl, ?_⟩
    -- 唯一性：两个子类型元素只要值相同就相等（证明是无关紧要的）
    intro u' hu'
    funext z
    apply Subtype.ext
    exact congrFun hu' z

/-- 例：偶数子集 -/
abbrev EvenNat := {n : Nat // χEven n = true}
def four : EvenNat := ⟨4, rfl⟩
example : four.val = 4 := rfl
```

::: tip Lean 深入：`Subtype.ext` 与证明无关性
`Subtype.ext : a₁.val = a₂.val → a₁ = a₂`。为什么只比较值就够了？因为 Lean 的 `Prop` 具有**证明无关性**（proof irrelevance）：
同一个命题的任意两个证明在定义上相等。所以子类型的元素完全由它的值决定——这正是“$f$ 是单射”的根源，也是本章挑战题的关键。
:::

这个拉回图可以用来在 $\mathbf{Set}$ 以外的范畴中定义分类对象。这样的范畴必须有终对象，好让我们定义单态射 $\mathit{true}$。
它还必须有拉回——实际的要求是它必须有所有有限极限（拉回是有限极限的一个例子）。在这些假设下，我们这样定义分类对象 $\Omega$：
对**每一个**单态射 $f$，都存在**唯一**的态射 $\chi$ 补全这个拉回图。

我们来分析最后这句话。构造拉回时，我们拿到的是三个对象 $\Omega$、$b$ 和 $1$，以及两个态射 $\mathit{true}$ 和 $\chi$。
拉回存在，意味着我们能找到最好的那个对象 $a$，配上两个态射 $f$ 和 $\mathit{unit}$（后者由终对象的定义唯一确定），使图交换。

而这里我们解的是另一组方程。我们要求解的是 $\Omega$ 和 $\mathit{true}$，同时让 $a$ **和** $b$ 都变化。对给定的 $a$ 和 $b$，单态射 $f \colon a \to b$ 可能有也可能没有。
但只要有，我们就希望它是某个 $\chi$ 的拉回。不仅如此，我们还希望这个 $\chi$ 由 $f$ 唯一确定。

我们不能说单态射 $f$ 和特征函数 $\chi$ 之间是一一对应的，因为拉回只在同构意义下唯一。但回想一下我们早先把子集定义为一族等价的单射。
我们可以推广它：把 $b$ 的**子对象**定义为一族到 $b$ 的等价单态射。这族单态射与我们图中的一族等价拉回一一对应。

于是我们可以把 $b$ 的子对象的集合 $\mathit{Sub}(b)$ 定义为一族一族的单态射，并且看到它同构于从 $b$ 到 $\Omega$ 的态射的集合：

$$\mathit{Sub}(b) \cong \mathcal{C}(b, \Omega)$$

这恰好是两个函子之间的自然同构。换句话说，$\mathit{Sub}(-)$ 是一个可表的（逆变）函子，它的表示对象就是 $\Omega$。

::: info 数学小课堂：数一数
取 $b = \{0, 1, \ldots, 7\}$。它有多少个子集？每个元素“在”或“不在”，共 $2^8 = 256$ 个。从 $b$ 到 $\Omega = \{\text{真}, \text{假}\}$ 的函数有多少个？
每个元素有 2 种取值，也是 $2^8 = 256$ 个。$\mathit{Sub}(b) \cong \mathcal{C}(b, \Omega)$ 在有限集合上就是这个计数等式“背后的原因”。
上面组件底部显示的二进制串，就是把特征函数的表格横过来读。
:::

为什么说它“逆变”且“自然”？给一个函数 $g \colon c \to b$，$b$ 的子集可以沿 $g$ **拉回**成 $c$ 的子集（取原像 $g^{-1}$）；
而在特征函数那一边，这只是**预复合** $\chi \mapsto \chi \circ g$。拉回把箭头方向倒了过来，所以是逆变的；而“先拉回再取特征函数”与“先取特征函数再预复合”结果一样，这就是自然性。
在 Lean 里，预复合的函子定律只是 `rfl`：

```lean
/-- Sub(-) 在态射上的作用：沿 g 拉回 = 预复合 -/
def pullbackAlong {c b : Type} (g : c → b) (χ : b → Bool) : c → Bool := χ ∘ g

-- 逆变函子的两条定律
example {b : Type} (χ : b → Bool) : pullbackAlong id χ = χ := rfl
example {d c b : Type} (k : d → c) (g : c → b) (χ : b → Bool) :
    pullbackAlong (g ∘ k) χ = pullbackAlong k (pullbackAlong g χ) := rfl

-- 例：偶数子集沿 n ↦ n + 1 拉回，得到奇数子集
example : pullbackAlong (· + 1) χEven 3 = true := rfl
example : pullbackAlong (· + 1) χEven 4 = false := rfl
```

### `Prop`：Lean 自带的子对象分类子

到这里你可能已经注意到，Lean 里用来分类子类型的，并不是 `Bool`，而是 `Prop`。子类型 `{x : α // p x}` 由一个**谓词** `p : α → Prop` 决定。
这和子对象分类子的图景完全吻合：

| 拓扑斯 | Lean |
|---|---|
| 分类对象 $\Omega$ | `Prop` |
| $\mathit{true} \colon 1 \to \Omega$ | `fun () => True` |
| 特征函数 $\chi \colon b \to \Omega$ | 谓词 `p : b → Prop` |
| 子对象 $f \colon a \hookrightarrow b$ | 子类型 `{x : b // p x}` 与 `Subtype.val` |
| $\mathit{Sub}(b) \cong \mathcal{C}(b, \Omega)$ | 子集**就是**谓词：`Set b := b → Prop` |

最后一行在 Mathlib 里是字面意义上的定义：`def Set (α : Type u) := α → Prop`。Lean 核心库没有 `Set`，我们自己写一个：

```lean
/-- 集合就是谓词，也就是到 Prop 的特征函数 -/
def Set (α : Type) : Type := α → Prop

instance {α : Type} : Membership α (Set α) := ⟨fun s x => s x⟩

def evens : Set Nat := fun n => n % 2 = 0

example : 4 ∈ evens := rfl          -- 4 ∈ evens 展开就是 4 % 2 = 0，计算即得
example : ¬ (3 ∈ evens) := by
  intro h
  -- h : 3 ∈ evens，展开就是 3 % 2 = 0；而 3 % 2 算出来是 1，矛盾
  have h' : 3 % 2 = 0 := h
  omega
```

用 `Prop` 作 $\Omega$，拉回方块同样成立。只是“方块交换”要求 $\chi \circ f$ 与 $\mathit{true} \circ \mathit{unit}$ 作为**函数**相等，也就是对每个 $x$ 都有 `p x = True`
——这是**命题之间的等式**。从“我有 `p x` 的证明”到“`p x = True`”，需要 Lean 的**命题外延性**公理 `propext`（`eq_true` 就是用它证明的）：

```lean
theorem subtype_isPullback_Prop {b : Type} (p : b → Prop) :
    IsPullbackOfTrue (fun () => True) p (Subtype.val : {x // p x} → b) where
  comm := by
    funext ⟨x, hx⟩
    exact eq_true hx              -- hx : p x  ⟹  p x = True（用到 propext）
  univ := by
    intro c h hh
    -- hh z : p (h z) = True，用 of_eq_true 取回 p (h z) 的证明
    refine ⟨fun z => ⟨h z, of_eq_true (congrFun hh z)⟩, rfl, ?_⟩
    intro u' hu'
    funext z
    apply Subtype.ext
    exact congrFun hu' z

/-- 从谓词出发，取子类型，再取它的像，又回到原来的谓词：Sub(b) → (b → Ω) 的一半 -/
theorem image_of_subtype {b : Type} (p : b → Prop) :
    (fun y => ∃ x : {x // p x}, x.val = y) = p := by
  funext y
  apply propext
  constructor
  · intro ⟨⟨x, hx⟩, hxy⟩
    exact hxy ▸ hx               -- x = y，把 p x 改写成 p y
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩
```

::: tip Lean 深入：`propext` 与 `▸`
- `propext : (a ↔ b) → a = b` 是 Lean 的公理之一：**逻辑等价的命题相等**。它让 `Prop` 真正表现得像“真值的对象”：
  一个命题只关心它真不真，而不关心它“长什么样”。
- `h ▸ e`：用等式 `h` 改写 `e` 的类型。这里 `hxy : x = y`，`hx : p x`，`hxy ▸ hx : p y`。
:::

## 拓扑斯

拓扑斯是满足以下条件的范畴：

1. 它是笛卡尔闭的：有所有的积、终对象，以及指数对象（定义为积的右伴随）；
2. 对所有有限图都有极限；
3. 有一个子对象分类子 $\Omega$。

这组性质让拓扑斯在大多数应用中都能顶替 $\mathbf{Set}$。它还有一些由定义推出的额外性质。例如，拓扑斯有所有有限余极限，包括始对象。

把子对象分类子定义成两个终对象的余积（和）会很诱人——在 $\mathbf{Set}$ 里它就是这样——但我们想比这更一般。满足这一点的拓扑斯叫做**布尔**拓扑斯（Boolean topos）。

::: tip Lean 深入：Lean 的 `Type` 很像一个拓扑斯
逐条对照（这里只作直观对照，不是严格的形式化）：

- **笛卡尔闭**：积 `α × β`，终对象 `Unit`，指数对象 `α → β`。第 1.9 章已经验证过柯里化就是伴随。
- **有限极限**：有积和等化子就有所有有限极限。等化子与拉回都可以用子类型写出：
  `{p : α × β // f p.1 = g p.2}` 就是 `f : α → γ` 与 `g : β → γ` 的拉回。
- **子对象分类子**：`Prop` 与 `fun () => True`，如上一节所示（需要 `propext`）。
- **有限余极限**：始对象 `Empty`，余积 `α ⊕ β`，余等化子可以用商类型 `Quot` 构造。

**布尔**这一条则微妙得多。两个终对象的余积 `Unit ⊕ Unit` 本质上就是 `Bool`。说 `Prop` 是布尔的，就是说 `Prop ≅ Bool`，
即“每个命题要么是 `True` 要么是 `False`”。这在 Lean 里**只有**借助经典公理才能证明（`Classical.propComplete`），下一节解释为什么。
:::

```lean
/-- 拉回的具体构造：f : α → γ 与 g : β → γ 的拉回 -/
def Pullback {α β γ : Type} (f : α → γ) (g : β → γ) : Type := {p : α × β // f p.1 = g p.2}

/-- 两个终对象的余积就是 Bool -/
def toU : Bool → Unit ⊕ Unit
  | true => .inl ()
  | false => .inr ()
def ofU : Unit ⊕ Unit → Bool
  | .inl () => true
  | .inr () => false

example : ∀ b, ofU (toU b) = b := by decide
example (s : Unit ⊕ Unit) : toU (ofU s) = s := by cases s <;> rfl

-- “Prop 是布尔的”：每个命题等于 True 或 False——经典公理
#check (Classical.propComplete : ∀ p : Prop, p = True ∨ p = False)
```

## 拓扑斯与逻辑

在集合论中，特征函数可以解释为在定义集合元素的一个性质——一个**谓词**（predicate），对某些元素为真，对另一些为假。
谓词 $\mathit{isEven}$ 从自然数集合中选出偶数构成的子集。在拓扑斯中，我们可以把谓词的概念推广为从对象 $a$ 到 $\Omega$ 的态射。
这就是为什么 $\Omega$ 有时被称为**真值对象**（truth object）。

```lean
def isEven (n : Nat) : Prop := n % 2 = 0

-- 谓词 isEven : Nat → Prop 选出的子类型
abbrev Evens := {n : Nat // isEven n}
def six : Evens := ⟨6, rfl⟩
```

谓词是逻辑的积木。拓扑斯包含研究逻辑所需的全部工具。它有积，对应逻辑合取（逻辑**与**）；有余积，对应析取（逻辑**或**）；有指数对象，对应蕴含。
除了排中律（或者等价地，双重否定消去），所有标准的逻辑公理在拓扑斯中都成立。这就是为什么拓扑斯的逻辑对应于构造性逻辑，或者说直觉主义逻辑。

在 Lean 里，这个对应是**字面意义上的**（这就是 Curry–Howard 对应）：

| 逻辑 | 范畴 | Lean 的 `Prop` | Lean 的 `Type` |
|---|---|---|---|
| $p \wedge q$ | 积 | `p ∧ q`（结构体 `And`，两个字段） | `α × β` |
| $p \vee q$ | 余积 | `p ∨ q`（归纳类型 `Or`，两个构造子） | `α ⊕ β` |
| $p \Rightarrow q$ | 指数对象 | `p → q` | `α → β` |
| 真 | 终对象 | `True` | `Unit` |
| 假 | 始对象 | `False` | `Empty` |
| $\neg p$ | $p \Rightarrow \bot$ | `¬p` 即 `p → False` | `α → Empty` |

“指数对象是积的右伴随”（柯里化）在逻辑里变成了一条推理规则：

```lean
section Logic
variable (p q r : Prop)

/-- 柯里化 = “积 ⊣ 指数”的伴随，在 Prop 里就是这条等价 -/
theorem and_imp_iff : (p ∧ q → r) ↔ (p → q → r) :=
  ⟨fun h hp hq => h ⟨hp, hq⟩, fun h ⟨hp, hq⟩ => h hp hq⟩

/-- 余积的泛性质 = 分情况讨论 -/
theorem or_imp_iff : (p ∨ q → r) ↔ (p → r) ∧ (q → r) :=
  ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
   fun ⟨hpr, hqr⟩ h => h.elim hpr hqr⟩

end Logic
```

直觉主义逻辑一直在稳步扩张它的地盘，而且意外地得到了计算机科学的支持。经典的排中律概念基于这样一种信念：存在绝对的真理。
任何陈述要么为真，要么为假，或者像古罗马人说的那样，*tertium non datur*（没有第三种可能）。
但我们能知道某事为真或为假的唯一途径，是我们能证明它或者否证它。证明是一个过程，一种计算——而我们知道，计算耗费时间和资源。
在某些情况下，它们可能永远不会终止。如果我们无法在有限时间内证明一个陈述，声称它为真就没有意义。
拓扑斯以及它那更细腻的真值对象，为建模有趣的逻辑提供了一个更一般的框架。

### 补充：在 Lean 里亲眼看见直觉主义逻辑

Lean 的核心逻辑是**构造性**的：证明就是程序，`p ∨ q` 的证明必须真的告诉你“是左边还是右边”。
很多我们熟悉的定律可以构造性地证明，下面这些都没有用任何公理：

```lean
section Constructive
variable (p q : Prop)

/-- 双重否定引入：p → ¬¬p -/
theorem dn_intro : p → ¬¬p := fun hp hnp => hnp hp

/-- 三重否定可以化简为一重 -/
theorem tn_elim : ¬¬¬p → ¬p := fun h hp => h (dn_intro p hp)

/-- 德摩根律的一半：¬(p ∨ q) ↔ ¬p ∧ ¬q -/
theorem not_or_iff : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
   fun ⟨hnp, hnq⟩ h => h.elim hnp hnq⟩

/-- 一个漂亮的事实：排中律虽然不能构造性地证明，但它“不可能是错的” -/
theorem nn_em : ¬¬(p ∨ ¬p) :=
  fun h => h (Or.inr (fun hp => h (Or.inl hp)))

end Constructive
```

`nn_em` 的证明值得慢慢读：假设有人声称 $\neg(p \vee \neg p)$（拿着一个函数 `h`，喂给它 `p ∨ ¬p` 的证明它就产出矛盾）。
我们先“赌” $\neg p$：要给出 $\neg p$，就是要在拿到 $p$ 的证明 `hp` 时导出矛盾——那好办，把 `Or.inl hp` 喂给 `h` 就行。于是 `Or.inr (…)` 喂给 `h`，矛盾。

而下面这些在经典逻辑里成立的命题，在直觉主义逻辑里**不可证**。Lean 允许你用经典公理 `Classical.em` 证明它们：

```lean
section ClassicalOnly
variable (p q : Prop)

theorem em' : p ∨ ¬p := Classical.em p

theorem dne : ¬¬p → p := fun h => Classical.byContradiction h

/-- 德摩根律的另一半 -/
theorem not_and_to_or : ¬(p ∧ q) → ¬p ∨ ¬q := fun h =>
  (Classical.em p).elim
    (fun hp => Or.inr (fun hq => h ⟨hp, hq⟩))
    (fun hnp => Or.inl hnp)

/-- Peirce 定律 -/
theorem peirce : ((p → q) → p) → p := fun h =>
  (Classical.em p).elim id (fun hnp => h (fun hp => absurd hp hnp))

end ClassicalOnly
```

Lean 能告诉你一个定理到底依赖了哪些公理。`#print axioms` 是检验“这个证明是不是构造性的”的照妖镜：

```lean
#print axioms nn_em          -- 'nn_em' does not depend on any axioms
#print axioms not_or_iff     -- 'not_or_iff' does not depend on any axioms
#print axioms em'            -- 'em'' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms peirce         -- 依赖 Classical.choice 等
```

原书说“排中律（或者等价地，双重否定消去）”。这个“等价”我们可以用**构造性**的证明来确认——注意下面两个定理都不依赖任何公理，
它们只是说“如果你接受其中一个，就能推出另一个”：

```lean
theorem dne_of_em (em : ∀ p : Prop, p ∨ ¬p) : ∀ p : Prop, ¬¬p → p := by
  intro p hnn
  cases em p with
  | inl hp => exact hp                 -- p 成立，直接用
  | inr hnp => exact absurd hnp hnn    -- ¬p 与 ¬¬p 矛盾

theorem em_of_dne (dne : ∀ p : Prop, ¬¬p → p) : ∀ p : Prop, p ∨ ¬p :=
  fun p => dne _ (nn_em p)             -- 排中律“不可能错”，再消去双重否定

#print axioms dne_of_em      -- does not depend on any axioms
#print axioms em_of_dne      -- does not depend on any axioms
```

::: info 数学小课堂：为什么排中律“证不出来”？一个会随时间变化的世界
“Lean 证不出来”和“它是假的”是两回事。要说明排中律**不可证**，需要找一个模型：所有构造性的推理规则都成立，但排中律不成立。
拓扑斯恰好提供了这样的模型。

想象一个“随时间演化的集合”构成的拓扑斯：对象是每天都可能长出新元素的集合。在这里，一个命题的真值不再只是“真/假”，
而是“**从第几天起**为真”（或者“永远不为真”）。所以 $\Omega$ 有无穷多个元素：$\{\text{第 0 天起}, \text{第 1 天起}, \ldots, \text{永不}\}$。

考虑命题 $p$ = “从明天起成立”。今天，$p$ 不成立；可 $\neg p$（“$p$ 永远不会成立”）今天也不成立——因为明天它就成立了。
于是今天 $p \vee \neg p$ 不成立。排中律在这个世界里失效了，而 $\neg\neg(p \vee \neg p)$ 依旧成立（它说的是“不可能永远不成立”）。

这也正是原书那段话的直觉：在这里，“真”是要靠时间去**确立**的。
:::

### 补充：`Decidable`——把 `Prop` 拉回到 `Bool`

`Bool` 是布尔的：它只有两个值，排中律对它总成立，所有真值表都可以穷举验证：

```lean
example : ∀ a b : Bool, (a && b) = (b && a) := by decide
example : ∀ a : Bool, (a || !a) = true := by decide            -- Bool 的“排中律”
example : ∀ a : Bool, (!!a) = a := by decide                    -- Bool 的“双重否定消去”
example : ∀ a b : Bool, (!(a && b)) = (!a || !b) := by decide   -- 德摩根律（两半都成立）
```

那么 `Prop` 和 `Bool` 是什么关系？Lean 的类型类 `Decidable p` 说的是：“命题 `p` 的真假可以被**计算**出来”。
有了它，函数 `decide : Prop → Bool` 就能把 `p` 变成一个布尔值，而且 `decide p = true ↔ p`。
换句话说，对**可判定**的谓词，`Prop` 版的子对象分类子可以被拉回到 `Bool` 版的上面：

```lean
instance : DecidablePred isEven := fun n => inferInstanceAs (Decidable (n % 2 = 0))

#guard decide (isEven 10)
example : decide (isEven 7) = false := rfl

/-- 可判定的谓词，它的 Bool 特征函数与 Prop 特征函数分类同一个子集 -/
theorem decide_classifies {b : Type} (p : b → Prop) [DecidablePred p] (x : b) :
    decide (p x) = true ↔ p x :=
  decide_eq_true_iff

/-- 对可判定的命题，排中律是构造性可证的——不需要任何公理 -/
theorem em_of_decidable (p : Prop) [d : Decidable p] : p ∨ ¬p :=
  match d with
  | .isTrue h => Or.inl h
  | .isFalse h => Or.inr h

#print axioms em_of_decidable   -- does not depend on any axioms
```

所以“直觉主义”并不意味着“排中律总不成立”，而是：**只有在你能判定 $p$ 的时候**，你才有 $p \vee \neg p$。
`Nat` 上的等式、有限范围内的量词都可判定；但像“`∀ f : Nat → Nat, …`”这样的命题，一般就没有 `Decidable` 实例了。

::: tip Rust 视角
Rust 的 `bool` 就是布尔拓扑斯里的 $\Omega$，而每一个 `fn(&T) -> bool` 都是一个**可判定**的谓词：你写得出这个函数，就说明你能算出答案。
Lean 的 `Prop` 则大得多：它可以表达“这个函数对所有输入都终止”这种你根本写不出 `-> bool` 实现的性质。
`Decidable` 就是那座桥：只有带着一个“算法”（实例），命题才能被送回 `Bool` 的世界。
:::

::: warning 易错点：`Classical` 让一切都“可判定”，但不可计算
`open Classical` 之后，Lean 会认为每个命题都有 `Decidable` 实例（`Classical.propDecidable`）。这让证明更方便，
但这些实例是**不可计算**的（`noncomputable`）：你不能 `#eval` 它们。这正是“经典真理”与“可计算的真理”之间的那道缝。
:::

## 挑战

1. 证明：作为 $\mathit{true}$ 沿特征函数的拉回的那个函数 $f$，必然是单射。

::: details 参考答案
关键在于拉回泛性质中的**唯一性**。设 $g, g' \colon c \to a$ 满足 $f \circ g = f \circ g'$。令 $h = f \circ g$，它也满足 $\chi \circ h = \mathit{true} \circ \mathit{unit}$
（因为 $\chi \circ f$ 已经等于它了）。于是 $(c, h)$ 是另一个交换方块，按泛性质，存在**唯一**的 $u \colon c \to a$ 使 $f \circ u = h$。
而 $g$ 和 $g'$ 都满足这个条件，所以 $g = u = g'$。这说明 $f$ 是单态射；再用前面的 `injective_of_mono`，它就是单射。

这个证明完全没有用到集合的元素（只用了泛性质），所以它在任何范畴里都成立：**任何单态射沿任何态射的拉回仍是单态射**的一个特例。

```lean
/-- 拉回 true 得到的 f 是单态射——只用泛性质 -/
theorem pullback_mono {Ω : Type} {tru : Unit → Ω} {a b : Type} {χ : b → Ω} {f : a → b}
    (P : IsPullbackOfTrue tru χ f) : Mono f := by
  intro c g g' hg
  -- h := f ∘ g 也构成一个交换方块
  have hcomm : χ ∘ (f ∘ g) = tru ∘ (fun _ => ()) := by
    funext z
    exact congrFun P.comm (g z)
  -- 由泛性质得到唯一的 u
  obtain ⟨u, _, huniq⟩ := P.univ (f ∘ g) hcomm
  -- g 和 g' 都满足 f ∘ _ = f ∘ g，所以都等于 u
  have e₁ : g = u := huniq g rfl
  have e₂ : g' = u := huniq g' hg.symm
  rw [e₁, e₂]

theorem pullback_injective {Ω : Type} {tru : Unit → Ω} {a b : Type} {χ : b → Ω} {f : a → b}
    (P : IsPullbackOfTrue tru χ f) : Injective f :=
  injective_of_mono (pullback_mono P)

-- 用在我们的两个例子上
example {b : Type} (χ : b → Bool) : Injective (Subtype.val : {x // χ x = true} → b) :=
  pullback_injective (subtype_isPullback χ)
example {b : Type} (p : b → Prop) : Injective (Subtype.val : {x // p x} → b) :=
  pullback_injective (subtype_isPullback_Prop p)
```

`obtain ⟨u, _, huniq⟩ := …` 把存在量词与合取一次拆开：`u` 是那个唯一的分解，`_` 丢掉“$f \circ u = h$”，`huniq` 是唯一性。
:::

下面是为本书补充的练习：

2. 证明 $\mathbf{Set}$ 中 $\mathit{true} \colon 1 \to \Omega$ 是单态射（在 Lean 里：`trueB` 是 `Mono`）。为什么从终对象出发的**任何**态射都是单态射？
3. 证明子集的交对应特征函数的“与”：$\{x \mid \chi_1(x) \wedge \chi_2(x)\}$ 的特征函数是 `fun x => χ₁ x && χ₂ x`。并说明“子集的并”对应什么。
4. 构造性地证明：$(p \to q) \to (\neg q \to \neg p)$（逆否命题的一个方向）。再思考：反方向 $(\neg q \to \neg p) \to (p \to q)$ 能构造性地证明吗？

::: details 参考答案
```lean
-- 2. 任何从 Unit 出发的函数都是单态射：c → Unit 的函数只有一个
theorem trueB_mono : Mono trueB := by
  intro c g g' _
  funext z
  rfl                     -- g z 与 g' z 都是 ()，Unit 只有一个元素

-- 3. 交 ↔ 与；并 ↔ 或
def inter {b : Type} (χ₁ χ₂ : b → Bool) : b → Bool := fun x => χ₁ x && χ₂ x
def union {b : Type} (χ₁ χ₂ : b → Bool) : b → Bool := fun x => χ₁ x || χ₂ x

theorem inter_spec {b : Type} (χ₁ χ₂ : b → Bool) (x : b) :
    inter χ₁ χ₂ x = true ↔ χ₁ x = true ∧ χ₂ x = true := by
  simp [inter]

theorem union_spec {b : Type} (χ₁ χ₂ : b → Bool) (x : b) :
    union χ₁ χ₂ x = true ↔ χ₁ x = true ∨ χ₂ x = true := by
  simp [union]

-- 4. 逆否命题：构造性可证
theorem contrapositive (p q : Prop) : (p → q) → (¬q → ¬p) :=
  fun hpq hnq hp => hnq (hpq hp)

-- 反方向需要经典逻辑
theorem contrapositive_rev (p q : Prop) : (¬q → ¬p) → (p → q) :=
  fun h hp => Classical.byContradiction (fun hnq => h hnq hp)
```

第 2 题：$c \to 1$ 的态射只有一个（终对象的定义），所以任意 $g, g' \colon c \to 1$ 本来就相等，单态射的条件自动满足。

第 4 题的反方向不能构造性地证明：在“随时间演化的世界”里取 $q$ = “从明天起成立”、$p$ = $\neg\neg q$，可以构造反例。
它在 Lean 中需要 `Classical.byContradiction`——事实上，它对所有 $p, q$ 成立就等价于双重否定消去（取 $p = \neg\neg q$ 试试看）。
:::

## 本章小结

- 拓扑斯是一类“可以代替集合论”的范畴，它的核心是推广了的**子集**概念——**子对象**。
- 在 $\mathbf{Set}$ 中，子集有两种描述：一族等价的**单射**（在一般范畴中换成**单态射**），或一个**特征函数** $\chi \colon b \to \Omega$。
- **子对象分类子** $(\Omega, \mathit{true} \colon 1 \to \Omega)$ 由一个拉回的泛性质定义：每个单态射 $f \colon a \to b$ 都是 $\mathit{true}$ 沿唯一的 $\chi$ 的拉回。
- $\mathit{Sub}(b) \cong \mathcal{C}(b, \Omega)$ 是自然同构：$\mathit{Sub}$ 是一个可表的逆变函子，表示对象是 $\Omega$；沿 $g$ 拉回子集，就是预复合 $\chi \circ g$。
- 在 Lean 里：子类型 `{x // p x}` 就是拉回，`Subtype.val` 就是单态射 $f$，`Prop` 就是 $\Omega$，`Set α := α → Prop` 就是 $\mathit{Sub} \cong \mathcal{C}(-, \Omega)$。
- **拓扑斯** = 笛卡尔闭 + 有限极限 + 子对象分类子。若 $\Omega \cong 1 + 1$，称为**布尔**拓扑斯。
- 拓扑斯的内部逻辑是**直觉主义**的：积是“与”，余积是“或”，指数是“蕴含”，但排中律（等价地，双重否定消去）一般不成立。
- Lean 的核心逻辑是构造性的；`Classical.em` 是额外的公理，`#print axioms` 能告诉你一个证明有没有用它。`Decidable` 把可判定的命题拉回到 `Bool`，对它们排中律构造性地成立。
