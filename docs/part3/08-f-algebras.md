# 3.8 F-代数

我们已经见过幺半群的好几种表述：作为集合，作为只有一个对象的范畴，作为幺半范畴中的一个对象。
从这么简单的一个概念里，我们还能再榨出多少汁来？

试试看。取幺半群的这样一个定义：一个集合 $m$，加上一对函数：

$$\mu : m \times m \to m \qquad \eta : 1 \to m$$

这里的 $1$ 是 $\mathbf{Set}$ 中的终对象——单元素集合（Lean 里的 `Unit`）。第一个函数定义乘法（它接收一对元素，返回它们的积），
第二个函数从 $m$ 中选出单位元。并不是随便选两个具有这种签名的函数都能得到幺半群。为此我们还需要附加一些条件：结合律和单位律。
不过我们先暂时忘掉这些，只考虑“潜在的幺半群”。一对函数是两个函数集合的笛卡尔积中的一个元素。我们知道这些集合可以表示为指数对象：

$$\mu \in m^{m \times m} \qquad \eta \in m^{1}$$

这两个集合的笛卡尔积是：

$$m^{m\times m} \times m^{1}$$

用一点中学代数（它在每一个笛卡尔闭范畴中都成立），我们可以把它改写成：

$$m^{\,m\times m + 1}$$

这里的 $+$ 号表示 $\mathbf{Set}$ 中的余积。我们刚刚把一对函数换成了一个函数——下面这个集合中的一个元素：

$$m \times m + 1 \to m$$

这个函数集合中的任何一个元素都是一个潜在的幺半群。

::: info 数学小课堂：为什么“两个函数”等于“一个从和类型出发的函数”
在 Rust 里你一定写过这种东西：

```rust
enum MonoidOp<A> { Empty, Append(A, A) }

fn interpret(op: MonoidOp<i64>) -> i64 {
    match op {
        MonoidOp::Empty => 0,
        MonoidOp::Append(x, y) => x + y,
    }
}
```

`interpret` 是**一个**函数，但它的两个 `match` 分支分别就是 $\eta$（`Empty` 分支，不需要参数，对应 $1 \to m$）和
$\mu$（`Append` 分支，对应 $m \times m \to m$）。从一个枚举（和类型）出发的函数，等价于“每个分支各一个函数”——
这正是指数法则 $m^{a+b} \cong m^a \times m^b$ 在编程里的样子。
:::

这种表述的美妙之处在于，它能引出有趣的推广。比如说，怎样用这种语言来描述**群**（group）？群是一个幺半群，外加一个给每个元素指定逆元的函数。
后者是一个类型为 $m \to m$ 的函数。举个例子，整数构成一个群：二元运算是加法，单位元是零，逆元是取相反数。
要定义一个群，我们从三个函数出发：

$$m \times m \to m \qquad m \to m \qquad 1 \to m$$

和前面一样，我们可以把所有这样的三元组合并成一个函数集合：

$$m \times m + m + 1 \to m$$

我们从一个二元运算符（加法）、一个一元运算符（取负）和一个零元运算符（单位元——这里是零）出发，把它们合并成了一个函数。
所有具有这种签名的函数都定义了潜在的群。

我们可以这样一直做下去。例如，要定义一个**环**（ring），就再添加一个二元运算符和一个零元运算符，依此类推。
每一次，我们最后得到的都是一个函数类型：左边是若干个幂的和（可能包括零次幂——也就是终对象），右边则是集合本身。

现在我们可以放开手脚疯狂推广了。首先，可以把集合换成对象，把函数换成态射。我们可以把 $n$ 元运算符定义为从 $n$ 元积出发的态射。
这意味着我们需要一个支持有限积的范畴。对于零元运算符，我们要求终对象存在。所以我们需要一个笛卡尔范畴。
为了把这些运算符组合起来，我们需要指数，于是它得是笛卡尔闭范畴。最后，我们还需要余积来完成这一套代数把戏。

或者，我们也可以干脆忘掉推导这些公式的过程，只专注于最终的成品。我们态射左边的那个积之和定义了一个自函子。
如果我们改为任选一个自函子 $F$ 呢？那样的话，我们就根本不必对我们的范畴施加任何约束了。由此得到的东西叫作 **F-代数**（F-algebra）。

一个 F-代数是一个三元组，由一个自函子 $F$、一个对象 $a$ 和一个态射

$$F\,a \to a$$

组成。这个对象常被称为**载体**（carrier）、底层对象，或者在编程语境中称为载体**类型**。这个态射常被称为**求值函数**（evaluation function）
或**结构映射**（structure map）。可以把函子 $F$ 想象成负责构造表达式，而态射负责对它们求值。

下面是 F-代数的 Lean 定义：

```lean
/-- `f` 上、载体为 `a` 的 F-代数：就是一个求值函数 `f a → a`。 -/
def Algebra (f : Type → Type) (a : Type) : Type := f a → a
```

它把代数等同于它的求值函数。

::: tip Lean 深入：`def` 定义一个类型
`Algebra f a` 本身是一个**类型**（它的值是函数），所以返回类型写 `Type`。Lean 中类型也是一等公民的值，
`def` 可以像定义普通函数一样定义“类型层面的函数”，这相当于 Haskell 的 `type` 同义词、Rust 的 `type Algebra<F, A> = ...`
（只不过 Rust 不能对“类型构造器 `F`”抽象，这一点 Lean 毫无压力：`f : Type → Type` 就是一个普通参数）。
:::

在幺半群的例子中，相应的函子是：

```lean
inductive MonF (a : Type) where
  | mempty  : MonF a            -- 对应 1
  | mappend : a → a → MonF a    -- 对应 a × a
```

这就是 $1 + a \times a$ 的 Lean 写法（回忆一下[代数数据结构](/part1/06-simple-algebraic-data-types)）。

环可以用下面这个函子来定义：

```lean
inductive RingF (a : Type) where
  | rzero : RingF a             -- 加法单位元 0
  | rone  : RingF a             -- 乘法单位元 1
  | radd  : a → a → RingF a     -- 加法
  | rmul  : a → a → RingF a     -- 乘法
  | rneg  : a → RingF a         -- 取负
```

这是 $1 + 1 + a \times a + a \times a + a$ 的 Lean 写法。

环的一个例子是整数集合。我们可以选 `Int` 作为载体类型，并把求值函数定义为：

```lean
open RingF in
def evalZ : Algebra RingF Int
  | rzero    => 0
  | rone     => 1
  | radd m n => m + n
  | rmul m n => m * n
  | rneg n   => -n

example : evalZ (.radd 2 3) = 5 := rfl
example : evalZ (.rneg 7) = -7 := rfl
```

::: tip Lean 深入：`open ... in` 与 `.radd`
`open RingF in` 只在紧随其后的这一个声明里打开命名空间 `RingF`，于是可以直接写 `rzero` 而不是 `RingF.rzero`。
`example` 里的 `.radd 2 3` 是“前导点”语法：Lean 根据期望的类型（这里是 `RingF Int`）自动补全成 `RingF.radd`。
`example : ... := rfl` 让编译器**验证**这个等式靠计算就成立——比在注释里写“输出 5”可靠得多。
:::

基于同一个函子 `RingF`，还有更多的 F-代数。例如，多项式构成一个环，方阵也构成一个环（本章的挑战题里你会亲手写出它们）。

可以看到，函子的作用是生成表达式，这些表达式可以用代数的求值器来求值。到目前为止，我们只见过非常简单的表达式。
我们通常更感兴趣的是那些可以用递归来定义的、更精巧的表达式。

## 递归

生成任意表达式树的一种方法，是把函子定义中的变量 `a` 换成递归。例如，环中的任意表达式由下面这个树状的数据结构生成：

```lean
inductive Expr where
  | rzero : Expr
  | rone  : Expr
  | radd  : Expr → Expr → Expr
  | rmul  : Expr → Expr → Expr
  | rneg  : Expr → Expr
```

我们可以把原来的环求值器换成它的递归版本：

```lean
namespace Expr
def evalZ : Expr → Int
  | rzero      => 0
  | rone       => 1
  | radd e₁ e₂ => evalZ e₁ + evalZ e₂
  | rmul e₁ e₂ => evalZ e₁ * evalZ e₂
  | rneg e     => -(evalZ e)
end Expr

-- (1 + 1) * (-1) = -2
example : Expr.evalZ (.rmul (.radd .rone .rone) (.rneg .rone)) = -2 := rfl
```

这仍然不太实用，因为我们被迫把所有整数都表示成一串 1 的和，不过应急还是够用的。

::: tip Rust 视角：递归 enum 为什么要 `Box`
同样的类型在 Rust 里得这么写：

```rust
enum Expr {
    Zero,
    One,
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
}

fn eval(e: &Expr) -> i64 {
    match e {
        Expr::Zero => 0,
        Expr::One => 1,
        Expr::Add(a, b) => eval(a) + eval(b),
        Expr::Mul(a, b) => eval(a) * eval(b),
        Expr::Neg(a) => -eval(a),
    }
}
```

Rust 需要 `Box`，是因为它要在编译期知道每个值占多大内存，而一个“直接包含自己”的类型大小是无穷的。
Lean 的归纳类型天然是“装箱”的（值在堆上，构造子保存指针），所以你看不到 `Box`。
但两者背后的数学是同一个问题：**一个“包含自身”的类型到底是什么？**这正是本节要回答的。
:::

但是，怎样用 F-代数的语言来描述表达式树呢？我们必须设法把这样一个过程形式化：递归地用替换的结果去替换函子定义中的自由类型变量。
设想分步来做。首先，把深度为一的树定义为：

```lean
abbrev RingF1 (a : Type) := RingF (RingF a)
```

我们是在用 `RingF a` 生成的深度为零的树去填 `RingF` 定义中的“洞”。深度为二的树可以类似地得到：

```lean
abbrev RingF2 (a : Type) := RingF (RingF (RingF a))
```

我们也可以把它写成：

```lean
example (a : Type) : RingF2 a = RingF (RingF1 a) := rfl

-- 一棵深度为二的树：(1 * 1) + (-(-()))，叶子处放的是 a = Unit 的值
example : RingF2 Unit := .radd (.rmul .rone .rone) (.rneg (.rneg ()))
```

继续这个过程，我们可以写出一个象征性的方程：

```lean no-check
-- 伪代码：Lean 的类型不能这样按自然数下标递归地写
RingF_{n+1} a = RingF (RingF_n a)
```

从概念上讲，把这个过程重复无穷多次之后，我们最终得到的就是我们的 `Expr`。注意 `Expr` 并不依赖于 `a`。我们旅程的起点无关紧要，
我们总是到达同一个地方。对任意范畴中的任意自函子，这并不总是成立，但在 $\mathbf{Set}$ 范畴中，事情都很美好。

当然，这只是一个挥挥手的论证，我稍后会把它弄得更严格。

把一个自函子作用无穷多次，就产生了一个**不动点**（fixed point），一个这样定义的对象：

$$\mathit{Fix}\ f = f\ (\mathit{Fix}\ f)$$

这个定义背后的直觉是：既然我们已经把 $f$ 作用了无穷多次才得到 $\mathit{Fix}\ f$，那么再多作用一次也不会改变什么。
在 Haskell 中，不动点的定义只有一行。把它直译成 Lean，就是：

```lean no-check
inductive Fix (f : Type → Type) where
  | mk : f (Fix f) → Fix f
```

可以说，如果构造子的名字和所定义的类型的名字不一样，这个定义会更易读一些——Haskell 程序员有时把构造子叫作 `In`：

```lean no-check
inductive Fix (f : Type → Type) where
  | In : f (Fix f) → Fix f
```

不过我会沿用公认的记法。（在 Lean 里，构造子总是带着类型名作命名空间，写作 `Fix.mk`，这个问题本来也就不存在。）

::: warning Lean 深入：Lean 拒绝这个定义——严格正性
这两个定义 Lean 都会拒绝：

```text
error: (kernel) arg #2 of 'Fix.mk' contains a non valid occurrence of the datatypes being declared
```

即便加上 `[Functor f]` 约束也一样（报错变成 `arg #3 ... contains a non valid occurrence`）。
这不是 Lean 小气，而是它的**严格正性检查**（strict positivity check）在保护逻辑的一致性。

问题在于 `f` 是**任意的** `Type → Type`。Lean 并不知道 `f` 会把它的参数放在哪里。
如果 `f` 恰好是 `fun a => a → False`，那么 `Fix f` 就相当于下面这个类型（Lean 同样拒绝它）：

```lean no-check
inductive Bad where
  | mk : (Bad → False) → Bad
-- error: (kernel) arg #1 of 'Bad.mk' has a non positive occurrence of the datatypes being declared
```

假如它被接受了，我们马上就能证明 `False`：

```lean no-check
def selfApply : Bad → False
  | .mk g => g (.mk g)          -- 把 b 喂给它自己里面的函数

theorem boom : False := selfApply (.mk selfApply)
```

这就是罗素悖论 / 康托尔对角线论证在类型论里的化身：一个类型“包含从它自己出发的函数”，就能自我指涉。
在 Lean 里，类型就是命题、程序就是证明（柯里–霍华德对应），能证明 `False` 意味着整个系统里任何命题都能被“证明”，
那么本书中所有的定理就都一文不值了。Haskell 允许这种类型，是因为 Haskell 本来就不是逻辑系统：
每个类型里都住着 ⊥（无限循环、`undefined`），`selfApply (Bad selfApply)` 在 Haskell 里只是一个死循环。

**严格正性**的规则是：被定义的类型只能出现在构造子参数类型中箭头的**右边**（“正”的位置），不能出现在任何箭头的左边。
`Bad → False` 里 `Bad` 在箭头左边，违规；而 `f (Fix f)` 中，由于 `f` 是未知的，Lean 无法确认 `Fix f` 处在正位置，只好拒绝。

Lean 能接受的有两种做法。一是对**具体的**函子定义具体的不动点：上面的 `Expr` 就是 `RingF` 的不动点；对 `Option`、`List`
这样 Lean 已经知道是“正”的类型构造子，嵌套也是允许的，比如 `inductive Rose | node : List Rose → Rose`。
二是用 **W 类型**作为所有多项式函子的通用不动点，见本节后面的补充小节。
:::

构造子 `Fix`（或者你更喜欢的 `In`）可以看作一个函数：

```lean no-check
Fix.mk : f (Fix f) → Fix f
```

还有一个函数，它剥掉一层函子应用：

```lean no-check
def unFix : Fix f → f (Fix f)
  | .mk x => x
```

这两个函数互为逆。我们稍后会用到它们。对具体的 `Expr`，这两个函数可以在 Lean 里写出来，并证明它们互逆：

```lean
namespace Expr
/-- 对应 Haskell 的构造子 `Fix :: f (Fix f) -> Fix f`。 -/
def fix : RingF Expr → Expr
  | .rzero    => rzero
  | .rone     => rone
  | .radd x y => radd x y
  | .rmul x y => rmul x y
  | .rneg x   => rneg x

/-- 剥掉一层函子。 -/
def unFix : Expr → RingF Expr
  | rzero    => .rzero
  | rone     => .rone
  | radd x y => .radd x y
  | rmul x y => .rmul x y
  | rneg x   => .rneg x

theorem unFix_fix (x : RingF Expr) : unFix (fix x) = x := by cases x <;> rfl
theorem fix_unFix (e : Expr) : fix (unFix e) = e := by cases e <;> rfl
end Expr
```

::: tip Lean 深入：`cases x <;> rfl`
`cases x` 按 `x` 的构造子分情况（这里 5 种），`<;>` 表示“对上一步产生的**每个**子目标都执行后面的 tactic”。
每种情况下两边都能直接算到同一个值，`rfl` 就收工了。
:::

### 补充：W 类型，Lean 中合法的“通用 Fix”

严格正性拒绝的是“任意的 `f`”。可是我们真正关心的函子——$1 + a\times a$、$1 + 1 + a\times a + a \times a + a$ 等等——
都是**多项式函子**：若干个“形状”，每个形状里有若干个“放 $a$ 的位置”。把这句话直接写成类型：

- `S : Type` 是形状的集合（每个构造子一个形状）；
- `P : S → Type` 告诉我们形状 `s` 有哪些位置（`P s` 有几个元素，这个构造子就有几个 `a`）。

形状 `s` 外加“每个位置放一个 `a`”，就是一个 `(s : S) × (P s → a)`。于是一个多项式函子就是：

```lean
/-- 多项式函子（容器）：选一个形状，再给它的每个位置填上一个 `a`。 -/
structure Poly (S : Type) (P : S → Type) (a : Type) where
  shape : S
  kids  : P shape → a

instance : Functor (Poly S P) where
  map f x := ⟨x.shape, f ∘ x.kids⟩

instance : LawfulFunctor (Poly S P) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

它的不动点在 Lean 中完全合法——这就是类型论里著名的 **W 类型**（W-type，W 取自 well-founded，“良基的”树）：

```lean
inductive W (S : Type) (P : S → Type) where
  | mk : (s : S) → (P s → W S P) → W S P
```

为什么这次 Lean 同意了？因为 `W S P` 出现在 `P s → W S P` 的**箭头右边**，这是严格正的位置。
我们不再把“未知的 `f`”套在 `W` 上，而是把多项式函子的结构**摊开写明**了。

::: info 数学小课堂：容器（container）
“形状 + 位置”的描述叫作**容器**。`List a` 是容器：形状是长度 $n$，位置是 $\{0, \dots, n-1\}$。
`Option a` 也是：两个形状（`none` 没有位置，`some` 有一个位置）。$1 + a\times a$ 也是：一个形状没有位置，另一个形状有两个位置。
一个容器 $(S, P)$ 定义的函子把 $a$ 映到 $\sum_{s\in S} a^{P(s)}$——“幂的和”，正是本章开头推导出来的那种左侧！
:::

W 类型同样带着 `Fix`/`unFix` 这对互逆函数：

```lean
namespace W
def fix : Poly S P (W S P) → W S P
  | ⟨s, k⟩ => mk s k

def unFix : W S P → Poly S P (W S P)
  | mk s k => ⟨s, k⟩

theorem unFix_fix (x : Poly S P (W S P)) : unFix (fix x) = x := rfl
theorem fix_unFix (w : W S P) : fix (unFix w) = w := by cases w; rfl
end W
```

把环的函子编码成容器：五个形状，位置数分别是 0、0、2、2、1。

```lean
inductive RingS where
  | zero | one | add | mul | neg

/-- 每个形状有几个“孩子”：`Empty` 表示没有，`Bool` 表示两个，`Unit` 表示一个。 -/
def RingP : RingS → Type
  | .zero => Empty
  | .one  => Empty
  | .add  => Bool
  | .mul  => Bool
  | .neg  => Unit

abbrev WExpr := W RingS RingP

def wOne : WExpr := .mk .one (fun e => nomatch e)       -- 没有孩子：用 nomatch 处理空类型
def wAdd (x y : WExpr) : WExpr := .mk .add (fun (b : Bool) => if b then y else x)
def wTwo : WExpr := wAdd wOne wOne
```

::: tip Lean 深入：`nomatch`
`Empty` 是没有任何值的类型，所以“从 `Empty` 出发的函数”一种情况都不用写：`fun e => nomatch e` 告诉 Lean
“`e` 不可能存在，这里没有分支”。这正是 $a^0 = 1$：从空集出发的函数恰好有一个。
:::

`WExpr` 与 `Expr` 同构，只是写法更笨重。它的价值在于**通用**：下面讲到的始代数、Lambek 定理、卡塔态射，
我们都能**对所有多项式函子一次性证明**。

## F-代数的范畴

这是全书最古老的把戏：每当你想出一种构造新对象的方法，就看看它们能不能构成一个范畴。不出所料，给定自函子 $F$ 上的代数构成一个范畴。
这个范畴中的对象是代数——由一个载体对象 $a$ 和一个态射 $F\,a \to a$ 组成的对，二者都来自原来的范畴 $\mathcal{C}$。

为了完成这幅图景，我们还得定义 F-代数范畴中的态射。一个态射必须把一个代数 $(a, f)$ 映到另一个代数 $(b, g)$。
我们把它定义为一个映射载体的态射 $m$——在原范畴中从 $a$ 到 $b$。并不是随便什么态射都行：我们希望它与两个求值器相容。
（我们把这种保持结构的态射称为**同态**，homomorphism。）F-代数的同态是这样定义的。首先，注意到我们可以把 $m$ 提升为映射：

$$F\,m : F\,a \to F\,b$$

然后可以在它之后接上 $g$，到达 $b$。等价地，我们也可以用 $f$ 从 $F\,a$ 走到 $a$，再接上 $m$。我们希望这两条路径相等：

$$g \circ F\,m = m \circ f$$

![F-代数同态](/img/3.8/alg.png "F-代数同态 m：先在函子里映射再用 g 求值，等于先用 f 求值再用 m 映射。")

```diagram
FA: (0, 0) "F\,a"
FB: (2, 0) "F\,b"
A: (0, 1.5) "a"
B: (2, 1.5) "b"
Fm: FA -> FB "F\,m"
f: FA -> A "f" side=right
g: FB -> B "g"
m: A -> B "m" side=right
path "先 F m 再 g": Fm g
path "先 f 再 m": f m color=green
caption: 同态的定义：$g \circ F\,m = m \circ f$。点按钮比较两条路径。
```

::: tip Lean 深入：把同态条件写进类型
在 Lean 中，我们把代数和同态都写成结构体，同态的定义把交换条件作为一个字段——**不满足交换条件的函数根本构造不出同态**：

```lean
/-- 一个 F-代数：载体 + 结构映射。 -/
structure Alg (f : Type → Type) where
  carrier : Type
  str : f carrier → carrier

/-- 同态：映射载体的函数，外加“方块交换”的证明。 -/
structure AlgHom (f : Type → Type) [Functor f] (A B : Alg f) where
  map  : A.carrier → B.carrier
  comm : map ∘ A.str = B.str ∘ Functor.map map

/-- 两个同态只要底层函数相同就相等（交换性证明是命题，不携带信息）。 -/
theorem AlgHom.ext {f} [Functor f] {A B : Alg f} {h k : AlgHom f A B}
    (e : h.map = k.map) : h = k := by
  cases h; cases k; cases e; rfl
```
:::

很容易说服自己这确实是一个范畴（提示：$\mathcal{C}$ 中的恒等态射完全可用，而同态的复合仍是同态）。

::: details 在 Lean 中验证：恒等同态与同态的复合
```lean
def AlgHom.id {f} [Functor f] [LawfulFunctor f] (A : Alg f) : AlgHom f A A where
  map := fun x => x
  comm := by
    funext x
    show A.str x = A.str (Functor.map (fun x => x) x)
    rw [id_map']               -- 函子定律：map id = id

def AlgHom.comp {f} [Functor f] [LawfulFunctor f] {A B C : Alg f}
    (g : AlgHom f B C) (h : AlgHom f A B) : AlgHom f A C where
  map := g.map ∘ h.map
  comm := by
    funext x
    show g.map (h.map (A.str x)) = C.str (Functor.map (g.map ∘ h.map) x)
    rw [comp_map]              -- 函子定律：map (g ∘ h) = map g ∘ map h
    have hh := congrFun h.comm x
    have hg := congrFun g.comm (Functor.map h.map x)
    simp only [Function.comp] at hh hg
    rw [hh, hg]                -- 先用 h 的方块，再用 g 的方块
```

- `LawfulFunctor f` 是 Lean 核心库的类型类，要求 `Functor f` 的实例满足函子定律：`id_map`（映射恒等函数什么也不做）和
  `comp_map`（映射一个复合 = 依次映射）。恒等同态需要前者，复合同态需要后者——**函子定律恰好就是“F-代数构成范畴”所需要的东西**。
- `congrFun h x`：从函数相等 `h : φ = ψ` 得到在某一点上的相等 `φ x = ψ x`。
- `show 目标` 把当前目标换成一个定义上相等、但更好读的写法。

结合律与单位律对同态是自动成立的：它们的底层函数就是普通函数的复合，再用 `AlgHom.ext` 即可。
:::

F-代数范畴中的始对象（如果存在的话）叫作**始代数**（initial algebra）。我们把这个始代数的载体叫作 $i$，把它的求值器叫作 $j : F\,i \to i$。
事实证明，始代数的求值器 $j$ 是一个同构。这个结果被称为 **Lambek 定理**。它的证明依赖于始对象的定义：
始对象要求从它到任何其他 F-代数都有唯一的同态 $m$。既然 $m$ 是同态，下面的图就必须交换：

![始代数出发的同态](/img/3.8/alg2.png "从始代数 (i, j) 出发到 (a, f) 的唯一同态 m。")

::: tip Lean 深入：“始”写成结构体
```lean
/-- `I` 是始代数：到任何代数 `B` 都有一个同态，而且只有这一个。 -/
structure IsInitial (f : Type → Type) [Functor f] (I : Alg f) where
  cata : (B : Alg f) → AlgHom f I B
  uniq : ∀ (B : Alg f) (h : AlgHom f I B), h = cata B
```

（字段名叫 `cata`，原因在讲卡塔态射时揭晓。）
:::

现在我们来构造一个载体为 $F\,i$ 的代数。这样一个代数的求值器必须是一个从 $F(F\,i)$ 到 $F\,i$ 的态射。
我们只要提升 $j$，就能轻而易举地构造出这样一个求值器：

$$F\,j : F(F\,i) \to F\,i$$

```lean
/-- 把代数 (a, f) 提升为 (F a, F f)。 -/
def liftAlg (f : Type → Type) [Functor f] (A : Alg f) : Alg f where
  carrier := f A.carrier
  str := Functor.map A.str
```

因为 $(i, j)$ 是始代数，从它到 $(F\,i, F\,j)$ 必定有唯一的同态 $m$。下面的图必须交换：

![到提升代数的同态](/img/3.8/alg3a.png "始代数到 (F i, F j) 的唯一同态 m。")

但我们还有这样一个平凡地交换的图（两条路径是同一条！）：

![j 是同态](/img/3.8/alg3.png "j 本身就是从 (F i, F j) 到 (i, j) 的同态：两条路径完全相同。")

它可以解读为：$j$ 是一个代数同态，把 $(F\,i, F\,j)$ 映到 $(i, j)$。我们可以把这两个图粘在一起，得到：

![粘合后的图](/img/3.8/alg4.png "两个方块并排粘合：外框说明 j ∘ m 是从 (i, j) 到自身的同态。")

```diagram
Fi: (0, 0) "F\,i"
FFi: (2, 0) "F(F\,i)"
Fi2: (4, 0) "F\,i"
i: (0, 1.5) "i"
Fi3: (2, 1.5) "F\,i"
i2: (4, 1.5) "i"
Fm: Fi -> FFi "F\,m"
Fj: FFi -> Fi2 "F\,j"
j1: Fi -> i "j" side=right
Fj2: FFi -> Fi3 "F\,j"
j3: Fi2 -> i2 "j"
m: i -> Fi3 "m" side=right
j4: Fi3 -> i2 "j" side=right
path "上路：F(j∘m) 再 j": Fm Fj j3
path "下路：j 再 j∘m": j1 m j4 color=green
caption: 左方块是 $m$ 的同态条件，右方块平凡交换；整个外框说明 $j \circ m$ 是 $(i, j)$ 到自身的同态。
```

反过来，这个图又可以解读为：$j \circ m$ 是一个代数同态。只不过在这里，两个代数是同一个。而且，因为 $(i, j)$ 是始代数，
从它到它自己只能有一个同态，那就是恒等态射 $\mathrm{id}_i$——我们知道它是一个代数同态。因此 $j \circ m = \mathrm{id}_i$。
利用这一事实和左边那个图的交换性，我们可以证明 $m \circ j = \mathrm{id}_{F i}$。这说明 $m$ 是 $j$ 的逆，因此 $j$ 是 $F\,i$ 与 $i$ 之间的同构：

$$F\,i \cong i$$

而这恰恰是在说：$i$ 是 $F$ 的一个不动点。这就是最初那个挥手论证背后的正式证明。

::: details 补充：Lambek 定理的 Lean 证明（对任意满足函子定律的 `f`）
```lean
theorem lambek {f} [Functor f] [LawfulFunctor f] {I : Alg f} (hI : IsInitial f I) :
    let m : I.carrier → f I.carrier := (hI.cata (liftAlg f I)).map
    (∀ x, I.str (m x) = x) ∧ (∀ y, m (I.str y) = y) := by
  intro m
  -- m 是同态：m ∘ j = F j ∘ F m = F (j ∘ m)
  have hm : ∀ y, m (I.str y) = Functor.map (I.str ∘ m) y := by
    intro y
    have h := congrFun (hI.cata (liftAlg f I)).comm y
    exact h.trans (comp_map m I.str y).symm
  -- 于是 j ∘ m 是从 (i, j) 到它自己的同态
  let jm : AlgHom f I I :=
    { map := I.str ∘ m
      comm := by
        funext y
        show I.str (m (I.str y)) = I.str (Functor.map (I.str ∘ m) y)
        rw [hm y] }
  -- 始代数到自身的同态只有一个，那就是恒等
  have h1 : jm = AlgHom.id I := (hI.uniq I jm).trans (hI.uniq I (AlgHom.id I)).symm
  have h2 : ∀ x, I.str (m x) = x := fun x => congrFun (congrArg AlgHom.map h1) x
  refine ⟨h2, fun y => ?_⟩
  -- m ∘ j = F (j ∘ m) = F id = id
  rw [hm y]
  have : (I.str ∘ m) = id := funext h2
  rw [this, id_map]
```

- `let m : ... := ...` 出现在定理的陈述里，给那个唯一同态起个名字，让陈述更好读。
- `have 名字 : 命题 := 证明` 引入一个中间结论；`let` 引入一个中间**数据**（这里是同态 `jm`）。
- `h1` 是整个证明的核心一步：`jm` 和 `AlgHom.id I` 都等于 `hI.cata I`（由唯一性），所以它们彼此相等。
  `Eq.trans`（写作 `.trans`）把 `a = b` 和 `b = c` 串成 `a = c`，`.symm` 把等式翻转。
- `refine ⟨h2, fun y => ?_⟩` 说“合取的第一半用 `h2`，第二半我接着证”，`?_` 是留给后续 tactic 的洞。
:::

回到代码：我们认出 $i$ 就是我们的 `Fix f`（在 Lean 中是 `Expr` 或 `W S P`），$j$ 就是构造子 `Fix`（`Expr.fix`），而它的逆就是 `unFix`。
Lambek 定理中的同构告诉我们：为了得到始代数，我们取函子 $f$，把它的参数 $a$ 替换成 `Fix f`。我们也看到了为什么不动点不依赖于 $a$。

## 自然数

自然数也可以定义成一个 F-代数。出发点是一对态射：

$$\mathit{zero} : 1 \to N \qquad \mathit{succ} : N \to N$$

第一个挑出零，第二个把所有的数映到它们的后继。和前面一样，我们可以把两者合并成一个：

$$1 + N \to N$$

左边定义了一个函子，在 Lean 中可以这样写：

```lean
inductive NatF (a : Type) where
  | zeroF : NatF a
  | succF : a → NatF a

instance : Functor NatF where
  map f
    | .zeroF   => .zeroF
    | .succF n => .succF (f n)

instance : LawfulFunctor NatF where
  map_const := rfl
  id_map x := by cases x <;> rfl
  comp_map f g x := by cases x <;> rfl
```

（`NatF a` 和 `Option a` 是同构的——`zeroF` 对应 `none`，`succF` 对应 `some`。）

这个函子的不动点（它所生成的始代数）可以在 Lean 中编码为：

```lean no-check
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```

这正是 Lean 核心库里 `Nat` 的定义，一字不差。一个自然数要么是零，要么是另一个数的后继。这被称为自然数的**皮亚诺表示**（Peano representation）。

::: tip Lean 深入：`Nat` 真的是这样定义的，但不会真的这样存
Lean 的 `Nat` 在逻辑上就是这个一元（unary）的归纳类型，所有证明都按 `zero`/`succ` 进行归纳；
但编译器会把它特殊处理成高效的任意精度整数（GMP），所以 `2^100` 并不会造出一百多位长的 `succ` 链。
这是“逻辑上的定义”与“运行时的表示”分离的好例子。
:::

::: details 补充：证明 `Nat` 是 `NatF` 的始代数
```lean
def natStr : NatF Nat → Nat
  | .zeroF   => 0
  | .succF n => n + 1

def natAlg : Alg NatF := ⟨Nat, natStr⟩

/-- 从 Nat 到任意 NatF-代数的映射：按皮亚诺结构递归。 -/
def cataNat {a : Type} (alg : NatF a → a) : Nat → a
  | 0     => alg .zeroF
  | n + 1 => alg (.succF (cataNat alg n))

def natInitial : IsInitial NatF natAlg where
  -- 存在性：cataNat 是同态（按两种情况检查方块，都是计算）
  cata B := { map := cataNat B.str, comm := by funext x; cases x <;> rfl }
  -- 唯一性：任何同态 h 都和 cataNat 逐点相等，对 n 归纳
  uniq B h := by
    apply AlgHom.ext
    funext n
    show h.map n = cataNat B.str n
    induction n with
    | zero => exact congrFun h.comm NatF.zeroF
    | succ n ih =>
      have hc := congrFun h.comm (NatF.succF n)
      refine hc.trans ?_
      show B.str (.succF (h.map n)) = B.str (.succF (cataNat B.str n))
      rw [ih]
```

把 Lambek 定理用在 `natInitial` 上，立刻得到 `NatF Nat ≅ Nat`——也就是 `Option Nat ≅ Nat`（`none ↦ 0`、`some n ↦ n + 1`）。
:::

::: info 数学小课堂：数学归纳法 = 自然数是始代数
“$P(0)$ 成立，且 $P(n) \Rightarrow P(n+1)$，则对所有 $n$ 都有 $P(n)$”——这就是数学归纳法。
上面唯一性证明里的 `induction n` 正是它：基础情形 `zero`，归纳步骤 `succ n ih`（`ih` 是归纳假设 $P(n)$）。
反过来说，**“自然数是 `NatF` 的始代数”这句话本身就是归纳法的范畴论表述**：从自然数出发、遵守 0 和后继结构的映射
只有一种定义方式，那就是递归。
:::

## 卡塔态射

我们用编程的记号把“始性”条件重写一遍。我们把始代数叫作 `Fix f`，它的求值器是构造子 `Fix`。
从始代数到同一函子上的任何其他代数，都存在唯一的态射 `m`。我们挑一个载体为 `a`、求值器为 `alg` 的代数。

![卡塔态射](/img/3.8/alg5.png "从 (Fix f, Fix) 到 (a, alg) 的唯一同态 m。")

顺便注意一下 `m` 是什么：它是不动点的求值器，是整棵递归表达式树的求值器。我们来找一个实现它的通用方法。

Lambek 定理告诉我们，构造子 `Fix` 是一个同构。我们把它的逆称为 `unFix`。因此，我们可以把这个图中的一个箭头翻转过来，得到：

![翻转后的图](/img/3.8/alg6.png "把 Fix 翻转成 unFix：m 等于 unFix、fmap m、alg 三者的复合。")

```diagram
FFix: (0, 0) "f\,(\mathrm{Fix}\,f)"
Fa: (2.4, 0) "f\,a"
Fix: (0, 1.5) "\mathrm{Fix}\,f"
a: (2.4, 1.5) "a"
unFix: Fix -> FFix "\mathrm{unFix}"
fm: FFix -> Fa "\mathrm{fmap}\ m"
alg: Fa -> a "\mathit{alg}"
m: Fix -> a "m" side=right
path "直接走 m": m
path "unFix，fmap m，再 alg": unFix fm alg color=green
caption: 卡塔态射的定义就是这个方块的交换条件：$m = \mathit{alg} \circ \mathrm{fmap}\ m \circ \mathrm{unFix}$。
```

我们写下这个图的交换条件：

```lean no-check
m = alg ∘ Functor.map m ∘ unFix
```

我们可以把这个等式解读为 `m` 的一个递归定义。对用函子 `f` 创建的任何有限的树，这个递归都必定终止。注意到 `fmap m` 作用在函子 `f` 的顶层之下，
就能明白这一点。换句话说，它作用在原树的孩子上。孩子总是比原来的树浅一层。

下面是把 `m` 应用到一棵用 `Fix f` 构造的树上时发生的事：`unFix` 的作用是剥掉构造子，露出树的顶层。
接着我们把 `m` 应用到顶层节点的所有孩子上，产生类型为 `a` 的结果。最后，我们应用非递归的求值器 `alg`，把这些结果组合起来。
关键在于，我们的求值器 `alg` 是一个简单的、非递归的函数。

既然对任何代数 `alg` 都可以这样做，那么定义一个以代数为参数、给出我们称为 `m` 的那个函数的高阶函数就很合理了。
这个高阶函数叫作**卡塔态射**（catamorphism）。在 Haskell 中，它就是上面那个等式的字面翻译；在 Lean 中，我们对 W 类型给出它的定义：

```lean
/-- 卡塔态射：对 W 类型（多项式函子的通用不动点）。 -/
def W.cata {S : Type} {P : S → Type} {a : Type} (alg : Poly S P a → a) : W S P → a
  | .mk s k => alg ⟨s, fun p => W.cata alg (k p)⟩
```

::: tip Lean 深入：为什么通用的 `cata` 只能对 W 类型写
对**未知的** `f`，Lean 里写不出 `cata alg = alg ∘ Functor.map (cata alg) ∘ unFix`：一来通用的 `Fix f` 本身就不存在，
二来 Lean 的终止检查器也看不出 `Functor.map` 只会作用在“更小”的子树上。对 W 类型，右边先把每个孩子 `k p` 递归地折叠成 `a`
（这就是 `fmap (cata alg)`），再把这一层交给 `alg`；Lean 看到 `k p` 是 `.mk s k` 的直接子项，于是接受这个递归。
:::

::: details 补充：证明 `cata alg` 是从始代数出发的唯一同态（对每一个多项式函子）
```lean
def wAlg (S : Type) (P : S → Type) : Alg (Poly S P) := ⟨W S P, W.fix⟩

def wInitial (S : Type) (P : S → Type) : IsInitial (Poly S P) (wAlg S P) where
  cata B := { map := W.cata B.str, comm := by funext x; cases x; rfl }
  uniq B h := by
    apply AlgHom.ext
    funext w
    show h.map w = W.cata B.str w
    -- 对树做归纳：ih 说“对每个孩子，h 与 cata 相等”
    induction w with
    | mk s k ih =>
      have hc := congrFun h.comm ⟨s, k⟩
      refine hc.trans ?_
      show B.str ⟨s, h.map ∘ k⟩ = B.str ⟨s, fun p => W.cata B.str (k p)⟩
      exact congrArg (fun g => B.str ⟨s, g⟩) (funext ih)
```

`induction w` 对 W 类型做**结构归纳**：要证明性质对 `.mk s k` 成立，可以假设它对所有孩子 `k p` 都已成立（`ih : ∀ p, ...`）。
这是自然数归纳法在树上的推广。孩子即使有无穷多个（`P s` 是无限类型），归纳法照样有效——这就是“良基”的意思。

再套用 `lambek`：对任何多项式函子，`W.fix : Poly S P (W S P) → W S P` 都是同构。
:::

我们来看一个例子。取定义自然数的那个函子（就是上面的 `NatF`）。我们选 `Nat × Nat` 作为载体类型，把代数定义为：

```lean
def fib : NatF (Nat × Nat) → Nat × Nat
  | .zeroF        => (1, 1)
  | .succF (m, n) => (n, m + n)
```

你很容易说服自己：这个代数的卡塔态射 `cataNat fib` 计算的是斐波那契数。（Lean 可以替我们检查：）

```lean
#guard (List.range 10).map (fun n => (cataNat fib n).1) == [1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
```

::: tip Lean 深入：`#guard`
`#guard 布尔表达式` 在编译时求值，若结果不是 `true` 就报错。它适合检查“程序算出来的结果”，
而 `example : ... := rfl` 适合检查“定义上相等”。两者都比在注释里写“输出是……”可靠。
:::

一般来说，`NatF` 的一个代数定义了一个递推关系：用前一个元素的值表示当前元素的值。而卡塔态射则计算出这个数列的第 $n$ 个元素。

### 补充：卡塔态射动画

为了亲眼看一看“同一个递归结构、不同的解释”，我们换一个更适合画图的表达式函子：带整数字面量的 `ExprF`，以及它的具体不动点 `Tree`。

```lean
inductive ExprF (a : Type) where
  | lit : Int → ExprF a
  | add : a → a → ExprF a
  | mul : a → a → ExprF a
  | neg : a → ExprF a

/-- ExprF 的具体不动点。 -/
inductive Tree where
  | lit : Int → Tree
  | add : Tree → Tree → Tree
  | mul : Tree → Tree → Tree
  | neg : Tree → Tree

/-- Tree 上的卡塔态射：先递归折叠孩子，再把这一层交给 alg。 -/
def Tree.cata {a : Type} (alg : ExprF a → a) : Tree → a
  | .lit n   => alg (.lit n)
  | .add x y => alg (.add (cata alg x) (cata alg y))
  | .mul x y => alg (.mul (cata alg x) (cata alg y))
  | .neg x   => alg (.neg (cata alg x))

def evalAlg : ExprF Int → Int
  | .lit n   => n
  | .add x y => x + y
  | .mul x y => x * y
  | .neg x   => -x

def showAlg : ExprF String → String
  | .lit n   => toString n
  | .add x y => "(" ++ x ++ " + " ++ y ++ ")"
  | .mul x y => x ++ " * " ++ y
  | .neg x   => "-(" ++ x ++ ")"

def countAlg : ExprF Nat → Nat
  | .lit _   => 1
  | .add x y => x + y + 1
  | .mul x y => x + y + 1
  | .neg x   => x + 1

def depthAlg : ExprF Nat → Nat
  | .lit _   => 1
  | .add x y => max x y + 1
  | .mul x y => max x y + 1
  | .neg x   => x + 1

/-- (2 + 3) * 4 -/
def sample : Tree := .mul (.add (.lit 2) (.lit 3)) (.lit 4)

#guard sample.cata evalAlg == 20
#guard sample.cata showAlg == "(2 + 3) * 4"
#guard sample.cata countAlg == 5
#guard sample.cata depthAlg == 3
```

四个代数**都不是递归函数**——每个只描述“一层”怎么算。递归只写了一次，在 `Tree.cata` 里。下面的动画逐步执行 `cata alg`：
橙色节点是当前这一步，此时它的孩子已经变成了载体里的值，`alg` 看到的只是一层 `ExprF a`。

<div class="ch-widget-wrap">
<Ch3_8CataAnimation />
</div>

::: tip Rust 视角：visitor / fold 模式
在 Rust 里，你可能写过这样的“fold trait”：每种节点一个方法，参数是**已经算好的**子结果。

```rust
enum Tree { Lit(i64), Add(Box<Tree>, Box<Tree>), Mul(Box<Tree>, Box<Tree>), Neg(Box<Tree>) }

trait ExprAlg {
    type Carrier;
    fn lit(&self, n: i64) -> Self::Carrier;
    fn add(&self, x: Self::Carrier, y: Self::Carrier) -> Self::Carrier;
    fn mul(&self, x: Self::Carrier, y: Self::Carrier) -> Self::Carrier;
    fn neg(&self, x: Self::Carrier) -> Self::Carrier;
}

fn cata<A: ExprAlg>(alg: &A, t: &Tree) -> A::Carrier {
    match t {
        Tree::Lit(n) => alg.lit(*n),
        Tree::Add(x, y) => { let (x, y) = (cata(alg, x), cata(alg, y)); alg.add(x, y) }
        Tree::Mul(x, y) => { let (x, y) = (cata(alg, x), cata(alg, y)); alg.mul(x, y) }
        Tree::Neg(x) => { let x = cata(alg, x); alg.neg(x) }
    }
}

struct Eval;
impl ExprAlg for Eval {
    type Carrier = i64;
    fn lit(&self, n: i64) -> i64 { n }
    fn add(&self, x: i64, y: i64) -> i64 { x + y }
    fn mul(&self, x: i64, y: i64) -> i64 { x * y }
    fn neg(&self, x: i64) -> i64 { -x }
}
```

`ExprAlg` 的一个实现就是一个 F-代数（关联类型 `Carrier` 是载体），`cata` 就是卡塔态射。
和经典的 visitor 模式相比，区别在于 visitor 通常让每个方法自己决定要不要、何时递归访问孩子；而 fold/代数风格把递归**统一收归** `cata`，
每个代数只处理一层。编译器（如 rustc 自己的 `TypeFolder`、`syn` 的 `Fold` trait）大量使用这种风格。
:::

## 折叠

元素类型为 `e` 的列表，是下面这个函子的始代数：

```lean
inductive ListF (e a : Type) where
  | nilF  : ListF e a
  | consF : e → a → ListF e a
```

确实，把变量 `a` 替换成递归的结果（我们把它叫作 `List e`），就得到：

```lean no-check
inductive List (e : Type) where
  | nil  : List e
  | cons : e → List e → List e
```

（这正是 Lean 核心库中 `List` 的定义：`[]` 是 `nil`，`x :: xs` 是 `cons x xs`。）

列表函子的代数选定一个特定的载体类型，并定义一个对两个构造子做模式匹配的函数。它在 `nilF` 上的值告诉我们如何对空列表求值，
而它在 `consF` 上的值告诉我们如何把当前元素与此前累积的值组合起来。（列表上的卡塔态射写出来是这样的：）

```lean
def cataList {e a : Type} (alg : ListF e a → a) : List e → a
  | []      => alg .nilF
  | x :: xs => alg (.consF x (cataList alg xs))
```

例如，下面是一个可以用来计算列表长度的代数（载体类型是 `Nat`）：

```lean
def lenAlg {e : Type} : ListF e Nat → Nat
  | .consF _ n => n + 1
  | .nilF      => 0

#guard cataList lenAlg ['a', 'b', 'c'] == 3
```

确实，由此得到的卡塔态射 `cataList lenAlg` 计算的就是列表的长度。注意，这个求值器是两样东西的组合：(1) 一个接收列表元素和累加器、
返回新累加器的函数；(2) 一个初始值，这里是零。值的类型和累加器的类型都由载体类型给出。

把它和传统的定义比较一下：

```lean
def length' {e : Type} : List e → Nat := List.foldr (fun _ n => n + 1) 0

#guard length' ['a', 'b', 'c'] == 3
```

`foldr` 的两个参数，恰好就是代数的两个组成部分。

我们再试一个例子：

```lean
def sumAlg : ListF Float Float → Float
  | .consF e s => e + s
  | .nilF      => 0.0

#guard cataList sumAlg [1.0, 2.5, 3.5] == 7.0
```

同样，把它和下面这个比较：

```lean
def sum' : List Float → Float := List.foldr (fun e s => e + s) 0.0

#guard sum' [1.0, 2.5, 3.5] == 7.0
```

可以看到，`foldr` 不过是卡塔态射在列表上的一个方便的特化。

::: tip Lean 深入：把“特化”写成定理
对任何代数，列表上的卡塔态射都等于以代数两部分为参数的 `foldr`：

```lean
theorem cataList_eq_foldr {e a : Type} (alg : ListF e a → a) (xs : List e) :
    cataList alg xs = xs.foldr (fun x acc => alg (.consF x acc)) (alg .nilF) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [cataList, ih]
```
:::

::: tip Rust 视角：`fold` 与 `rfold`
Rust 的 `Iterator::fold` 是**左**折叠（从头往尾累积）；与 `foldr` 对应的是 `DoubleEndedIterator::rfold`：
`xs.iter().rfold(0, |acc, _| acc + 1)`。卡塔态射天然是右折叠，因为列表的结构是“头 + 尾”，先折叠尾部（孩子），再处理头部。
:::

## 余代数

照例，我们有一个对偶的构造：**F-余代数**（F-coalgebra），其中态射的方向反了过来：

$$a \to F\,a$$

给定函子上的余代数同样构成一个范畴，其中的同态保持余代数结构。这个范畴中的终对象 $(t, u)$ 叫作**终余代数**（terminal 或 final coalgebra）。
对于每个其他的（余）代数 $(a, f)$，都存在唯一的同态 $m$，使下面的图交换：

![终余代数](/img/3.8/alg7.png "从任意余代数 (a, f) 到终余代数 (t, u) 的唯一同态 m。")

```diagram
Ft: (0, 0) "F\,t"
Fa: (2, 0) "F\,a"
t: (0, 1.5) "t"
a: (2, 1.5) "a"
u: t -> Ft "u"
f: a -> Fa "f" side=right
m: a -> t "m"
Fm: Fa -> Ft "F\,m" side=right
path "先 m 再 u": m u
path "先 f 再 F m": f Fm color=green
caption: 余代数同态：$u \circ m = F\,m \circ f$。
```

终余代数是这个函子的一个不动点，意思是态射 $u : t \to F\,t$ 是一个同构（余代数的 Lambek 定理）：

$$F\,t \cong t$$

在编程中，终余代数通常被解读为生成（可能无限的）数据结构或状态转移系统的配方。

正如卡塔态射可以用来对始代数求值，**安娜态射**（anamorphism）可以用来对终余代数进行“余求值”（coevaluate）：

```lean no-check
-- Haskell 原书的定义，用 Lean 记号写出（对通用的 Fix 无法在 Lean 中编译）
def ana (coalg : a → f a) : a → Fix f := Fix.mk ∘ Functor.map (ana coalg) ∘ coalg
```

::: warning 易错点：这在 Lean 里有两个障碍
通用的 `Fix` 不存在；更要紧的是，这个递归**没有任何东西在变小**——它从种子出发不断“向外”生成，可能永不停止。
Lean 只接受全函数，所以不能这样写。下面会看到，对流这样的具体函子，我们可以给终余代数一个具体的模型，安娜态射就成了全函数。
:::

余代数的一个典型例子建立在这样一个函子上：它的不动点是类型为 `e` 的元素组成的无限流。这就是那个函子：

```lean
/-- StreamF e a：一个元素，外加“下一个种子”。 -/
structure StreamF (e a : Type) where
  head : e
  next : a
```

而这是它的不动点（Haskell 中只有一个构造子的递归类型，“头 + 尾”）：

```lean
inductive IStream (e : Type) where
  | cons : e → IStream e → IStream e
```

::: warning 易错点：在 Lean 里，上面这个类型是空的
Lean 接受了 `IStream` 的定义（它是严格正的），但它**一个值都没有**：要造一个 `IStream`，你得先有一个 `IStream`，没有起点。

```lean
theorem IStream.isEmpty {e : Type} (s : IStream e) : False := by
  induction s with
  | cons _ _ ih => exact ih
```

归纳类型给出的是函子的**最小**不动点——也就是**始代数**——而 `StreamF e` 的始代数是空类型（$\emptyset \cong e \times \emptyset$，确实是个不动点！）。
我们想要的无限流是**最大**不动点，即**终余代数**。在 $\mathbf{Set}$ 中，它可以具体地表示为函数 $\mathbb{N} \to e$：

```lean
/-- 流：从位置到元素的函数。这是 StreamF e 的终余代数的一个具体模型。 -/
def Strm (e : Type) : Type := Nat → e

namespace Strm
def hd (s : Strm e) : e := s 0
def tl (s : Strm e) : Strm e := fun n => s (n + 1)
def cons (x : e) (s : Strm e) : Strm e
  | 0     => x
  | n + 1 => s n
def take : Nat → Strm e → List e
  | 0,     _ => []
  | n + 1, s => s.hd :: take n s.tl
end Strm
```

`(hd, tl)` 就是终余代数的结构映射 $u : t \to F\,t$，`cons` 是它的逆——这就是余代数的 Lambek 定理在这里的具体样子。

- Haskell 的列表是惰性的，所以同一个类型既能表示有限列表也能表示无限列表；Lean 是**严格求值**的，`List` 只能是有限的。
- Lean 4（本书使用的 4.34）支持 `coinductive` **谓词**（`Prop` 中的余归纳定义），但不支持余归纳**数据类型**。
  所以无限结构要么用函数表示（如 `Nat → e`），要么用 `Thunk` 手动延迟，要么在“有界”的意义下处理（只展开有限步，即 fuel 技巧）。
- 也可以用 `partial def` 写出可能不终止的展开。`partial def` 编译后照样能运行，但 Lean 不会把它的定义展开用于证明——
  你得到了程序，失去了推理。
:::

`StreamF e` 的余代数是一个函数，它接收类型为 `a` 的种子，产生一个对（`StreamF` 是“对”的一个花哨名字），由一个元素和下一个种子组成。
（用 `Strm` 做模型，安娜态射就是一个全函数：第 $n$ 个元素就是把种子推进 $n$ 步之后吐出的那个元素。）

```lean
/-- 把种子向前推进 n 步。 -/
def iterateNext {e a : Type} (coalg : a → StreamF e a) : Nat → a → a
  | 0,     x => x
  | n + 1, x => iterateNext coalg n (coalg x).next

/-- 流的安娜态射。 -/
def ana' {e a : Type} (coalg : a → StreamF e a) (seed : a) : Strm e :=
  fun n => (coalg (iterateNext coalg n seed)).head
```

::: details 补充：证明 `Strm e` 是终余代数（`ana'` 是唯一的余代数同态）
```lean
-- 同态条件：头 = 余代数吐出的元素，尾 = 下一个种子展开成的流
theorem ana_hd {e a} (c : a → StreamF e a) (x : a) : (ana' c x).hd = (c x).head := rfl
theorem ana_tl {e a} (c : a → StreamF e a) (x : a) : (ana' c x).tl = ana' c (c x).next := rfl

/-- 唯一性：任何满足同态条件的 h 都等于 ana'。 -/
theorem ana_unique {e a} (c : a → StreamF e a) (h : a → Strm e)
    (hhd : ∀ x, (h x).hd = (c x).head) (htl : ∀ x, (h x).tl = h (c x).next) :
    h = ana' c := by
  funext x n
  induction n generalizing x with
  | zero => exact hhd x
  | succ n ih =>
    show (h x).tl n = _
    rw [htl x, ih]
    rfl
```

唯一性证明对位置 $n$ 归纳。但第 $n+1$ 个元素关于种子 `x` 的结论，要用到第 $n$ 个元素关于**另一个**种子 `(c x).next` 的结论，
所以归纳假设必须对所有种子成立。`generalizing x` 正是让归纳假设变成“对所有 `x`”。
:::

你可以很容易地构造出一些简单的余代数，产生无限序列，比如平方数列，或者倒数数列。

```lean
def squares : Strm Nat := ana' (fun n => ⟨n * n, n + 1⟩) 0

#guard squares.take 6 == [0, 1, 4, 9, 16, 25]
```

一个更有意思的例子是产生素数列表的余代数。诀窍是用一个无限列表作为载体。我们的初始种子是列表 `[2..]`。
下一个种子是这个列表的尾部，并删去所有 2 的倍数。它是从 3 开始的奇数列表。下一步，我们取这个列表的尾部，删去所有 3 的倍数，依此类推。
你也许认出来了，这就是埃拉托色尼筛法的雏形。这个余代数由下面的函数实现：

```lean
/-- 筛子的种子：从 `start` 起、不被 `primes` 里任何数整除的所有自然数（一个无限列表的有限描述）。 -/
structure Sieve where
  start  : Nat
  primes : List Nat

def Sieve.notdiv (ps : List Nat) (n : Nat) : Bool := ps.all (fun p => n % p != 0)

/-- 找到从 n 开始第一个通过筛子的数。fuel 保证终止（由 Bertrand 公设，n 步之内必有素数）。 -/
def Sieve.firstFrom (ps : List Nat) (n : Nat) : Nat → Nat
  | 0        => n
  | fuel + 1 => if Sieve.notdiv ps n then n else Sieve.firstFrom ps (n + 1) fuel

/-- 余代数：吐出无限列表的头 p，新种子是尾部删去 p 的倍数。 -/
def era (s : Sieve) : StreamF Nat Sieve :=
  let p := Sieve.firstFrom s.primes s.start s.start
  ⟨p, ⟨p + 1, p :: s.primes⟩⟩
```

::: tip Lean 深入：无限列表的有限描述与 fuel 技巧
Lean 没有惰性的无限列表，但“剩余的无限列表”——也就是“从 `start` 开始、不被 `primes` 中任何数整除的所有数”——
可以用 `Sieve` 这个有限的结构精确地描述。“取尾部并删去 $p$ 的倍数”就变成了“`start` 移到 $p+1$，把 $p$ 加入筛子”。

`firstFrom` 里多出来的参数 `fuel`（燃料）是写全函数的常用手法：每递归一次就烧掉一点燃料，燃料耗尽就停。
Lean 看到 `fuel` 在结构上变小，就接受了这个递归。代价是我们得自己保证燃料“够用”——这里由数学（Bertrand 公设：$n$ 与 $2n$ 之间必有素数）
保证。如果不想操这份心，也可以写 `partial def`，但那样就不能对它做证明了。
:::

这个余代数的安娜态射生成素数列表：

```lean
def primes : Strm Nat := ana' era ⟨2, []⟩

#guard primes.take 10 == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
```

下面的动画逐步展示 `era` 的工作：每一步它吐出种子的头部，再从尾部删掉它的倍数。

<div class="ch-widget-wrap">
<Ch3_8Sieve />
</div>

流是一个无限列表，所以应该可以把它转换成一个 Haskell 列表。为此，我们可以用同一个函子 `StreamF` 构成一个代数，并在它上面运行一个卡塔态射。
例如，下面就是一个把流转换为列表的卡塔态射：

```lean no-check
-- Haskell 原书的做法，用 Lean 记号写出：在 Lean 中无法成立
def toListC : Fix (StreamF e) → List e := cata al
  where al : StreamF e (List e) → List e
    | ⟨e, a⟩ => e :: a
```

这里，同一个不动点同时是同一个自函子的始代数和终余代数。在任意范畴中并不总是这样。一般来说，一个自函子可能有很多个不动点（也可能一个都没有）。
始代数是所谓的**最小不动点**，而终余代数是**最大不动点**。不过在 Haskell 中，两者由同一个公式定义，它们是重合的。

::: info 数学小课堂：最小与最大不动点（以及 Lean 中的情形）
想想集合上的方程 $X = 1 + e \times X$（列表函子）。“最小”的解是所有**有限**列表：从空列表开始，一步步加元素能造出来的东西。
“最大”的解还额外包含**无限**列表：只要能一直“拆”下去（拆出一个头，剩下的仍可以继续拆），就算数。
归纳（induction）讲“能从底下造出来”，余归纳（coinduction）讲“能一直拆下去”。

Haskell 的惰性列表是后者，Lean 的 `List` 是前者。所以在 Lean（以及 $\mathbf{Set}$）中，两种不动点泾渭分明：
`StreamF e` 的始代数是空的 `IStream e`，终余代数是 `Nat → e`；上面的 `toListC` 也无从写起——我们只能用 `Strm.take` 取一个有限前缀。
:::

列表的安娜态射叫作 **unfold**。为了创建有限列表，函子被修改为产生一个 `Option` 对：

```lean
partial def unfoldr {a b : Type} (f : b → Option (a × b)) (seed : b) : List a :=
  match f seed with
  | none            => []
  | some (x, seed') => x :: unfoldr f seed'

#guard unfoldr (fun n => if n < 5 then some (n * n, n + 1) else none) 0 == [0, 1, 4, 9, 16]
```

值 `none` 会终止列表的生成。（`unfoldr` 只能写成 `partial def`：Lean 无法确认任意的 `f` 总会在某一时刻返回 `none`。）

余代数的一个有趣的例子与透镜有关。一个透镜（lens）可以表示成一对 getter 和 setter：

```lean no-check
set : a → s → a
get : a → s
```

这里，`a` 通常是某个积数据类型，其中有一个类型为 `s` 的字段。getter 读取这个字段的值，setter 把这个字段替换成一个新值。
这两个函数可以合并成一个：

```lean no-check
a → s × (s → a)
```

我们还可以把这个函数进一步改写成：

```lean no-check
a → Store s a
```

其中我们定义了一个函子：

```lean
structure Store (s a : Type) where
  peek : s → a     -- 给定一个新字段值，得到整体
  pos  : s         -- 当前的字段值

instance : Functor (Store s) where
  map g x := ⟨g ∘ x.peek, x.pos⟩

/-- 一个透镜就是一个 Store s 的余代数。 -/
def lensCoalg {a s : Type} (get : a → s) (set : a → s → a) : a → Store s a :=
  fun x => ⟨set x, get x⟩
```

注意，这不是一个由积之和构造出来的简单代数函子。它涉及一个指数 $a^s$。

透镜是这个函子的一个余代数，载体类型为 `a`。我们之前见过，`Store s` 也是一个[余单子](/part3/07-comonads)。
事实证明，一个非常良好（very well behaved）的透镜对应于一个与余单子结构相容的余代数。我们将在下一节讨论这一点。

## 挑战

1. 为一元多项式环实现求值函数。你可以把多项式表示为 $x$ 的各次幂前面的系数组成的列表。例如，$4x^2 - 1$ 表示为（从零次幂开始）`[-1, 0, 4]`。
2. 把上一题的构造推广到多个独立变量的多项式，比如 $x^2 y - 3y^3 z$。
3. 实现 $2 \times 2$ 矩阵环的代数。
4. 定义一个余代数，使其安娜态射产生自然数的平方组成的列表。
5. 用 `unfoldr` 生成前 $n$ 个素数组成的列表。

::: details 参考答案
**1. 一元多项式。** 载体是 `List Int`（系数表），加法逐项相加（长度不同时补零），乘法是卷积。

```lean
abbrev Poly1 := List Int

def Poly1.add : Poly1 → Poly1 → Poly1
  | [],     q      => q
  | p,      []     => p
  | a :: p, b :: q => (a + b) :: Poly1.add p q

def Poly1.scale (c : Int) (p : Poly1) : Poly1 := p.map (c * ·)

/-- (a + x·p) · q = a·q + x·(p·q) -/
def Poly1.mul : Poly1 → Poly1 → Poly1
  | [],     _ => []
  | a :: p, q => Poly1.add (Poly1.scale a q) (0 :: Poly1.mul p q)

/-- 在一点求值（霍纳法则），用于检验。 -/
def Poly1.eval (p : Poly1) (x : Int) : Int := p.foldr (fun c acc => c + x * acc) 0

def evalPoly : Algebra RingF Poly1
  | .rzero    => []
  | .rone     => [1]
  | .radd p q => Poly1.add p q
  | .rmul p q => Poly1.mul p q
  | .rneg p   => p.map (- ·)

-- (2x - 1)(2x + 1) = 4x² - 1
#guard evalPoly (.rmul [-1, 2] [1, 2]) == [-1, 0, 4]
#guard Poly1.eval [-1, 0, 4] 3 == 35
```

**2. 多元多项式。** 用“项的列表”表示：每一项是系数加上一个单项式（变量名与指数的列表）。这里不做合并同类项的规范化——
代数只需要给出一个环结构；规范化可以作为额外练习。

```lean
abbrev PolyN := List (Int × List (String × Nat))

def PolyN.evalAt (env : String → Int) (p : PolyN) : Int :=
  p.foldr (fun (c, ms) acc => c * ms.foldr (fun (v, k) m => env v ^ k * m) 1 + acc) 0

def evalPolyN : Algebra RingF PolyN
  | .rzero    => []
  | .rone     => [(1, [])]
  | .radd p q => p ++ q
  | .rmul p q => p.flatMap (fun (c, m) => q.map (fun (d, n) => (c * d, m ++ n)))
  | .rneg p   => p.map (fun (c, m) => (-c, m))

def env₀ : String → Int
  | "x" => 2 | "y" => 3 | "z" => 5 | _ => 0

-- x²y - 3y³z 在 x=2, y=3, z=5 处：12 - 405 = -393
#guard (evalPolyN (.radd [(1, [("x", 2), ("y", 1)])] [(-3, [("y", 3), ("z", 1)])])).evalAt env₀ == -393
```

**3. 2×2 矩阵。**

```lean
structure M2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving BEq, Repr

def evalM2 : Algebra RingF M2
  | .rzero    => ⟨0, 0, 0, 0⟩
  | .rone     => ⟨1, 0, 0, 1⟩
  | .radd m n => ⟨m.a + n.a, m.b + n.b, m.c + n.c, m.d + n.d⟩
  | .rmul m n => ⟨m.a * n.a + m.b * n.c, m.a * n.b + m.b * n.d,
                  m.c * n.a + m.d * n.c, m.c * n.b + m.d * n.d⟩
  | .rneg m   => ⟨-m.a, -m.b, -m.c, -m.d⟩

-- 斐波那契矩阵的平方
#guard evalM2 (.rmul ⟨1, 1, 1, 0⟩ ⟨1, 1, 1, 0⟩) == ⟨2, 1, 1, 1⟩
```

**4. 平方数。** 正文里的 `squares` 就是：种子是 $n$，吐出 $n^2$，下一个种子是 $n+1$。若要有限列表，用 `unfoldr` 并在某处返回 `none`：

```lean
def squaresUpTo (k : Nat) : List Nat :=
  unfoldr (fun n => if n ≤ k then some (n * n, n + 1) else none) 0

#guard squaresUpTo 5 == [0, 1, 4, 9, 16, 25]
```

**5. 前 n 个素数。** 种子里多带一个计数器，计数到零时返回 `none`：

```lean
def primeStep : Nat × Sieve → Option (Nat × (Nat × Sieve))
  | (0, _)     => none
  | (k + 1, s) =>
    let ⟨p, s'⟩ := era s
    some (p, (k, s'))

def firstPrimes (n : Nat) : List Nat := unfoldr primeStep (n, ⟨2, []⟩)

#guard firstPrimes 8 == [2, 3, 5, 7, 11, 13, 17, 19]
#guard firstPrimes 0 == []
```
:::

## 本章小结

- 幺半群、群、环的运算都可以合并成一个函数 $F\,m \to m$，左边是“幂的和”。把它推广到任意自函子 $F$，就得到 **F-代数** $(a,\ F\,a \to a)$：$F$ 构造表达式，结构映射对表达式求值。
- F-代数之间的**同态**是与求值相容的映射：$g \circ F\,m = m \circ f$。F-代数构成范畴，而这恰好需要函子定律（`LawfulFunctor`）。
- **始代数**的结构映射是同构（**Lambek 定理**），所以始代数是函子的不动点 $F\,i \cong i$。我们在 Lean 中对任意函子证明了它。
- Lean 的**严格正性检查**拒绝通用的 `Fix f`，因为对 `f a = a → False` 它会导出矛盾。替代方案是为具体函子写具体的不动点，或用 **W 类型**作为所有多项式函子的通用不动点。
- 自然数是 `NatF`（即 `Option`）的始代数；**数学归纳法**正是这一事实的另一种说法。
- **卡塔态射** `cata alg` 是从始代数出发的唯一同态：递归只写一次，每个代数只处理一层。`foldr` 是卡塔态射在列表上的特化。
- 对偶地，**F-余代数** $a \to F\,a$ 生成结构，**安娜态射**展开种子；**终余代数**是最大不动点，代表（可能无限的）数据。
- 在 Lean 中，归纳类型给出最小不动点（`StreamF` 的始代数是空类型！），无限流需用 `Nat → e` 之类的模型、fuel 或 `partial def` 处理。Haskell 中两种不动点因惰性而重合。
- 透镜是 `Store s` 函子的余代数；下一章将看到，“非常良好”的透镜正是 `Store` 余单子的余代数。
