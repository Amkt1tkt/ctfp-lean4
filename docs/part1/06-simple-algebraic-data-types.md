# 1.6 简单代数数据类型

我们已经见过两种把类型组合起来的基本方式：积和余积。事实证明，日常编程里的大量数据结构，单凭这两种机制就能搭出来。
这件事有很实际的后果：数据结构的许多性质是**可以复合的**。比如，只要你知道怎样比较基本类型的值是否相等，
又知道怎样把这种比较推广到积类型和余积类型上，那么复合类型的相等判断就可以自动推导出来。
在 Haskell 里，你可以为一大类复合类型自动派生出相等、比较、与字符串互相转换等等操作；
Lean 也一样——只要在类型定义后面写上 `deriving DecidableEq, Repr, Ord, Hashable`，编译器就替你把活干完了。
（Rust 程序员对此再熟悉不过：`#[derive(PartialEq, Eq, Debug, Hash)]` 背后正是同一个道理。）

下面我们就来仔细看看积类型与和类型在编程中的样子。

```lean hidden
/-! 第 1.6 章：简单代数数据类型。本章不需要 Prelude 中的范畴定义。 -/
```

## 积类型

在编程语言里，两个类型之积的标准实现就是**序对**（pair）。在 Haskell 中，序对是语言内建的类型构造子；
在 C++ 中，它是标准库里一个相当复杂的模板。在 Lean 中，序对是核心库里的结构体 `Prod α β`，写作 `α × β`（输入法：`\x` 或 `\times`）；
在 Rust 中则是内建的元组 `(A, B)`。

![两只手拉手的小猪 a 和 b](/img/1.6/pair.jpg "一个序对：两个值手拉手，谁也离不开谁。")

序对并不是严格可交换的：序对 `Int × Bool` 不能被当作 `Bool × Int` 来用，尽管它们携带的信息一模一样。
但它们**在同构意义下**是可交换的——这个同构由函数 `swap` 给出（而 `swap` 恰好是它自己的逆）：

```lean
def swap {α β : Type} : α × β → β × α
  | (x, y) => (y, x)
```

::: tip Lean 深入：用模式匹配定义函数
`def swap ... : α × β → β × α` 后面紧跟的 `| (x, y) => (y, x)` 是**按模式匹配定义函数**的写法：
函数的参数没有名字，直接用一个“模式” `(x, y)` 去拆开它。这相当于 Rust 的

```rust
fn swap<A, B>((x, y): (A, B)) -> (B, A) {
    (y, x)
}
```

花括号里的 `{α β : Type}` 是**隐式参数**：调用 `swap (1, true)` 时，Lean 会自己推断出 `α := Nat`、`β := Bool`，
就像 Rust 推断泛型参数 `<A, B>` 一样。
:::

你可以把这两种序对想成是同一份数据的两种存储格式，就像大端序和小端序一样。

“`swap` 是它自己的逆”这句话，在 Lean 里可以写成一条定理并证明：

```lean
theorem swap_swap {α β : Type} (p : α × β) : swap (swap p) = p := by
  cases p   -- 把 p 拆成 (x, y)
  rfl       -- swap (swap (x, y)) 按定义就算出 (x, y)
```

::: info 数学小课堂：什么是“同构”
两个集合（或类型）$A$ 和 $B$ **同构**（isomorphic），意思是它们之间存在一对互逆的函数：

- $f : A \to B$，
- $g : B \to A$，

满足“走过去再走回来，等于没动”：对所有 $a \in A$ 有 $g(f(a)) = a$，对所有 $b \in B$ 有 $f(g(b)) = b$。
记作 $A \cong B$。

直观地说，同构的两个集合“元素一一对应”，只是给元素起的名字（或者说存储格式）不同。
例如 $\{\text{红}, \text{绿}\}$ 和 $\{0, 1\}$ 同构：让红 ↦ 0、绿 ↦ 1，反过来 0 ↦ 红、1 ↦ 绿。
同构的集合在“结构”上没有区别——任何只关心结构的问题，对两者的答案都一样。

注意两条往返恒等**缺一不可**：只有 $g(f(a)) = a$ 的话，$f$ 只是单射，$B$ 可能比 $A$ 大得多。
:::

## 补充：在 Lean 里把“同构”写成一个结构体

原书在这一章会反复说“这两个类型同构”“这个函数是可逆的”，然后请你相信它。
在 Lean 里我们可以做得更好：**把“同构”本身定义成一个数据结构**，它不仅装着两个方向的函数，
还装着“它们互逆”的**证明**。没有证明，就造不出这个结构体的值——编译器会替我们把关。

```lean
/-- 类型 `α` 与 `β` 之间的同构：两个方向的函数，加上两条往返恒等的证明。 -/
structure TypeIso (α β : Type) where
  to     : α → β
  inv    : β → α
  inv_to : ∀ a, inv (to a) = a   -- 先 to 后 inv：回到原处
  to_inv : ∀ b, to (inv b) = b   -- 先 inv 后 to：也回到原处

infix:25 " ≅ " => TypeIso
```

::: tip Lean 深入：结构体里可以放“证明”
`structure` 和 Rust 的 `struct` 很像：一组带名字的字段。不同的是，Lean 的字段类型可以是**命题**，
比如 `∀ a, inv (to a) = a`。这种字段的“值”就是一个证明。这是 Lean 作为依值类型语言的看家本领：
**不变量直接写进类型里**。Rust 里你只能在文档里写“调用者保证 `inv` 是 `to` 的逆”，
Lean 里这句话是类型检查的一部分。

`infix:25 " ≅ " => TypeIso` 定义了一个中缀记号，于是 `α ≅ β` 就是 `TypeIso α β`（`≅` 输入 `\cong` 或 `\iso`）。
数字 25 是优先级，比 `×`（35）和 `⊕`（30）低，所以 `α × β ≅ β × α` 会被正确地读成 `(α × β) ≅ (β × α)`。
:::

有了它，“序对在同构意义下可交换”就成了一个**有类型的值**：

```lean
def prodComm (α β : Type) : α × β ≅ β × α where
  to     := swap
  inv    := swap
  inv_to := swap_swap
  to_inv := swap_swap
```

同构可以“原地不动”（自反）、可以“倒过来”（对称）、也可以“接起来”（传递）。
这三件事让 `≅` 成为一种**等价关系**——这正是“在同构意义下相等”这种说法站得住脚的原因：

::: details 同构的自反、对称、传递（完整证明）
```lean
namespace TypeIso

/-- 每个类型都和自己同构 -/
def refl (α : Type) : α ≅ α := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

/-- 同构可以倒过来 -/
def symm {α β : Type} (e : α ≅ β) : β ≅ α := ⟨e.inv, e.to, e.to_inv, e.inv_to⟩

/-- 两个同构可以首尾相接 -/
def trans {α β γ : Type} (e₁ : α ≅ β) (e₂ : β ≅ γ) : α ≅ γ where
  to     := e₂.to ∘ e₁.to
  inv    := e₁.inv ∘ e₂.inv
  inv_to a := by simp [Function.comp, e₂.inv_to, e₁.inv_to]
  to_inv c := by simp [Function.comp, e₁.to_inv, e₂.to_inv]

end TypeIso
```

`⟨…, …⟩` 是**匿名构造子**记号：只要 Lean 知道期望的类型是哪个结构体，就可以按字段顺序直接填值。
`simp [...]` 是一个化简 tactic：它用方括号里给出的等式（以及库里标记为化简规则的等式）反复改写目标，直到化简不动为止。
这里它先展开 `∘`，再用 `e₂.inv_to`、`e₁.inv_to` 把 `e₁.inv (e₂.inv (e₂.to (e₁.to a)))` 一层层消掉。
:::

下面这张图就是“同构”的样子。点按钮，看看两条往返路径是不是都等于原地不动：

```diagram
top: (2, -0.75) ""
bot: (2, 0.75) ""
A: (0, 0) "\alpha \times \beta"
B: (4, 0) "\beta \times \alpha"
to: A -> B "\mathtt{swap}" bend=45
inv: B -> A "\mathtt{swap}" bend=45
idA: A -> A "\mathrm{id}" loop=left
idB: B -> B "\mathrm{id}" loop=right
path "先 to 再 inv": to inv
path "直接 id": idA color=green
caption: 一个同构：去程与回程复合起来，等于什么也没做（两边都是如此）。
```

回到原书。你可以把任意多个类型嵌套成序对的序对，来得到它们的积。不过还有更简单的办法：
嵌套的序对等价于**元组**（tuple）。这是因为序对的各种嵌套方式彼此同构。
如果你想按顺序把三个类型 `α`、`β`、`γ` 组合成一个积，有两种做法：

```lean no-check
(α × β) × γ
```

或者

```lean no-check
α × (β × γ)
```

这两个类型是不同的——你不能把其中一个传给期望另一个的函数——但它们的元素之间存在一一对应。
有一个函数把前者映到后者：

```lean
def alpha {α β γ : Type} : (α × β) × γ → α × (β × γ)
  | ((x, y), z) => (x, (y, z))
```

而且这个函数是可逆的：

```lean
def alphaInv {α β γ : Type} : α × (β × γ) → (α × β) × γ
  | (x, (y, z)) => ((x, y), z)
```

所以它是一个同构。这只是把同一份数据换个方式重新打包而已。在 Lean 里，“它是同构”同样可以写下来并检查：

```lean
def prodAssoc (α β γ : Type) : (α × β) × γ ≅ α × (β × γ) where
  to     := alpha
  inv    := alphaInv
  inv_to := by intro ⟨⟨x, y⟩, z⟩; rfl   -- 拆开嵌套的序对，然后按定义计算
  to_inv := by intro ⟨x, y, z⟩; rfl
```

::: tip Lean 深入：Lean 的元组就是嵌套的序对
Lean 里的 `×` 是**右结合**的：`α × β × γ` 就是 `α × (β × γ)`，而 `(1, 2, 3)` 就是 `(1, (2, 3))`。
换句话说，Lean 干脆没有单独的“三元组”类型——元组**就是**嵌套的序对。这两条都能被编译器直接验证：

```lean
example : (Nat × Nat × Nat) = (Nat × (Nat × Nat)) := rfl
example : (1, 2, 3) = (1, (2, 3)) := rfl
```

Rust 则不同：`(A, B, C)` 和 `(A, (B, C))` 是两个不同的类型（内存布局也可能不同），它们只是同构。
上面 `intro ⟨x, y, z⟩` 能一次拆开 `α × (β × γ)`，用的正是这种右结合的约定。
:::

你可以把“构造积类型”看成类型上的一种二元运算。从这个角度看，上面的同构很像我们在幺半群里见过的结合律：

$$(a * b) * c = a * (b * c)$$

只不过在幺半群里，两种复合方式得到的结果是**相等**的，而这里它们只是“在同构意义下相等”。

如果我们能接受同构、不苛求严格相等，还可以走得更远：证明单位类型 `Unit`（Haskell 里写作 `()`）是积的单位元，
就像 1 是乘法的单位元一样。确实，把某个类型 `α` 的值和一个单位值配成对，并不会增加任何信息。类型

```lean no-check
α × Unit
```

同构于 `α`。同构如下：

```lean
def rho {α : Type} : α × Unit → α
  | (x, ()) => x
```

```lean
def rhoInv {α : Type} : α → α × Unit :=
  fun x => (x, ())
```

```lean
def prodUnit (α : Type) : α × Unit ≅ α where
  to     := rho
  inv    := rhoInv
  inv_to := fun (_, ()) => rfl   -- 拆开序对后，两边按定义相同
  to_inv := fun _ => rfl
```

::: details 左单位律 `Unit × α ≅ α`
单位元在左边也一样。这次我们直接在 `where` 里写匿名函数，不再单独起名：

```lean
def unitProd (α : Type) : Unit × α ≅ α where
  to     := fun ((), x) => x
  inv    := fun x => ((), x)
  inv_to := fun ((), _) => rfl
  to_inv := fun _ => rfl
```
:::

这些观察可以被形式化为一句话：$\mathbf{Set}$（集合范畴）是一个**幺半范畴**（monoidal category）。
它是一个范畴，同时也是一个幺半群——意思是你可以把对象“乘”起来（这里就是取它们的笛卡尔积）。
我以后会更多地讨论幺半范畴，并给出完整定义。

在 Haskell 里，还有一种更通用的定义积类型的方式——尤其是当它和和类型结合起来时，我们很快就会看到。
它使用带名字、带多个参数的构造子。比如，序对可以另外定义成：

```lean
inductive Pair (α β : Type) where
  | P : α → β → Pair α β
```

这里，`Pair α β` 是一个由另外两个类型 `α` 和 `β` 参数化的类型的名字；`P` 是**数据构造子**（data constructor）的名字。
把两个类型传给**类型构造子** `Pair`，你就定义了一个序对类型；把两个类型合适的值传给构造子 `P`，你就构造出一个序对值。
例如，我们来定义一个值 `stmt`，它是 `String` 和 `Bool` 的序对：

```lean
def stmt : Pair String Bool := Pair.P "This statement is" false
```

第一部分 `stmt : Pair String Bool` 是类型签名。它使用类型构造子 `Pair`，用 `String` 和 `Bool` 替换了 `Pair` 通用定义中的 `α` 和 `β`。
`:=` 之后定义了实际的值：把一个具体的字符串和一个具体的布尔值传给数据构造子 `P`。
类型构造子用来构造类型；数据构造子用来构造值。（这句话本身是“假”的——这是个说谎者悖论的小玩笑。）

::: tip Lean 深入：`inductive`、类型构造子与数据构造子
`inductive` 声明一个新类型，并列出它的所有构造子，每个构造子写成 `| 名字 : 参数类型 → … → 结果类型`。
这和 Rust 的 `enum` 非常接近：

```rust
enum Pair<A, B> {
    P(A, B),
}
```

在 Lean 里，`Pair` 本身的类型是 `Type → Type → Type`：它是一个“吃两个类型、吐出一个类型”的函数。
而构造子 `Pair.P` 的类型是 `α → β → Pair α β`。构造子住在类型的**命名空间**里，所以全名是 `Pair.P`；
若写 `open Pair`，就可以直接写 `P`。另外，当期望的类型已知时，还可以用前导点号简写：`(.P "x" true : Pair String Bool)`。
:::

```lean
#check (Pair : Type → Type → Type)
#check (@Pair.P : {α β : Type} → α → β → Pair α β)
```

在 Haskell 中，类型构造子和数据构造子的名字空间是分开的，所以你经常会看到同一个名字既用作类型、又用作构造子。
Lean 的情况类似：构造子的全名是 `类型名.构造子名`，所以给构造子起一个和类型一样的名字也不会冲突：

```lean
namespace Version2

inductive Pair (α β : Type) where
  | Pair : α → β → Pair α β

def stmt : Pair String Bool := Pair.Pair "This statement is" false

end Version2
```

（为了不和前面的 `Pair` 重名，这里把它放进了命名空间 `Version2`。不过 Lean 的习惯是把唯一的构造子叫作 `mk`——
`structure` 默认就会生成一个叫 `mk` 的构造子。）

如果你眯起眼睛看，甚至可以把内建的序对类型看作这类声明的一个变体，只不过名字 `Pair` 被换成了二元运算符。
在 Haskell 里这个构造子叫作 `(,)`；在 Lean 里，它就是 `Prod` 的构造子 `Prod.mk`。你可以像使用任何其他具名构造子那样，
用前缀写法来构造序对：

```lean
def stmt' : String × Bool := Prod.mk "This statement is" false

example : stmt' = ("This statement is", false) := rfl
```

类似地，Haskell 用 `(,,)` 构造三元组，以此类推；而在 Lean 里，三元组只是 `Prod.mk x (Prod.mk y z)`。

除了使用通用的序对或元组，你还可以定义具体的、带名字的积类型，例如：

```lean
structure Stmt where
  mk ::
  text  : String
  value : Bool
```

它不过是 `String` 和 `Bool` 的积，但有了自己的名字和构造子。这种声明风格的好处是：
你可以定义许多内容相同、但意义和功能不同的类型，而且它们彼此不能互相替代。

::: tip Rust 视角：newtype 模式
这正是 Rust 中 newtype 模式的用意：`struct Meters(f64);` 和 `struct Seconds(f64);` 里装的都是 `f64`，
但编译器不允许你把秒数传给需要米数的函数。
Lean 的 `structure` 同样会创造一个**新的**类型；与之相对，`abbrev Stmt' := String × Bool` 只是起了个别名，
`Stmt'` 和 `String × Bool` 可以随意互换。
:::

用元组和多参数构造子编程，很容易变得一团乱、还容易出错——你得时刻记着哪个分量代表什么。
通常更好的做法是给分量起名字。带有具名字段的积类型，在 Haskell 里叫作**记录**（record），在 C 里叫作 `struct`，
在 Lean 里就是 `structure`，在 Rust 里是 `struct`。

## 记录

来看一个简单的例子。我们想描述化学元素：把两个字符串（名称和符号）和一个整数（原子序数）合成一个数据结构。
我们可以用元组 `String × String × Int`，并且记住哪个分量代表什么。提取分量时用模式匹配，
就像下面这个函数，它检查元素的符号是否是其名称的前缀（比如 **He** 是 **Helium** 的前缀）：

```lean
def startsWithSymbol₀ : String × String × Int → Bool
  | (name, symbol, _) => symbol.isPrefixOf name

#guard startsWithSymbol₀ ("Helium", "He", 2)
```

（`#guard` 让 Lean 在编译时求值一个布尔表达式，结果不是 `true` 就报错。本书用它来写“被机器检查过的输出”。
模式里的 `_` 是通配符，表示“这里有个值，但我不关心”。）

这样的代码容易出错，也难以阅读和维护。更好的做法是定义一个记录：

```lean
structure Element where
  name         : String
  symbol       : String
  atomicNumber : Int
deriving Repr
```

这两种表示是同构的，下面这两个互逆的转换函数就是见证：

```lean
def tupleToElem : String × String × Int → Element
  | (n, s, a) => { name := n, symbol := s, atomicNumber := a }
```

```lean
def elemToTuple (e : Element) : String × String × Int :=
  (e.name, e.symbol, e.atomicNumber)
```

```lean
def elemIso : String × String × Int ≅ Element where
  to     := tupleToElem
  inv    := elemToTuple
  inv_to := fun (_, _, _) => rfl
  to_inv := fun ⟨_, _, _⟩ => rfl
```

注意，记录字段的名字同时也是访问这些字段的函数。例如，`Element.atomicNumber e` 从 `e` 中取出 `atomicNumber` 字段。
`Element.atomicNumber` 就是一个这种类型的函数：

```lean
#check (Element.atomicNumber : Element → Int)
```

有了 `Element` 的记录语法，函数 `startsWithSymbol` 变得更好读了：

```lean
def startsWithSymbol (e : Element) : Bool :=
  String.isPrefixOf (Element.symbol e) (Element.name e)
```

在 Haskell 里，我们还可以用一个小技巧：用反引号把函数 `isPrefixOf` 包起来，把它变成中缀运算符，让代码读起来几乎像一句话：
``symbol e `isPrefixOf` name e``。Lean 里对应的技巧是**点号记法**（generalized field notation）：
如果 `s : String`，那么 `s.isPrefixOf t` 就是 `String.isPrefixOf s t`。于是：

```lean
def startsWithSymbol' (e : Element) : Bool :=
  e.symbol.isPrefixOf e.name

#guard startsWithSymbol' { name := "Helium", symbol := "He", atomicNumber := 2 }
#guard !startsWithSymbol' { name := "Sodium", symbol := "Na", atomicNumber := 11 }
```

这一版不需要任何括号，因为在 Lean（以及 Haskell）里，函数应用和点号访问的优先级比任何中缀运算符都高。

::: tip Rust 视角
这个记录在 Rust 里一模一样，连点号写法都一样：

```rust
struct Element {
    name: String,
    symbol: String,
    atomic_number: i32,
}

fn starts_with_symbol(e: &Element) -> bool {
    e.name.starts_with(&e.symbol)
}
```

区别在于：Lean 的 `e.symbol.isPrefixOf e.name` 是一个**普通函数调用的语法糖**——Lean 会在类型 `String` 的命名空间里找名叫
`isPrefixOf` 的函数，并把 `e.symbol` 作为它的第一个（类型匹配的）显式参数。你自己写的 `def String.shout (s : String) := s ++ "!"`
马上就能用 `"hi".shout` 调用，不需要像 Rust 那样写 `impl` 块或扩展 trait。
:::

## 和类型

正如集合范畴中的积产生了积类型，余积则产生了**和类型**（sum type）。Haskell 中和类型的标准实现是 `Either`。
在 Lean 核心库里，它叫 `Sum`，写作 `α ⊕ β`（输入 `\oplus`），定义如下（这是核心库的定义，这里只展示）：

```lean no-check
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β   -- “左”内射，Haskell 的 Left
  | inr (val : β) : Sum α β   -- “右”内射，Haskell 的 Right
```

与序对一样，`Sum` 在同构意义下是可交换的，可以嵌套，而且嵌套的顺序无关紧要（同样是在同构意义下）。
于是我们可以定义一个与三元组对应的和类型，比如：

```lean
inductive OneOfThree (α β γ : Type) where
  | sinistral : α → OneOfThree α β γ   -- 拉丁语“左边的”
  | medial    : β → OneOfThree α β γ   -- “中间的”
  | dextral   : γ → OneOfThree α β γ   -- “右边的”
```

等等。

::: details 和的交换律与结合律（完整证明）
`Sum.swap` 是核心库里交换左右的函数，`Sum.swap_swap` 是“交换两次等于没换”的定理：

```lean
def sumComm (α β : Type) : α ⊕ β ≅ β ⊕ α where
  to     := Sum.swap
  inv    := Sum.swap
  inv_to := Sum.swap_swap
  to_inv := Sum.swap_swap

def sumAssoc (α β γ : Type) : (α ⊕ β) ⊕ γ ≅ α ⊕ (β ⊕ γ) where
  to
    | .inl (.inl a) => .inl a
    | .inl (.inr b) => .inr (.inl b)
    | .inr c        => .inr (.inr c)
  inv
    | .inl a        => .inl (.inl a)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr c) => .inr c
  -- rcases 按模式一次拆开嵌套的和；`<;>` 表示“对拆出来的每一种情况都执行 rfl”
  inv_to := by intro x; rcases x with (a | b) | c <;> rfl
  to_inv := by intro x; rcases x with a | b | c <;> rfl
```

`.inl a` 中的前导点号是简写：Lean 根据期望的类型知道这里指的是 `Sum.inl`。
:::

事实证明，$\mathbf{Set}$ 关于余积也是一个（对称的）幺半范畴。二元运算的角色由不交并扮演，单位元的角色由始对象扮演。
用类型的语言说，`Sum` 是幺半运算，而 `Empty`——没有任何值的类型（Haskell 里叫 `Void`）——是它的中性元。
你可以把 `Sum` 想成加法，把 `Empty` 想成零。确实，往和类型里加上 `Empty` 不会改变它的内容。例如：

```lean no-check
α ⊕ Empty
```

同构于 `α`。这是因为没有任何办法构造出这个类型的 `inr` 版本——根本不存在 `Empty` 类型的值。
`α ⊕ Empty` 的居民只能用 `inl` 构造，它们不过是把一个 `α` 类型的值包了一层。所以，用符号表示就是 $a + 0 = a$。

```lean
def sumEmpty (α : Type) : α ⊕ Empty ≅ α where
  to
    | .inl a => a
    | .inr e => nomatch e   -- e : Empty 不可能存在，这一支不需要给出任何结果
  inv    := Sum.inl
  inv_to := by
    intro x
    cases x with
    | inl a => rfl
    | inr e => cases e      -- 对 Empty 做情况分析：零种情况，证明自动完成
  to_inv := fun _ => rfl
```

::: tip Lean 深入：`Empty` 与 `nomatch`
Lean 的 `Empty` 是一个**没有任何构造子**的归纳类型：`inductive Empty : Type`。
对它做模式匹配时，需要列出的分支数是零，所以 `nomatch e` 就是一个“已经处理完所有情况”的完整匹配，
它可以充当**任何**类型的值。这和 Rust 里的 `enum Void {}` 以及 `match v {}` 完全一样：

```rust
enum Void {}

fn absurd<T>(v: Void) -> T {
    match v {}
}
```
:::

和类型在 Haskell 里非常常见，而在 C++ 里与之对应的联合体（union）或变体（variant）则少见得多。这有几个原因。
在这一点上 Rust 站在 Haskell 这一边：Rust 的 `enum` 就是货真价实的和类型，而且是 Rust 编程的日常。
下面我们沿着原书的思路，看看 C++ 的各种“替代品”，以及 Rust 和 Lean 是怎么做的。

首先，最简单的和类型就是枚举，在 C++ 里用 `enum` 实现。下面这个 Haskell/Lean 和类型

```lean
inductive Color where
  | red | green | blue
```

在 C++ 中是 `enum { Red, Green, Blue };`，在 Rust 中则是

```rust
enum Color {
    Red,
    Green,
    Blue,
}
```

更简单的和类型是

```lean no-check
inductive Bool where
  | false | true
```

它在 C++ 里就是原生的 `bool`。（这是 Lean 核心库中 `Bool` 的真实定义，所以这里只展示、不重新定义。）
从“和”的角度看，`Bool` 就是 `Unit ⊕ Unit`：两个各只有一个值的类型加起来，正好两个值——$2 = 1 + 1$。

```lean
def boolIso : Bool ≅ Unit ⊕ Unit where
  to b := if b then .inr () else .inl ()
  inv
    | .inl () => false
    | .inr () => true
  inv_to := by intro b; cases b <;> rfl
  to_inv := by intro x; rcases x with ⟨⟩ | ⟨⟩ <;> rfl
```

编码“有值或没有值”的简单和类型，在 C++ 里有各种实现方式：用特殊技巧和“不可能的”值，比如空字符串、负数、空指针等等。
这种可选性如果是有意为之，在 Haskell 里用 `Maybe` 类型表达；Lean 里它叫 `Option`（与 Rust 的 `Option` 同名同义），
构造子是 `none` 和 `some`。它在核心库中的定义如下（只展示）：

```lean no-check
inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α
```

`Option` 类型是两个类型的和。把两个构造子分别拆成单独的类型，你就能看出这一点。第一个看起来是这样的：

```lean
inductive NothingType where
  | nothing
```

它是一个只有一个值（叫作 `nothing`）的枚举。换句话说，它是一个单例，等价于单位类型 `Unit`。第二部分：

```lean
inductive JustType (α : Type) where
  | just : α → JustType α
```

只是把类型 `α` 包了一层。我们本可以把 `Maybe` 编码成：

```lean
def Maybe (α : Type) : Type := Unit ⊕ α
```

（`Option α` 和 `Unit ⊕ α` 同构的严格证明，留到本章的挑战 1。）

::: tip Rust 视角：`Option` 才是正道
Rust 的标准库在这件事上和 Haskell/Lean 完全一致：没有空指针，没有“用 -1 表示没找到”，只有 `Option<T>`。
`str::find` 返回 `Option<usize>`，`HashMap::get` 返回 `Option<&V>`。
C++ 程序员用“不可能的值”默默编码的东西，在 Rust 和 Lean 里都被提升成了类型系统里看得见的和类型。
:::

更复杂的和类型在 C++ 里常常用指针来伪造。指针要么为空，要么指向某个特定类型的值。
例如，Haskell 的列表类型可以定义成一个（递归的）和类型。在 Lean 中：

```lean
inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α
```

（Lean 自带的 `List` 正是这样定义的，构造子叫 `List.nil` 和 `List.cons`，并有记号 `[]` 与 `x :: xs`；
为了不和它冲突，我们这里叫 `MyList`。）

在 C++ 里，它可以借助空指针技巧来实现：类 `List` 内部只有一个指向 `Node<A>` 的指针 `_head`；
无参构造函数把 `_head` 设为 `nullptr`，代表 `Nil`；接受一个值和一个列表的构造函数则新分配一个节点，代表 `Cons`。
注意，Haskell 的两个构造子 `Nil` 和 `Cons` 被翻译成了 `List` 类的两个重载构造函数，参数也类似
（`Nil` 没有参数；`Cons` 接受一个值和一个列表）。`List` 类不需要标签来区分和类型的两个分量，
而是用 `_head` 的特殊值 `nullptr` 来编码 `Nil`。

用 Rust 照着 C++ 的结构写，空指针要换成 `Option<Box<…>>`：

```rust
struct Node<A> {
    head: A,
    tail: Option<Box<Node<A>>>,
}

pub struct List<A> {
    head: Option<Box<Node<A>>>, // None 扮演 C++ 的 nullptr
}

impl<A> List<A> {
    pub fn nil() -> Self {
        List { head: None }
    }
    pub fn cons(a: A, l: List<A>) -> Self {
        List { head: Some(Box::new(Node { head: a, tail: l.head })) }
    }
}

// 编译期断言：Option<Box<T>> 和裸指针一样大——None 就是用空指针表示的
const _: () = assert!(std::mem::size_of::<Option<Box<u8>>>() == std::mem::size_of::<Box<u8>>());
```

最后那行断言很有意思：Rust 编译器的“空位优化”（niche optimization）**自动**做了 C++ 程序员手工做的事——
用空指针来代表 `None`。区别在于，在 Rust 里这是编译器的实现细节，类型层面你看到的始终是一个诚实的和类型。
当然，地道的 Rust 写法是直接用 `enum`，和 Lean 的定义一一对应：

```rust
enum MyList<A> {
    Nil,
    Cons(A, Box<MyList<A>>),
}
```

不过，Haskell 类型和 C++ 类型之间的主要区别在于：Haskell 的数据结构是不可变的。
如果你用某个构造子创建了一个对象，这个对象将永远记得它是用哪个构造子、以哪些参数创建的。
所以一个以 `just "energy"` 创建的 `Maybe` 对象永远不会变成 `nothing`。
同样，空列表永远是空的，一个有三个元素的列表永远是那三个元素。Lean 的值也是如此。

::: tip Rust 视角：可变性
在 Rust 里，只要你手里有 `&mut Option<String>`，就可以 `*opt = None`，把一个 `Some("energy")` 原地改成 `None`。
Lean 里没有这回事：值一旦构造出来就不会再变。（Lean 的运行时会在引用计数为 1 时偷偷原地复用内存，
但这是看不见的优化，语义上一切都是不可变的。）
:::

正是这种不可变性，使得构造是**可逆**的。给定一个对象，你总能把它拆回构造它时用的那些部件。
这种拆解通过模式匹配完成，它把构造子重新当作模式来用。构造子的参数（如果有的话）则换成变量（或者其他模式）。

`MyList` 数据类型有两个构造子，所以拆解任意一个 `MyList` 要用两个与之对应的模式：一个匹配空列表 `nil`，
另一个匹配由 `cons` 构造的列表。例如，下面是一个作用在 `MyList` 上的简单函数的定义：

```lean
def maybeTail {α : Type} : MyList α → Option (MyList α)
  | .nil      => none
  | .cons _ t => some t
```

`maybeTail` 定义的第一部分用构造子 `nil` 作为模式，返回 `none`。第二部分用构造子 `cons` 作为模式。
它把构造子的第一个参数换成了通配符，因为我们对它不感兴趣；`cons` 的第二个参数绑定到变量 `t` 上
（我会把这些东西叫作变量，尽管严格说来它们从不变化：一旦绑定到某个表达式，变量就再也不会改变）。
返回值是 `some t`。现在，取决于你的 `MyList` 是怎样创建的，它会匹配其中一个分支。
如果它是用 `cons` 创建的，当初传给 `cons` 的两个参数就会被取回来（第一个被丢弃）。

```lean
example : maybeTail (.cons 1 (.cons 2 .nil)) = some (.cons 2 .nil) := rfl
example : maybeTail (MyList.nil : MyList Nat) = none := rfl
```

更复杂的和类型在 C++ 里用多态的类层次来实现。一族拥有共同祖先的类，可以理解为一个变体类型，其中虚函数表（vtable）充当了隐藏的标签。
在 Haskell 里通过对构造子做模式匹配、再调用相应代码来完成的事情，在 C++ 里是通过根据 vtable 指针分派虚函数调用来完成的。

::: tip Rust 视角：`dyn Trait` 也是一个和类型
Rust 里对应的是 trait 对象：`Box<dyn Shape>` 是一个胖指针，一半指向数据，一半指向 vtable。
vtable 指针就是那个隐藏的“标签”，告诉你这个值“其实是哪一种”。
同一个问题因此在 Rust 里有两种解法：**封闭**的 `enum` + `match`（像 Lean 的 `inductive`），
或者**开放**的 `trait` + `dyn`（像 C++ 的类层次）。这两种解法的取舍，正是本章挑战 2~4 要讨论的“表达式问题”。
:::

在 C++ 里你很少会看到把 `union` 用作和类型，因为对 union 里能放什么有严格的限制。
你甚至不能把 `std::string` 放进 union，因为它有拷贝构造函数。

::: tip Rust 视角：Rust 的 `union` 也一样别扭
Rust 也有 `union`，限制几乎一样：字段必须是 `Copy` 的，或者包在 `ManuallyDrop` 里（因为编译器不知道该析构哪个字段）；
而且读取字段是 `unsafe` 的——union 没有标签，编译器不知道里面现在装的是什么。
下面这样写编译不过：

```rust no-check
union Slot {
    n: u32,
    s: String, // 错误：union 的字段不能有析构函数（须为 Copy 或 ManuallyDrop<T>）
}
```

必须写成：

```rust
use std::mem::ManuallyDrop;

union Slot {
    n: u32,
    s: ManuallyDrop<String>,
}
```

所以 Rust 程序员也几乎从不手写 union，`enum`——带标签的联合体——才是日常。
:::

## 类型代数

单独来看，积类型与和类型已经可以用来定义各种有用的数据结构，但真正的威力来自把两者结合起来。
我们又一次在借助复合的力量。

来总结一下目前的发现。我们已经看到，类型系统底下有两种可交换的幺半结构：一种是和类型，以 `Empty` 为中性元；
另一种是积类型，以单位类型 `Unit` 为中性元。我们想把它们类比为加法和乘法。在这个类比中，`Empty` 对应零，`Unit` 对应一。

来看看这个类比能延伸多远。比如，乘以零会得到零吗？换句话说，一个分量是 `Empty` 的积类型，同构于 `Empty` 吗？
例如，能不能造出一个 `Int` 和 `Empty` 的序对？

要造一个序对，你需要两个值。整数随手就能找一个，可是 `Empty` 类型的值一个都没有。
因此，对任意类型 `α`，类型 `α × Empty` 是无人居住的——没有值——所以它等价于 `Empty`。换句话说，$a \times 0 = 0$。

```lean
def prodEmpty (α : Type) : α × Empty ≅ Empty where
  to p     := nomatch p.2   -- p.2 : Empty，不可能存在
  inv e    := nomatch e
  inv_to p := nomatch p.2
  to_inv e := nomatch e
```

另一条把加法和乘法联系在一起的性质是分配律：

$$a \times (b + c) = a \times b + a \times c$$

它对积类型与和类型也成立吗？成立——照例是在同构意义下。左边对应的类型是：

```lean no-check
α × (β ⊕ γ)
```

右边对应的类型是：

```lean no-check
(α × β) ⊕ (α × γ)
```

下面是一个方向的转换函数：

```lean
def prodToSum {α β γ : Type} : α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
  | (x, e) =>
    match e with
    | .inl y => .inl (x, y)
    | .inr z => .inr (x, z)
```

这是反方向的：

```lean
def sumToProd {α β γ : Type} : (α × β) ⊕ (α × γ) → α × (β ⊕ γ)
  | e =>
    match e with
    | .inl (x, y) => (x, .inl y)
    | .inr (x, z) => (x, .inr z)
```

`match … with` 子句用于在函数内部做模式匹配（它对应 Haskell 的 `case … of`，也就是 Rust 的 `match`）。
每个模式后面跟一个箭头 `=>` 和模式匹配成功时要求值的表达式。例如，如果你用下面这个值调用 `prodToSum`：

```lean
def prod1 : Int × (String ⊕ Float) := (2, .inl "Hi!")
```

`match e with` 中的 `e` 就等于 `.inl "Hi!"`。它会匹配模式 `.inl y`，用 `"Hi!"` 替换 `y`。
由于 `x` 已经匹配到了 `2`，`match` 子句——也就是整个函数——的结果将是 `.inl (2, "Hi!")`，正如所料。
Lean 可以直接验证这个推演：

```lean
example : prodToSum prod1 = .inl (2, "Hi!") := rfl
```

原书在这里说：“我不打算证明这两个函数互为逆，但只要你想一想，它们必然如此！它们只是在平凡地把两个数据结构的内容重新打包。
数据还是那份数据，只是格式不同。”在 Lean 里，“想一想”可以换成“证一证”，而且证明短得惊人：

```lean
def distrib (α β γ : Type) : α × (β ⊕ γ) ≅ (α × β) ⊕ (α × γ) where
  to     := prodToSum
  inv    := sumToProd
  inv_to := by
    intro ⟨x, e⟩
    cases e <;> rfl     -- e 要么是 inl，要么是 inr；两种情况都按定义算完即可
  to_inv := by
    intro s
    rcases s with ⟨x, y⟩ | ⟨x, z⟩ <;> rfl
```

证明这么短，恰恰印证了原书的直觉：这两个函数只是“重新打包”，所以每种情况下按定义展开就能直接看出来回到了原处。

数学家给这样两个交织在一起的幺半群起了个名字：**半环**（semiring）。它不是完整的**环**（ring），因为我们无法定义类型的减法。
所以半环有时也被叫作 **rig**，这是个文字游戏：“ring without an *n*”——少了 *n*（negative，负元）的 ring。
不过撇开这一点，把关于（比如）自然数——它们构成一个 rig——的命题翻译成关于类型的命题，可以让我们收获颇丰。
下面是一张翻译表，列出了一些有意思的条目：

| 数 | 类型（Lean） |
|---|---|
| $0$ | `Empty` |
| $1$ | `Unit` |
| $a + b$ | `α ⊕ β`，即 `inductive Sum α β \| inl : α → … \| inr : β → …` |
| $a \times b$ | `α × β`，或 `inductive Pair α β \| P : α → β → Pair α β` |
| $2 = 1 + 1$ | `inductive Bool \| false \| true` |
| $1 + a$ | `inductive Option α \| none \| some : α → Option α` |

::: info 数学小课堂：半环
一个**半环**是一个集合，配上两种运算 $+$ 和 $\times$，满足：

- $+$ 有结合律、交换律，有单位元 $0$（$a + 0 = a$）；
- $\times$ 有结合律，有单位元 $1$（$a \times 1 = a$）；
- 乘法对加法有分配律：$a \times (b + c) = a \times b + a \times c$；
- 零乘任何数得零：$a \times 0 = 0$。

自然数 $\{0, 1, 2, \dots\}$ 就是最典型的半环。它缺的是**减法**：$3 - 5$ 不是自然数。整数 $\mathbb{Z}$ 才是“环”。

本章我们已经在 Lean 里把类型的这些定律逐条证明了一遍（全部是在同构意义下）：

| 定律 | Lean 中的证明 |
|---|---|
| $a \times b = b \times a$ | `prodComm` |
| $(a \times b) \times c = a \times (b \times c)$ | `prodAssoc` |
| $a \times 1 = a$，$1 \times a = a$ | `prodUnit`、`unitProd` |
| $a + b = b + a$ | `sumComm` |
| $(a + b) + c = a + (b + c)$ | `sumAssoc` |
| $a + 0 = a$ | `sumEmpty` |
| $a \times 0 = 0$ | `prodEmpty` |
| $a \times (b + c) = a \times b + a \times c$ | `distrib` |
| $2 = 1 + 1$ | `boolIso` |
:::

“类型代数”这个名字可不是比喻。对于有限类型，把每个类型换成它的元素个数，$\times$、$+$ 就真的变成了数的乘法和加法。
在下面的计算器里亲手试一试：选两个小类型和一种构造方式，看看构造出来的类型到底有哪些元素。
（$\to$ 是函数类型，我们会在[第 1.9 章](/part1/09-function-types)正式讨论它；这里先剧透一下：它对应的是**乘方**。）

<div><Ch1_6TypeAlgebra /></div>

::: details 补充：让 Lean 自己数一数
我们也可以让 Lean 来数元素。定义一个类型类 `Enum`，它为一个类型列出全部元素；
再为积与和给出实例——积的元素是“每个 `a` 配每个 `b`”，和的元素是“左边全部 + 右边全部”：

```lean
class Enum (α : Type) where
  elems : List α

instance : Enum Empty    := ⟨[]⟩
instance : Enum Unit     := ⟨[()]⟩
instance : Enum Bool     := ⟨[false, true]⟩
instance : Enum (Fin 3)  := ⟨[0, 1, 2]⟩

instance {α β : Type} [Enum α] [Enum β] : Enum (α × β) :=
  ⟨(Enum.elems : List α).flatMap fun a => (Enum.elems : List β).map fun b => (a, b)⟩

instance {α β : Type} [Enum α] [Enum β] : Enum (α ⊕ β) :=
  ⟨(Enum.elems : List α).map Sum.inl ++ (Enum.elems : List β).map Sum.inr⟩

def card (α : Type) [Enum α] : Nat := (Enum.elems : List α).length

example : card (Bool × Fin 3) = 6 := rfl   -- 2 × 3 = 6
example : card (Bool ⊕ Fin 3) = 5 := rfl   -- 2 + 3 = 5
example : card (Fin 3 × Empty) = 0 := rfl  -- a × 0 = 0
example : card (Fin 3 ⊕ Empty) = 3 := rfl  -- a + 0 = a
-- 分配律：两边元素个数相同
example : card (Bool × (Unit ⊕ Fin 3)) = card (Bool × Unit ⊕ Bool × Fin 3) := rfl
```

`Fin 3` 是“小于 3 的自然数”组成的类型，恰好有 0、1、2 三个元素。
`[Enum α]` 是**实例参数**：调用者不需要手动传入，Lean 会自动去找 `Enum α` 的实例（相当于 Rust 的 `T: Enum` 约束）。

不过要注意：元素个数相等只是同构的**必要**条件的一个影子。对有限类型而言，个数相等确实意味着同构，
但个数说明不了**是哪个**同构——而本章前面的 `≅` 证明给出的正是那个具体的、“自然”的同构。
:::

列表类型很有意思，因为它被定义为一个方程的解。我们要定义的类型出现在方程两边：

```lean no-check
inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α
```

如果我们照常做替换，并把 `MyList α` 换成 `x`，就得到方程：

```
  x = 1 + a * x
```

我们没法用传统的代数方法解这个方程，因为类型不能相减、也不能相除。但我们可以尝试一连串的代入：
不断把右边的 `x` 替换成 `(1 + a*x)`，并使用分配律。这就得到下面的级数：

```
  x = 1 + a*x
  x = 1 + a*(1 + a*x) = 1 + a + a*a*x
  x = 1 + a + a*a*(1 + a*x) = 1 + a + a*a + a*a*a*x
  ...
  x = 1 + a + a*a + a*a*a + a*a*a*a...
```

最后我们得到一个无穷的积（元组）之和，可以这样解读：一个列表要么是空的，`1`；要么是单个元素，`a`；
要么是一个序对，`a*a`；要么是一个三元组，`a*a*a`；等等……嗯，这恰恰就是列表——一串 `a`！

方程 $x = 1 + a \times x$ 本身，在 Lean 里同样是一个可以证明的同构：

```lean
def listIso (α : Type) : List α ≅ Unit ⊕ (α × List α) where
  to
    | []      => .inl ()
    | x :: xs => .inr (x, xs)
  inv
    | .inl ()       => []
    | .inr (x, xs)  => x :: xs
  inv_to := by intro xs; cases xs <;> rfl
  to_inv := by intro s; rcases s with ⟨⟩ | ⟨x, xs⟩ <;> rfl
```

::: warning 易错点：“解方程”是个启发，不是定义
满足 $x \cong 1 + a \times x$ 的类型不止一个。比如“可能无限长的列表”（Haskell 的惰性列表）也满足它。
Lean 的 `inductive` 选的是其中**最小**的那个解：只包含用有限次 `nil`/`cons` 搭出来的值，所以 Lean 的列表一定是有限的。
“最小解”与“最大解”的区别，会在第三部分讲 F-代数的始代数与终余代数时再精确地回来。
:::

关于列表还有很多内容，学完函子和不动点之后，我们会再回到它和其他递归数据结构上来。

用符号变量解方程——这就是代数！这也正是这些类型得名的原因：**代数数据类型**（algebraic data type）。

最后，我得提一下类型代数的一个非常重要的解释。注意，两个类型 `α` 和 `β` 的积必须**同时**包含一个 `α` 类型的值**和**一个 `β` 类型的值，
这意味着两个类型都必须有居民。而两个类型的和只需包含一个 `α` 类型的值**或**一个 `β` 类型的值，所以只要其中一个有居民就够了。
逻辑上的**与**和**或**也构成一个半环，它同样可以映射到类型论中：

| 逻辑 | 类型 | Lean 中的命题版本 |
|---|---|---|
| $\mathit{false}$ | `Empty` | `False` |
| $\mathit{true}$ | `Unit` | `True` |
| $a \mathbin{\Vert} b$ | `α ⊕ β` | `a ∨ b`（`Or`） |
| $a \mathbin{\&\&} b$ | `α × β` | `a ∧ b`（`And`） |

这个类比还可以更深入，它是逻辑与类型论之间的 **Curry–Howard 同构**的基础。我们会在讨论函数类型时回到这个话题。

::: tip Lean 深入：Curry–Howard 在 Lean 里是字面意思
上表第三列不是比喻。Lean 里命题（`Prop`）就是一种特殊的类型，证明就是这种类型的值。
核心库里 `And` 的定义和 `Prod` 几乎逐字相同（一个有两个字段 `left`、`right` 的结构体），
`Or` 的定义和 `Sum` 几乎逐字相同（两个构造子 `inl`、`inr`），`False` 和 `Empty` 一样没有构造子，
`True` 和 `Unit` 一样只有一个构造子。于是“构造一个序对”和“证明一个合取”用的是同一套语法：

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩      -- 像构造序对
example (p q : Prop) (hp : p) : p ∨ q := Or.inl hp              -- 像 Sum.inl
example (p : Prop) (h : False) : p := nomatch h                 -- 像 Empty 的 nomatch
```

你在本书里写的每一个 `≅` 证明，用的都是这套“命题即类型、证明即程序”的机制。
:::

## 挑战

1. 证明 `Option α` 与 `Unit ⊕ α`（Haskell 的 `Either () a`）之间的同构。
2. 下面是 Lean 中定义的一个和类型：

   ```lean
   def pi : Float := 3.141592653589793   -- Lean 核心库没有内置 π，自己定义一个

   inductive Shape where
     | circle : Float → Shape
     | rect   : Float → Float → Shape
   ```

   当我们想定义一个作用在 `Shape` 上的函数（比如 `area`）时，就对两个构造子做模式匹配：

   ```lean
   def Shape.area : Shape → Float
     | .circle r => pi * r * r
     | .rect d h => d * h
   ```

   请用 Rust 把 `Shape` 实现成一个 trait，并创建两个结构体 `Circle` 和 `Rect`，把 `area` 实现为 trait 方法（也就是通过 vtable 动态分派的“虚函数”）。
   （原书要求用 C++ 或 Java 的接口与类。）
3. 接着上一题：我们可以轻松地添加一个新函数 `circ`，计算 `Shape` 的周长。完全不需要动 `Shape` 的定义：

   ```lean
   def Shape.circ : Shape → Float
     | .circle r => 2.0 * pi * r
     | .rect d h => 2.0 * (d + h)
   ```

   把 `circ` 加到你的 Rust 实现里。你不得不改动原有代码的哪些部分？
4. 再进一步：给 `Shape` 添加一种新形状 `Square`，并做出所有必要的修改。在 Lean 里和在 Rust（trait 版本）里，你分别要改哪些代码？
   （即使你不是 Lean 程序员，需要做的修改也应该相当明显。）
5. 证明 $a + a = 2 \times a$ 对类型成立（在同构意义下）。记住，根据我们的翻译表，$2$ 对应 `Bool`。

::: details 参考答案
**1.** 两个方向各按构造子一一对应：`none ↔ inl ()`，`some a ↔ inr a`。

```lean
def optionIso (α : Type) : Option α ≅ Unit ⊕ α where
  to
    | none   => .inl ()
    | some a => .inr a
  inv
    | .inl () => none
    | .inr a  => some a
  inv_to := by intro o; cases o <;> rfl
  to_inv := by intro s; rcases s with ⟨⟩ | a <;> rfl
```

**2.** 用 trait 对象实现，`area` 是通过 vtable 动态分派的方法：

```rust
use std::f32::consts::PI;

trait Shape {
    fn area(&self) -> f32;
}

struct Circle {
    r: f32,
}

struct Rect {
    d: f32,
    h: f32,
}

impl Shape for Circle {
    fn area(&self) -> f32 {
        PI * self.r * self.r
    }
}

impl Shape for Rect {
    fn area(&self) -> f32 {
        self.d * self.h
    }
}

fn total_area(shapes: &[Box<dyn Shape>]) -> f32 {
    shapes.iter().map(|s| s.area()).sum()
}
```

**3.** 要加 `circ`，必须修改 trait `Shape` 的定义（加一个方法），**并且**修改**每一个**已有的 `impl`：

```rust
use std::f32::consts::PI;

trait Shape {
    fn area(&self) -> f32;
    fn circ(&self) -> f32; // 改动 1：接口本身
}

struct Circle {
    r: f32,
}

struct Rect {
    d: f32,
    h: f32,
}

impl Shape for Circle {
    fn area(&self) -> f32 {
        PI * self.r * self.r
    }
    fn circ(&self) -> f32 { // 改动 2：每个已有的实现
        2.0 * PI * self.r
    }
}

impl Shape for Rect {
    fn area(&self) -> f32 {
        self.d * self.h
    }
    fn circ(&self) -> f32 { // 改动 3
        2.0 * (self.d + self.h)
    }
}
```

如果 `Circle` 和 `Rect` 分布在不同的 crate 里、由不同的人维护，这就成了一次“破坏性变更”。
（Rust 有个缓解办法：另起一个新 trait `trait Circ { fn circ(&self) -> f32; }` 并为已有类型实现它，这样旧 trait 不用改；
但 `Box<dyn Shape>` 里的值并不能直接调用 `circ`，你还得把 trait 对象的类型改成同时要求两个 trait。）
而在 Lean 的 `inductive` 版本里，正如题目所示，加函数只需**新增**一个 `def Shape.circ`，一行旧代码都不用动。

**4.** 添加 `Square` 时，情况正好反过来。

在 Lean 里，必须修改 `Shape` 的定义，并修改**每一个**对 `Shape` 做模式匹配的函数：

```lean
namespace WithSquare

inductive Shape where
  | circle : Float → Shape
  | rect   : Float → Float → Shape
  | square : Float → Shape          -- 改动 1：类型定义

def Shape.area : Shape → Float
  | .circle r => pi * r * r
  | .rect d h => d * h
  | .square d => d * d              -- 改动 2：每个已有的函数

def Shape.circ : Shape → Float
  | .circle r => 2.0 * pi * r
  | .rect d h => 2.0 * (d + h)
  | .square d => 4.0 * d            -- 改动 3

end WithSquare
```

好消息是：如果你忘了改某个函数，Lean 会报“模式匹配不完整”的错误（`missing cases`），绝不会悄悄漏掉。
（Rust 的 `enum` + `match` 版本也一样。）

而在 Rust 的 trait 版本里，加一种形状只需**新增**代码，原有代码一行都不用动：

```rust
use std::f32::consts::PI;

trait Shape {
    fn area(&self) -> f32;
    fn circ(&self) -> f32;
}

// ……Circle 与 Rect 的定义和实现保持原样……

struct Square {
    d: f32,
}

impl Shape for Square {
    fn area(&self) -> f32 {
        self.d * self.d
    }
    fn circ(&self) -> f32 {
        4.0 * self.d
    }
}
```

这就是著名的**表达式问题**（expression problem）：

| | 加一个新**操作**（`circ`） | 加一个新**情形**（`Square`） |
|---|---|---|
| 和类型 + 模式匹配（Lean `inductive`、Rust `enum`） | 容易：只新增一个函数 | 难：改类型定义和所有函数 |
| 接口 + 虚函数（Rust `trait` + `dyn`、C++/Java 类层次） | 难：改接口和所有实现 | 容易：只新增一个类型 |

两种组织方式各有所长，没有哪一种在两个方向上都轻松。在 Lean 和 Rust 里，你都可以根据“将来更可能加操作还是加情形”来选择。

**5.** 构造 `α ⊕ α ≅ Bool × α`：`Bool` 那一位记住“值来自左边还是右边”。

```lean
def twoTimes (α : Type) : α ⊕ α ≅ Bool × α where
  to
    | .inl a => (false, a)
    | .inr a => (true, a)
  inv
    | (false, a) => .inl a
    | (true, a)  => .inr a
  inv_to := by intro s; cases s <;> rfl
  to_inv := by intro ⟨b, a⟩; cases b <;> rfl
```

也可以不直接写，而是用已经证明过的同构“拼”出来：$a + a \cong 1 \times a + 1 \times a \cong (1 + 1) \times a \cong 2 \times a$。
每一步都是本章的一个定理（单位律、分配律、`boolIso`），再用 `TypeIso.trans` 串起来。这就是“类型代数”的意思：
用代数定律一步步变形，每一步都有一个可执行的同构作为见证。
:::

## 本章小结

- 积类型 `α × β`（序对、`structure`、Rust `struct`/元组）和和类型 `α ⊕ β`（`inductive`、Rust `enum`）是构造数据结构的两块基本积木。
- 两个类型**同构**，意思是有一对互逆的函数在它们之间来回转换；在 Lean 里我们把它写成结构体 `TypeIso`（`α ≅ β`），连同“互逆”的证明一起打包。
- 积在同构意义下满足交换律、结合律，单位元是 `Unit`；和也满足交换律、结合律，单位元是 `Empty`。这使 $\mathbf{Set}$ 成为（两种意义下的）幺半范畴。
- 记录（`structure`）就是字段带名字的积类型；字段名同时是访问函数，`e.symbol` 是 `Element.symbol e` 的语法糖。
- `Bool = Unit ⊕ Unit`（$2 = 1 + 1$），`Option α = Unit ⊕ α`（$1 + a$），`List α = Unit ⊕ α × List α`（$x = 1 + a x$）。
- 类型构成一个**半环**（rig）：有加法、乘法、零、一、分配律、$a \times 0 = 0$，但没有减法。对有限类型，把类型换成元素个数，类型代数就变成了自然数的算术。
- Lean 的值不可变，所以构造可逆，模式匹配就是“把构造倒着做一遍”。
- 和类型（封闭、易加操作）与接口/trait 对象（开放、易加情形）的取舍，就是表达式问题。
- 逻辑的与/或/真/假也构成半环，并对应积/和/`Unit`/`Empty`——这是 Curry–Howard 同构的雏形，而在 Lean 里它是字面事实。
