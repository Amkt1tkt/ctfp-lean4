# 1.5 积与余积

```lean hidden
universe u v

namespace CTFP

class Category (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id : (a : Obj) → Hom a a
  comp : {a b c : Obj} → Hom b c → Hom a b → Hom a c
  id_comp : ∀ {a b : Obj} (f : Hom a b), comp (id b) f = f := by intros; rfl
  comp_id : ∀ {a b : Obj} (f : Hom a b), comp f (id a) = f := by intros; rfl
  assoc : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp h (comp g f) = comp (comp h g) f := by intros; rfl

infixr:10 " ⟶ " => Category.Hom
infixr:80 " ⊚ " => Category.comp
notation "𝟙" => Category.id

open Category

instance typeCategory : Category (Type u) where
  Hom a b := a → b
  id _ := fun x => x
  comp g f := fun x => g (f x)

end CTFP

open CTFP
```

古希腊剧作家欧里庇得斯说过：“一个人，就像他惯常结交的那些人。”我们由自己的关系所定义。这句话在范畴论里比在任何地方都更正确。如果想在一个范畴里把某个特定对象挑出来，我们唯一能做的，就是描述它与其他对象（以及它自己）之间的关系模式。而这些关系，是由态射定义的。

范畴论里有一种常见的构造，叫做**泛构造**（universal construction），它通过对象之间的关系来定义对象。一种做法是：挑一个**模式**（pattern）——一个由对象和态射构成的特定形状——然后在范畴里寻找它的所有出现。如果这个模式足够常见、范畴又足够大，你多半会得到成堆成堆的匹配。诀窍在于在这些匹配之间建立某种**排名**，然后挑出可以被认为是“最佳匹配”的那一个。

这个过程让人想起我们做网页搜索的方式。一个查询就像一个模式。一个很宽泛的查询会给你很高的**召回率**（recall）：大量的结果，有些相关，有些不相关。为了剔除不相关的结果，你会细化查询，这提高了它的**精确率**（precision）。最后，搜索引擎会给结果排名，运气好的话，你真正想要的那一条就排在列表最顶端。

## 始对象

最简单的形状是单个对象。显然，一个范畴里有多少个对象，这个形状就有多少个实例。选择实在太多了。我们需要建立某种排名，试着找出位于这个等级体系顶端的那个对象。我们手头唯一的工具就是态射。如果你把态射想象成箭头，那么可能存在一股从范畴的一端流向另一端的“净箭头流”。这在有序的范畴里确实如此，比如偏序集。我们可以推广“对象之间谁先谁后”的概念：如果有一个箭头（一个态射）从对象 $a$ 指向对象 $b$，就说 $a$ 比 $b$“更始”（more initial）。然后，我们把**那个**始对象定义为：有箭头指向所有其他对象的对象。显然，不能保证这样的对象一定存在，这没关系。更大的问题是这样的对象可能太多了：召回率不错，但精确率不够。解决办法是从有序范畴那里得到启发——它们在任意两个对象之间最多只允许一个箭头：“小于或等于”另一个对象的方式只有一种。这就引出了始对象的定义：

> **始对象**（initial object）是这样一个对象：从它出发，到范畴中的任何一个对象，都**有且只有一个**态射。

![始对象](/img/1.5/initial.jpg "始对象：从它出发到每个对象都恰好有一个箭头。")

::: info 数学小课堂：“有且只有一个”
“有且只有一个”（数学家写作 $\exists!$，读作“存在唯一”）其实是**两句话**：

1. **存在**：至少有一个。
2. **唯一**：如果有两个，那它们其实是同一个——也就是说，任取两个满足条件的东西 $f$ 和 $g$，必有 $f = g$。

所以要证明“从 $i$ 到 $a$ 有且只有一个态射”，你得做两件事：先**造出**一个态射，再证明**任意两个**这样的态射都相等。
本章会反复用到这个套路。在 Lean 里，第一件事是写一个定义，第二件事是证一个形如 `∀ f g, f = g` 的定理。
:::

不过，即使这样，也不能保证始对象（如果存在的话）是唯一的。但它保证了退而求其次的东西：**在同构意义下唯一**（unique up to isomorphism）。同构在范畴论里非常重要，我很快就会讲到它。现在我们先约定：在同构意义下唯一，就足以让我们在定义里理直气壮地说“**那个**始对象”。

来看几个例子。在一个偏序集（partially ordered set，常简称 **poset**）里，始对象就是它的最小元。有些偏序集没有始对象——比如全体整数（正的和负的）配上“小于等于”关系作为态射：不存在比所有整数都小的整数。

在集合与函数的范畴里，始对象是空集。回忆一下，空集对应于 Lean 的类型 `Empty`（Haskell 里叫 `Void`；Rust 里对应没有任何变体的枚举 `enum Void {}`，或者实验性的 never 类型 `!`），而从 `Empty` 到任何其他类型的那个唯一的多态函数，Haskell 里叫做 `absurd`：

```lean
def absurd' {α : Type} : Empty → α :=
  fun e => nomatch e
```

`nomatch e` 的意思是：“对 `e` 做模式匹配，但一个分支都不写”。因为 `Empty` 没有任何构造子，一个分支都不需要写，Lean 也就心满意足地接受了这个函数：它永远不可能被调用，因为你根本造不出一个 `Empty` 类型的值来调用它。

::: tip Lean 深入：核心库里的 `Empty.elim` 与 `absurd`
Lean 核心库已经提供了这个函数，名叫 `Empty.elim : Empty → C`。核心库里**也**有一个叫 `absurd` 的东西，
但它是逻辑层面的：`absurd : a → ¬a → b`，意思是“同时拥有命题 `a` 及其否定，就能推出任何东西”。
两者其实是同一个思想（从“不可能”中可以推出一切，拉丁文叫 *ex falso quodlibet*），只是一个在类型层面，一个在命题层面。
所以我们给自己的版本加了一撇，叫 `absurd'`，以免和核心库冲突。
:::

正是这一族态射，使得 `Empty` 成为类型范畴中的始对象。用 Lean，我们可以把“唯一”这一半也证出来：从 `Empty` 出发的任意两个函数都相等。

```lean
theorem empty_unique {α : Type} (f g : Empty → α) : f = g :=
  funext (fun e => nomatch e)   -- 要对每个 e : Empty 证明 f e = g e，但这样的 e 根本不存在

-- 核心库的 Empty.elim 和我们的 absurd' 是同一个函数
example {α : Type} : (absurd' : Empty → α) = Empty.elim := empty_unique _ _
```

这个证明值得多看一眼：`funext` 把“两个函数相等”化为“对每个输入，输出相等”；而对 `Empty` 来说，“每个输入”是一个空洞的要求——没有输入需要检查。数学家管这叫**空真**（vacuous truth）：“我口袋里的每一枚金币都是假的”——如果我口袋里根本没有金币，这句话就是真的。

## 终对象

我们继续使用单个对象的模式，但改变一下给对象排名的方式。如果有一个态射从 $b$ 指向 $a$（注意方向反过来了），就说对象 $a$ 比 $b$“更终”（more terminal）。我们要找的，是一个比范畴中任何其他对象都更终的对象。同样，我们坚持唯一性：

> **终对象**（terminal object）是这样一个对象：从范畴中的任何一个对象出发，到它都**有且只有一个**态射。

![终对象](/img/1.5/final.jpg "终对象：从每个对象出发到它都恰好有一个箭头。")

同样，终对象在同构意义下是唯一的，我马上就会证明这一点。但先看几个例子。在偏序集里，终对象（如果存在的话）就是最大元。在集合范畴里，终对象是单元素集。我们已经讨论过单元素集——它们对应 Lean 里的 `Unit` 类型（Rust 里的 `()`）。这是一个只有一个值的类型，那个值也写作 `()`。我们也已经确认过：从任何类型到 `Unit`，有且只有一个纯函数：

```lean
def unit {α : Type} : α → Unit :=
  fun _ => ()
```

所以终对象的所有条件都满足了。用 Lean 把“只有一个”证出来更是轻而易举：

```lean
theorem unit_unique {α : Type} (f g : α → Unit) : f = g :=
  funext (fun _ => rfl)   -- f x 和 g x 都是 Unit 的值，而 Unit 只有一个值
```

::: tip Lean 深入：为什么这里 `rfl` 就够了？
`rfl` 证明的是“两边在定义上相等”。`f x` 和 `g x` 是两个我们一无所知的 `Unit` 值，凭什么定义上相等？
因为 Lean 的类型检查器内置了**结构体的 eta 规则**：`Unit` 是一个没有字段的结构体，它的任何两个值都被视为定义上相等。
在 Rust 里你也有同样的直觉：类型 `()` 的值不携带任何信息，两个 `()` 当然是一样的。
:::

注意，在这个例子里，唯一性条件至关重要。因为还有别的集合（实际上，除了空集以外的**所有**集合）都有从每个集合射入的态射。比如，对每个类型，都有一个取布尔值的函数（一个谓词）：

```lean
def yes {α : Type} : α → Bool :=
  fun _ => true
```

但 `Bool` 不是终对象。从每个类型出发，至少还有另一个取 `Bool` 值的函数（`Empty` 除外——对它来说，两个函数都等于 `absurd'`）：

```lean
def no {α : Type} : α → Bool :=
  fun _ => false

-- 对 Nat 而言，yes 和 no 是两个不同的函数：所以 Bool 不是终对象
example : (yes : Nat → Bool) ≠ no := by
  intro h                    -- 假设 yes = no
  have := congrFun h 0       -- 那么 yes 0 = no 0，即 true = false
  simp [yes, no] at this     -- 这是荒谬的

-- 但对 Empty 而言，yes 和 no 是同一个函数
example : (yes : Empty → Bool) = no := empty_unique _ _
```

（`congrFun h 0` 把函数等式 `h : f = g` 变成具体输入上的等式 `f 0 = g 0`；`simp ... at this` 把假设 `this` 化简成 `False`，从而结束证明。）

坚持唯一性给了我们恰到好处的精确率，把终对象的定义收窄到了一个类型上。

下面这个小组件把“有且只有一个”变成了一张表。在集合范畴里，从集合 $a$ 到集合 $b$ 的函数恰好有 $|b|^{|a|}$ 个（每个输入都有 $|b|$ 种去处）。始对象那一**行**全是 1，终对象那一**列**全是 1。留意 `Bool` 那一列：没有一个格子是 0，所以从每个集合出发都有箭头射向 `Bool`——但除了来自空集的那一格，其余的数字是 2、4、8……唯一性不满足。

<div><Ch1_5InitialTerminal /></div>

现在我们把始对象和终对象的定义，用全书统一的 `CTFP.Category` 写成 Lean 的结构体，使它们对**任何**范畴都有意义：

```lean
/-- `i` 是始对象：到每个对象 `a` 都有一个态射 `into a`，并且任何从 `i` 到 `a` 的态射都等于它。 -/
structure IsInitial {C : Type u} [Category.{u, v} C] (i : C) where
  into : (a : C) → (i ⟶ a)
  uniq : ∀ {a : C} (f : i ⟶ a), f = into a

/-- `t` 是终对象：从每个对象 `a` 都有一个态射 `from_ a`，并且任何从 `a` 到 `t` 的态射都等于它。 -/
structure IsTerminal {C : Type u} [Category.{u, v} C] (t : C) where
  from_ : (a : C) → (a ⟶ t)
  uniq : ∀ {a : C} (f : a ⟶ t), f = from_ a

def emptyIsInitial : IsInitial (C := Type) Empty where
  into _ := absurd'
  uniq _ := empty_unique _ _

def unitIsTerminal : IsTerminal (C := Type) Unit where
  from_ _ := unit
  uniq _ := unit_unique _ _
```

注意这两个结构体的字段，恰好就是“有且只有一个”的两半：`into`/`from_` 负责“存在”，`uniq` 负责“唯一”。（字段名 `from_` 多了一个下划线，是因为 `from` 是 Lean 的关键字。）`(C := Type)` 是**具名参数**的写法：明确告诉 Lean“这里的范畴是 `Type`”。

## 对偶

你一定注意到了始对象和终对象定义之间的对称性：两者唯一的区别就是态射的方向。事实上，对任何范畴 $\mathcal{C}$，只要把所有箭头都反过来，就能定义出它的**对偶范畴**（opposite category，也叫反范畴）$\mathcal{C}^{op}$。只要同时重新定义复合，对偶范畴就自动满足一个范畴的全部要求。如果原来的态射 $f \colon a \to b$ 和 $g \colon b \to c$ 复合成 $h \colon a \to c$，$h = g \circ f$，那么反过来的态射 $f^{op} \colon b \to a$ 和 $g^{op} \colon c \to b$ 就复合成 $h^{op} \colon c \to a$，$h^{op} = f^{op} \circ g^{op}$。至于把恒等箭头反过来——（双关预警！）——那是个 no-op。（“no-op”是程序员说的“空操作”，而“op”恰好就是 opposite 的缩写：反过来的恒等箭头还是它自己。）

```diagram
A: (0, 0) "a"
B: (1.6, 0) "b"
C: (3.2, 0) "c"
f: A -> B "f"
g: B -> C "g"
h: A -> C "h = g \circ f" bend=-45 side=right
A2: (0, 1.7) "a"
B2: (1.6, 1.7) "b"
C2: (3.2, 1.7) "c"
fop: B2 -> A2 "f^{op}" side=left
gop: C2 -> B2 "g^{op}" side=left
hop: C2 -> A2 "h^{op} = f^{op} \circ g^{op}" bend=-45 side=right color=purple
path "原范畴：先 f 再 g": f g
path "对偶范畴：先 g^op 再 f^op": gop fop color=purple
caption: 上：原范畴 C 中的复合。下：对偶范畴 C^op 中，所有箭头都反了过来，复合的顺序也随之颠倒。
```

全书的公共前导（`lean/Prelude.lean`）里就有对偶范畴的定义。因为这是它第一次登场，我们把它完整展示出来，逐行看一遍：

```lean
namespace CTFP

/-- 对偶范畴 `Cᵒᵖ`：对象相同、箭头反转。 -/
def Op (C : Type u) : Type u := C

instance opCategory (C : Type u) [Category.{u, v} C] : Category.{u, v} (Op C) where
  Hom a b := @Category.Hom C _ b a
  id a := @Category.id C _ a
  comp g f := @Category.comp C _ _ _ _ f g
  id_comp f := @Category.comp_id C _ _ _ f
  comp_id f := @Category.id_comp C _ _ _ f
  assoc f g h := (@Category.assoc C _ _ _ _ _ h g f).symm

end CTFP
```

- `def Op (C : Type u) : Type u := C`：对偶范畴的**对象**和原范畴完全一样，所以 `Op C` 在定义上就等于 `C`。之所以要起一个新名字，原因和上一章 Writer 范畴的 `WriterObj` 一样：Lean 按对象的类型挑选范畴实例，`C` 已经有一个实例了，我们需要一个新名字来挂另一套箭头（Rust 的 newtype 模式）。这里用的是 `def` 而不是 `abbrev`，正是为了让 Lean **不要**自动把 `Op C` 看穿成 `C`——否则它又会去用 `C` 原来的实例。
- `Hom a b := @Category.Hom C _ b a`：对偶范畴中从 `a` 到 `b` 的箭头，就是原范畴中从 `b` 到 `a` 的箭头。注意 `b a` 的顺序被调换了——这一行就是“把箭头反过来”的全部内容。`@` 让我们显式地写出所有参数（包括通常隐式的范畴 `C` 和实例 `_`），以确保用的是原范畴 `C` 的 `Hom`。
- `id a := @Category.id C _ a`：恒等箭头原样照搬。这就是那个“no-op”。
- `comp g f := @Category.comp C _ _ _ _ f g`：对偶范畴中的“`g` 在 `f` 之后”，就是原范畴中的“`f` 在 `g` 之后”。参数顺序 `f g` 被调换了，这正是 $h^{op} = f^{op} \circ g^{op}$。
- 三条定律：对偶范畴的左单位律，就是原范畴的**右**单位律（`id_comp` 用 `comp_id` 来证，反之亦然）；结合律则是原范畴结合律的反向（`.symm` 把等式 `x = y` 翻成 `y = x`）。我们**不需要证明任何新东西**——对偶范畴的定律只不过是原范畴定律换了个角度看。

这正是“对偶范畴自动满足范畴的全部要求”这句话在 Lean 里的精确含义。

对偶是范畴的一个非常重要的性质，因为它让每一位从事范畴论研究的数学家的生产力翻了一倍。你想出的每一个构造，都有它的对偶构造；你证明的每一个定理，都附送一个免费的定理。对偶范畴中的构造常常冠以“余”（co-）字前缀，于是你有积与余积、单子与余单子、锥与余锥、极限与余极限，等等。不过，并没有“余余单子”（cocomonad）这种东西，因为把箭头反转两次，就回到了原样。

最后这句话在 Lean 里就是一个 `rfl`：

```lean
example (C : Type u) : Op (Op C) = C := rfl
```

由此可知，终对象就是对偶范畴里的始对象。在 Lean 里，这条“免费定理”的证明几乎什么都不用做——把字段原样搬过去就行：

```lean
/-- C 中的终对象，就是 Cᵒᵖ 中的始对象。 -/
def IsTerminal.op {C : Type u} [Category.{u, v} C] {t : C} (h : IsTerminal t) :
    IsInitial (C := Op C) t where
  into a := h.from_ a     -- Cᵒᵖ 中 t ⟶ a，就是 C 中 a ⟶ t
  uniq f := h.uniq f
```

## 同构

作为程序员，我们深知定义“相等”可不是一件简单的事。两个对象相等是什么意思？它们必须占据同一块内存（指针相等）吗？还是只要所有分量的值都相等就够了？一个复数用实部和虚部表示，另一个用模和辐角表示，这两个复数相等吗？你可能以为数学家早就把相等的含义搞清楚了，但他们并没有。他们同样面临多种互相竞争的相等定义：命题相等、内涵相等、外延相等，以及同伦类型论中作为“路径”的相等。然后还有更弱的同构的概念，以及再弱一些的等价的概念。

::: tip Rust 视角：好几种“相等”
Rust 程序员对“相等有好几种”再熟悉不过了：`std::ptr::eq(a, b)` 是指针相等；`a == b` 调用的是你自己实现的 `PartialEq`；
而 `Eq` trait 额外承诺这种相等满足自反性。Lean 里也有好几种：`a = b` 是**命题相等**（一个可以被证明的命题），
`a == b` 是 `BEq` 类型类给出的**布尔判断**（一个可以被计算的函数），而 `rfl` 能证明的是**定义相等**（两边算到底是同一个东西）。
我们证明函数相等时用的 `funext`，体现的正是**外延相等**：对每个输入给出相同输出的两个函数就是相等的。
:::

直觉上，同构的对象看起来是一样的——它们有相同的形状。这意味着一个对象的每一部分，都以一一对应的方式对应着另一个对象的某个部分。就我们的仪器所能分辨的而言，这两个对象是彼此的完美复制品。数学上，这意味着有一个从对象 $a$ 到对象 $b$ 的映射，也有一个从对象 $b$ 回到对象 $a$ 的映射，而且它们互为逆。在范畴论里，我们用态射来代替映射。一个**同构**（isomorphism）就是一个可逆的态射；或者说，是一对态射，其中一个是另一个的逆。

我们借助复合和恒等来理解“逆”：如果态射 $g$ 与态射 $f$ 的复合是恒等态射，那么 $g$ 就是 $f$ 的逆。这实际上是两个等式，因为两个态射有两种复合方式：

$$f \circ g = \mathrm{id} \qquad g \circ f = \mathrm{id}$$

在 Lean 里，我们把同构定义成一个结构体：它打包了两个方向的态射，以及这两个等式的证明：

```lean
/-- `a` 与 `b` 之间的同构：一对互逆的态射。 -/
structure Iso {C : Type u} [Category.{u, v} C] (a b : C) where
  hom : a ⟶ b
  inv : b ⟶ a
  inv_hom : inv ⊚ hom = 𝟙 a    -- 先去后回 = 原地不动
  hom_inv : hom ⊚ inv = 𝟙 b    -- 先回后去 = 原地不动
```

::: tip Lean 深入：把证明当作数据的一部分
在 Rust 里，你可以写 `struct Iso<A, B> { hom: fn(A) -> B, inv: fn(B) -> A }`，但没法在类型里要求“这两个函数互逆”——
那只能写在文档注释里，靠调用者自觉。Lean 的结构体可以有**证明字段**：`inv_hom` 的类型是一个命题，它的值是这个命题的证明。
想构造一个 `Iso`，你**必须**交出证明，否则编译不通过。这就是“把定律写进类型”的含义。
:::

一个最简单的例子：交换二元组的两个分量，是 `α × β` 与 `β × α` 之间的同构。在 `Type` 中，两条定律都是 `rfl`：

```lean
def swapIso (α β : Type) : Iso (C := Type) (α × β) (β × α) where
  hom := fun (a, b) => (b, a)
  inv := fun (b, a) => (a, b)
  inv_hom := rfl
  hom_inv := rfl
```

::: info 数学小课堂：同构 ≠ 相等
`Int × Bool` 和 `Bool × Int` 不是同一个类型——`(3, true)` 和 `(true, 3)` 写法都不一样。但它们**同构**：
它们之间有一对互逆的转换，信息一点不丢。就“能表达什么”而言，它们没有区别。

范畴论几乎从不问“两个对象是否相等”，只问“它们是否同构”。这就像我们说“两个 JSON 文档语义相同”，而不在乎字段的书写顺序。
:::

当我说始（终）对象在同构意义下唯一时，我的意思是：任意两个始（终）对象都是同构的。这其实很容易看出来。假设我们有两个始对象 $i_1$ 和 $i_2$。因为 $i_1$ 是始对象，所以从 $i_1$ 到 $i_2$ 有唯一的态射 $f$。同理，因为 $i_2$ 是始对象，所以从 $i_2$ 到 $i_1$ 有唯一的态射 $g$。这两个态射的复合是什么？

![始对象的唯一性](/img/1.5/uniqueness.jpg "这个图里的所有态射都是唯一的。")

复合 $g \circ f$ 一定是从 $i_1$ 到 $i_1$ 的态射。但 $i_1$ 是始对象，所以从 $i_1$ 到 $i_1$ 只能有一个态射。既然我们身处一个范畴，我们知道从 $i_1$ 到 $i_1$ 有一个恒等态射；既然只容得下一个，那就只能是它。因此 $g \circ f$ 等于恒等态射。类似地，$f \circ g$ 也必须等于恒等态射，因为从 $i_2$ 回到 $i_2$ 只能有一个态射。这就证明了 $f$ 和 $g$ 一定互逆。所以任意两个始对象都是同构的。

```diagram
I1: (0, 0) "i_1"
I2: (2.4, 0) "i_2"
f: I1 -> I2 "f" bend=22
g: I2 -> I1 "g" bend=22
id1: I1 -> I1 "\mathrm{id}_{i_1}" loop=left
id2: I2 -> I2 "\mathrm{id}_{i_2}" loop=right
path "g ∘ f：从 i₁ 出发绕一圈": f g
path "id：原地不动": id1 color=green
caption: 从 i₁ 到 i₁ 只能有一个态射，所以绕一圈 g ∘ f 和原地不动 id 必须是同一个箭头。
```

这段论证翻译成 Lean，几乎是逐句对应的：

```lean
/-- 任意两个始对象同构。 -/
def initialIso {C : Type u} [Category.{u, v} C] {i₁ i₂ : C}
    (h₁ : IsInitial i₁) (h₂ : IsInitial i₂) : Iso i₁ i₂ where
  hom := h₁.into i₂     -- f：i₁ 是始对象，所以有 i₁ ⟶ i₂
  inv := h₂.into i₁     -- g：i₂ 是始对象，所以有 i₂ ⟶ i₁
  -- g ∘ f 和 id 都是 i₁ ⟶ i₁，由唯一性，它们都等于 h₁.into i₁，所以相等
  inv_hom := by rw [h₁.uniq (h₂.into i₁ ⊚ h₁.into i₂), h₁.uniq (𝟙 i₁)]
  -- 同理，f ∘ g 和 id 都是 i₂ ⟶ i₂
  hom_inv := by rw [h₂.uniq (h₁.into i₂ ⊚ h₂.into i₁), h₂.uniq (𝟙 i₂)]
```

（`rw [e]` 用等式 `e : x = y` 把目标中的 `x` 改写成 `y`。这里先把 `g ∘ f` 改写成“那个唯一的态射”，再把 `id` 也改写成它，目标就变成了 `x = x`，`rw` 会自动用 `rfl` 收尾。）

请注意，在这个证明里我们用到了“从始对象到它自身的态射是唯一的”这一点。没有它，我们就证明不了“在同构意义下”这一部分。但为什么我们还需要 $f$ 和 $g$ 的唯一性呢？因为始对象不仅在同构意义下唯一，而且是在**唯一的**同构意义下唯一。原则上，两个对象之间可以有不止一个同构，但这里并非如此。这种“在唯一同构意义下唯一”，是所有泛构造的重要性质。

```lean
/-- 而且这个同构是唯一的：i₁ 与 i₂ 之间任何一个同构，其正向态射都和上面那个相同。 -/
theorem initialIso_unique {C : Type u} [Category.{u, v} C] {i₁ i₂ : C}
    (h₁ : IsInitial i₁) (h₂ : IsInitial i₂) (e : Iso i₁ i₂) :
    e.hom = (initialIso h₁ h₂).hom :=
  h₁.uniq e.hom
```

## 积

下一个泛构造是积。我们知道两个集合的笛卡尔积是什么：它是由二元组构成的集合。但积集合与它的两个组成集合之间，是由什么模式联系起来的呢？如果能搞清楚这一点，我们就能把它推广到其他范畴。

我们只能说：有两个函数——**投影**（projection）——从积分别通向两个组成部分。在 Lean 里，这两个函数叫 `Prod.fst` 和 `Prod.snd`，它们分别取出二元组的第一个和第二个分量。我们自己写一遍（放进命名空间以免和核心库冲突）：

```lean
namespace MyDefs

def fst {α β : Type} : α × β → α
  | (x, y) => x

def snd {α β : Type} : α × β → β
  | (x, y) => y

end MyDefs
```

这里的函数是通过对参数做模式匹配来定义的：能匹配任何二元组的模式是 `(x, y)`，它把二元组的两个分量分别取到变量 `x` 和 `y` 里。`def f : A → B` 后面直接跟 `| 模式 => 结果` 的写法，是 Lean 中“按模式定义函数”的简写，相当于 `fun p => match p with | (x, y) => x`。

如果你把上面这段代码交给 Lean，它会客气地发出警告：`fst` 里的变量 `y`、`snd` 里的变量 `x` 从来没有被用到（Rust 编译器也会对未使用的变量发出类似的警告）。用**通配符** `_` 就能把定义进一步简化——用不到的变量，干脆不起名字：

```lean
namespace MyDefs2

def fst {α β : Type} : α × β → α
  | (x, _) => x

def snd {α β : Type} : α × β → β
  | (_, y) => y

end MyDefs2
```

在 Rust 里，元组的投影是内置语法 `p.0`、`p.1`；要写成泛型函数的话，大概是这样：

```rust
fn fst<A, B>(p: (A, B)) -> A {
    p.0
}

fn snd<A, B>((_, y): (A, B)) -> B {
    y // Rust 也能在参数位置做模式匹配，`_` 同样是通配符
}
```

带着这点看似非常有限的知识，我们来试着在集合范畴中定义一个对象与态射的模式，让它把我们引向两个集合 $a$ 和 $b$ 的积的构造。这个模式由一个对象 $c$ 和两个态射 $p$、$q$ 组成，它们分别把 $c$ 连到 $a$ 和 $b$：

```lean no-check
p : c → a
q : c → b
```

![积的模式](/img/1.5/productpattern.jpg "积的模式：一个对象 c，带着两个分别指向 a 和 b 的态射 p、q。")

所有符合这个模式的 $c$ 都会被当作积的**候选者**。候选者可能有很多很多。

![积的候选者](/img/1.5/productcandidates.jpg "符合这个模式的候选者可能有很多。")

例如，我们挑两个 Lean 类型 `Int` 和 `Bool` 作为组成部分，来抽样看看它们的积有哪些候选者。

这里有一个：`Int`。`Int` 能被当作 `Int` 与 `Bool` 之积的候选者吗？能——下面就是它的两个投影：

```lean
namespace Cand1

def p : Int → Int := fun x => x
def q : Int → Bool := fun _ => true

end Cand1
```

这相当寒碜，但它符合标准。

这里还有一个：`Int × Int × Bool`。这是一个三元组。下面两个态射使它成为一个合格的候选者（我们对三元组做模式匹配）：

```lean
namespace Cand2

def p : Int × Int × Bool → Int := fun (x, _, _) => x
def q : Int × Int × Bool → Bool := fun (_, _, b) => b

end Cand2
```

::: tip Lean 深入：三元组其实是嵌套的二元组
Lean 里的 `×` 是右结合的：`Int × Int × Bool` 就是 `Int × (Int × Bool)`，`(x, y, b)` 就是 `(x, (y, b))`。
Lean 没有单独的“三元组”类型，二元组嵌套一下就够了（Rust 则有独立的 `(i32, i32, bool)` 类型）。
模式 `(x, _, _)` 同样会被自动展开成嵌套的匹配，所以写起来和真正的三元组没什么两样。
另外，Lean 的 `Int` 是任意精度的整数，不会溢出，比 Rust 的 `i32` 更接近数学上的整数集合。
:::

你可能已经注意到：第一个候选者太**小**了——它只覆盖了积的 `Int` 那一维；第二个又太**大**了——它多余地把 `Int` 那一维复制了一份。

但我们还没有探索泛构造的另一部分：排名。我们希望能比较模式的两个实例：把一个候选对象 $c$ 及其两个投影 $p$、$q$，与另一个候选对象 $c'$ 及其两个投影 $p'$、$q'$ 作比较。我们想说：如果有一个从 $c'$ 到 $c$ 的态射 $m$，那么 $c$ 就比 $c'$“更好”——但这个条件太弱了。我们还希望 $c$ 的投影比 $c'$ 的投影“更好”，或者说“更通用”。这句话的意思是：投影 $p'$ 和 $q'$ 可以借助 $m$ 从 $p$ 和 $q$ 重建出来：

$$p' = p \circ m \qquad q' = q \circ m$$

![积的排名](/img/1.5/productranking.jpg "如果存在 m 使得 p' = p ∘ m 且 q' = q ∘ m，那么 c 比 c' 更好。")

```diagram
C2: (1.2, 0) "c'"
C: (1.2, 1.25) "c"
A: (0, 2.5) "a"
B: (2.4, 2.5) "b"
p2: C2 -> A "p'" bend=-38 side=right
q2: C2 -> B "q'" bend=38 side=left
m: C2 -> C "m" dashed side=left
p: C -> A "p" side=left
q: C -> B "q" side=right
path "直接走 p′": p2 color=orange
path "先 m 再 p": m p color=brand
path "直接走 q′": q2 color=orange
path "先 m 再 q": m q color=brand
caption: 积的排名：c 比 c' 更好，当且仅当存在 m 使两个三角形都交换——走 p′ 和走“先 m 再 p”到达同一个地方，q 那边也一样。
```

看待这两个等式的另一种方式是：$m$ **分解**（factorize）了 $p'$ 和 $q'$。不妨假装这两个等式是自然数上的等式，而那个圆点是乘法：$m$ 就是 $p'$ 和 $q'$ 共有的一个公因子。

为了建立一些直觉，我来证明一下：带着两个标准投影 `Prod.fst` 和 `Prod.snd` 的二元组 `Int × Bool`，确实比前面那两个候选者都**更好**。

![不是积](/img/1.5/not-a-product.jpg "Int × Bool 比前面两个候选者都更好。")

对第一个候选者，映射 `m` 是：

```lean
namespace Cand1

def m : Int → Int × Bool := fun x => (x, true)

end Cand1
```

确实，两个投影 `p` 和 `q` 都可以重建出来：`p x = Prod.fst (m x) = x`，`q x = Prod.snd (m x) = true`。在 Lean 里，这两句话就是两个定理，而且都是 `rfl`：

```lean
example : Cand1.p = Prod.fst ∘ Cand1.m := rfl
example : Cand1.q = Prod.snd ∘ Cand1.m := rfl
```

第二个例子里的 `m` 同样是唯一确定的：

```lean
namespace Cand2

def m : Int × Int × Bool → Int × Bool := fun (x, _, b) => (x, b)

example : p = Prod.fst ∘ m := rfl
example : q = Prod.snd ∘ m := rfl

end Cand2
```

我们证明了 `Int × Bool` 比两个候选者都好。来看看为什么反过来不成立。我们能不能找到某个 `m'`，帮我们从 `p` 和 `q` 重建出 `fst` 和 `snd` 呢？

$$\mathtt{fst} = p \circ m' \qquad \mathtt{snd} = q \circ m'$$

在第一个例子里，`q` 永远返回 `true`，而我们知道有些二元组的第二个分量是 `false`。我们没法从 `q` 重建出 `snd`。用 Lean 说，就是“不存在这样的 `m'`”：

```lean
theorem cand1_not_better :
    ¬ ∃ m' : Int × Bool → Int, Prod.fst = Cand1.p ∘ m' ∧ Prod.snd = Cand1.q ∘ m' := by
  intro ⟨m', _, h⟩                  -- 假设有这样的 m'，且 snd = q ∘ m'
  have := congrFun h (0, false)     -- 在 (0, false) 上：false = q (m' (0, false)) = true
  simp [Cand1.q] at this            -- false = true，矛盾
```

第二个例子则不同：运行 `p` 或 `q` 之后，我们保留了足够的信息，但分解 `fst` 和 `snd` 的方式不止一种。因为 `p` 和 `q` 都忽略三元组的第二个分量，我们的 `m'` 可以往那里放任何东西。可以是：

```lean
namespace Cand2

def m'₁ : Int × Bool → Int × Int × Bool := fun (x, b) => (x, x, b)

end Cand2
```

也可以是：

```lean
namespace Cand2

def m'₂ : Int × Bool → Int × Int × Bool := fun (x, b) => (x, 42, b)

-- 两者都能重建 fst 和 snd……
example : Prod.fst = p ∘ m'₁ ∧ Prod.snd = q ∘ m'₁ := ⟨rfl, rfl⟩
example : Prod.fst = p ∘ m'₂ ∧ Prod.snd = q ∘ m'₂ := ⟨rfl, rfl⟩

-- ……但它们是不同的函数
example : m'₁ ≠ m'₂ := by
  intro h
  have := congrFun h (0, true)      -- (0, 0, true) = (0, 42, true)？
  simp [m'₁, m'₂] at this

end Cand2
```

等等，还有无数种。

下面这个组件让你亲手做这种比较。挑一个“挑战者” $c'$ 和一个“被比较者” $c$，它会去找所有满足 $p' = p \circ m$、$q' = q \circ m$ 的 $m$：如果找不到，就给出反例；如果找到不止一个，就把歧义之处指出来。最下面的排行榜汇总了所有两两比较的结果。

<div><Ch1_5ProductRanking /></div>

把这些放在一起：给定任何一个带两个投影 `p` 和 `q` 的类型 `c`，都有唯一一个从 `c` 到笛卡尔积 `a × b` 的 `m` 分解它们。事实上，它就是把 `p` 和 `q` 合成一个二元组：

```lean no-check
m : c → a × b
m x = (p x, q x)
```

这使得笛卡尔积 `a × b` 成为我们的最佳匹配，也就是说，这个泛构造在集合范畴中是行得通的：它挑出了任意两个集合的积。

现在让我们忘掉集合，用同样的泛构造来定义**任意**范畴中两个对象的积。这样的积并不总是存在，但只要存在，它就在唯一同构意义下唯一。

> 对象 $a$ 和 $b$ 的**积**（product），是配备了两个投影的对象 $c$，使得对任何其他配备了两个投影的对象 $c'$，都存在唯一一个从 $c'$ 到 $c$ 的态射 $m$，分解那两个投影。

一个从两个候选投影产生分解函数 `m` 的（高阶）函数，有时被称为**分解子**（factorizer）。在我们的例子里，它就是这个函数：

```lean
def factorizer {a b c : Type} (p : c → a) (q : c → b) : c → a × b :=
  fun x => (p x, q x)
```

::: tip Rust 视角
```rust no-check
fn factorizer<A, B, C>(p: impl Fn(&C) -> A, q: impl Fn(&C) -> B) -> impl Fn(&C) -> (A, B) {
    move |x| (p(x), q(x))
}
```
这就是那个你写过无数次的“把两个 getter 合并成一个返回元组的函数”。泛性质告诉你：**只有**这一种写法是对的。
:::

## 补充：用 Lean 证明积的泛性质

原书说“存在唯一的 `m`”。“存在”这一半就是 `factorizer` 本身外加两个 `rfl`；“唯一”这一半需要一个真正的证明：

```lean
/-- 存在：factorizer p q 确实让两个三角形交换。 -/
theorem factorizer_fst {a b c : Type} (p : c → a) (q : c → b) :
    Prod.fst ∘ factorizer p q = p := rfl

theorem factorizer_snd {a b c : Type} (p : c → a) (q : c → b) :
    Prod.snd ∘ factorizer p q = q := rfl

/-- 唯一：任何让两个三角形交换的 m，都等于 factorizer p q。 -/
theorem factorizer_unique {a b c : Type} (p : c → a) (q : c → b) (m : c → a × b)
    (h₁ : Prod.fst ∘ m = p) (h₂ : Prod.snd ∘ m = q) :
    m = factorizer p q := by
  funext x               -- 对每个 x 证明 m x = (p x, q x)
  rw [← h₁, ← h₂]        -- 把 p、q 换回 fst ∘ m、snd ∘ m：目标变成 m x = ((m x).1, (m x).2)
  rfl                    -- 二元组的 eta 规则：任何二元组都等于“由它的两个分量重新组成的二元组”
```

这个证明的核心只有一句话：**一个二元组完全由它的两个分量决定**。既然 `m x` 的第一个分量必须是 `p x`、第二个分量必须是 `q x`，那 `m x` 就别无选择，只能是 `(p x, q x)`。

现在把“积”的泛性质写成对任意范畴都有意义的结构体。注意它和原书的文字定义是一一对应的：

```lean
/-- `p` 是 `a` 与 `b` 的积：带两个投影，且任何候选者都有唯一的分解态射 `lift f g`。 -/
structure IsProduct {C : Type u} [Category.{u, v} C] (a b p : C) where
  fst : p ⟶ a
  snd : p ⟶ b
  lift : {c : C} → (c ⟶ a) → (c ⟶ b) → (c ⟶ p)                -- 分解子（存在）
  fac_fst : ∀ {c : C} (f : c ⟶ a) (g : c ⟶ b), fst ⊚ lift f g = f
  fac_snd : ∀ {c : C} (f : c ⟶ a) (g : c ⟶ b), snd ⊚ lift f g = g
  uniq : ∀ {c : C} (f : c ⟶ a) (g : c ⟶ b) (m : c ⟶ p),         -- 唯一
    fst ⊚ m = f → snd ⊚ m = g → m = lift f g

/-- 在 Type 中，α × β 就是 α 与 β 的积。 -/
def prodIsProduct (α β : Type) : IsProduct (C := Type) α β (α × β) where
  fst := Prod.fst
  snd := Prod.snd
  lift f g := factorizer f g
  fac_fst _ _ := rfl
  fac_snd _ _ := rfl
  uniq f g m h₁ h₂ := factorizer_unique f g m h₁ h₂
```

最后，原书说“积只要存在，就在唯一同构意义下唯一”。我们也把它证出来（证明折叠起来了，感兴趣可以展开）：

::: details 完整证明：任意两个积都同构
思路和始对象那里完全一样：用 `Q` 的泛性质得到 `P ⟶ Q`，用 `P` 的泛性质得到 `Q ⟶ P`；
绕一圈回到 `P` 的态射和 `𝟙 P` 都分解 `P` 自己的两个投影，由唯一性，它们相等。

```lean
/-- 恒等态射就是“把自己的两个投影重新组合起来”。 -/
theorem IsProduct.lift_self {C : Type u} [Category.{u, v} C] {a b p : C}
    (P : IsProduct a b p) : 𝟙 p = P.lift P.fst P.snd :=
  P.uniq _ _ _ (Category.comp_id _) (Category.comp_id _)

def productIso {C : Type u} [Category.{u, v} C] {a b p q : C}
    (P : IsProduct a b p) (Q : IsProduct a b q) : Iso p q where
  hom := Q.lift P.fst P.snd
  inv := P.lift Q.fst Q.snd
  inv_hom := by
    rw [P.lift_self]          -- 把 𝟙 p 换成 P.lift P.fst P.snd
    apply P.uniq              -- 只需证明“绕一圈”也分解 P.fst 和 P.snd
    · rw [Category.assoc, P.fac_fst, Q.fac_fst]
    · rw [Category.assoc, P.fac_snd, Q.fac_snd]
  hom_inv := by
    rw [Q.lift_self]
    apply Q.uniq
    · rw [Category.assoc, Q.fac_fst, P.fac_fst]
    · rw [Category.assoc, Q.fac_snd, P.fac_snd]

-- 例如：Int × Bool 和 Bool × Int（配上交换过的投影）都是 Int 与 Bool 的积，所以它们同构
def swappedIsProduct : IsProduct (C := Type) Int Bool (Bool × Int) where
  fst := Prod.snd
  snd := Prod.fst
  lift f g := fun x => (g x, f x)
  fac_fst _ _ := rfl
  fac_snd _ _ := rfl
  uniq f g m h₁ h₂ := by
    funext x
    rw [← h₁, ← h₂]
    rfl

example : (productIso (prodIsProduct Int Bool) swappedIsProduct).hom (3, true) = (true, 3) := rfl
```
:::

## 余积

和范畴论中的每一个构造一样，积也有一个对偶，叫做**余积**（coproduct）。把积的模式中的箭头反过来，我们得到一个对象 $c$，配备两个**内射**（injection）`i` 和 `j`：从 $a$ 和 $b$ 到 $c$ 的态射。

```lean no-check
i : a → c
j : b → c
```

![余积的模式](/img/1.5/coproductpattern.jpg "余积的模式：两个箭头 i、j 分别从 a 和 b 射入 c。")

排名也反了过来：如果有一个从 $c$ 到 $c'$ 的态射 $m$ 分解了内射，那么对象 $c$ 就比配备了内射 $i'$ 和 $j'$ 的对象 $c'$“更好”：

$$i' = m \circ i \qquad j' = m \circ j$$

![余积的排名](/img/1.5/coproductranking.jpg "如果存在 m 使得 i' = m ∘ i 且 j' = m ∘ j，那么 c 比 c' 更好。")

```diagram
A: (0, 0) "a"
B: (2.4, 0) "b"
C: (1.2, 1.25) "c"
C2: (1.2, 2.5) "c'"
i2: A -> C2 "i'" bend=-38 side=right
j2: B -> C2 "j'" bend=38 side=left
i: A -> C "i" side=right
j: B -> C "j" side=left
m: C -> C2 "m" dashed side=left
path "直接走 i′": i2 color=orange
path "先 i 再 m": i m color=brand
path "直接走 j′": j2 color=orange
path "先 j 再 m": j m color=brand
caption: 余积的排名：箭头全部反向。c 比 c' 更好，当且仅当存在从 c 出发的 m，使 i′ = m ∘ i、j′ = m ∘ j。
```

“最好”的那个对象——与任何其他模式实例之间都有唯一态射相连的那个——叫做余积。如果它存在，它在唯一同构意义下唯一。

> 对象 $a$ 和 $b$ 的**余积**（coproduct），是配备了两个内射的对象 $c$，使得对任何其他配备了两个内射的对象 $c'$，都存在唯一一个从 $c$ 到 $c'$ 的态射 $m$，分解那两个内射。

在集合范畴中，余积是两个集合的**不交并**（disjoint union）。$a$ 与 $b$ 的不交并中的一个元素，要么是 $a$ 的元素，要么是 $b$ 的元素。如果两个集合有重叠，不交并会包含公共部分的两份拷贝。你可以把不交并中的元素想象成贴上了一个标签，标明它的出身。

::: info 数学小课堂：并集与不交并
普通的**并集**：$\{1, 2\} \cup \{2, 3\} = \{1, 2, 3\}$——那个 $2$ 只出现一次，你分不清它是从哪边来的。

**不交并**会给每个元素贴上出身标签：$\{1, 2\} \sqcup \{2, 3\} = \{\mathsf{左}\,1, \mathsf{左}\,2, \mathsf{右}\,2, \mathsf{右}\,3\}$——四个元素，
两个 $2$ 是不同的。所以不交并的大小永远是两边大小之和（$2 + 2 = 4$），而并集不一定（这里只有 $3$）。
一个集合和它自己的不交并 $a \sqcup a$，就是“两份 $a$”。
:::

对程序员来说，用类型来理解余积更容易：它是两个类型的**带标签的联合**（tagged union）。Rust 其实同时支持两种联合：不带标签的 `union`（主要为了和 C 互操作）和带标签的 `enum`。不带标签的联合意味着你得在程序里自己想办法记住联合中的哪个成员是有效的。要做出一个带标签的联合，你得自己定义一个标签（一个枚举），再把它和联合组合起来。比如，一个 `i32` 和一个 C 字符串指针的带标签联合，可以这样实现：

```rust
#[derive(Clone, Copy)]
enum Tag {
    IsPhone,
    IsEmail,
}

#[derive(Clone, Copy)]
union ContactData {
    phone_num: i32,
    email_addr: *const u8,
}

struct Contact {
    tag: Tag,
    data: ContactData,
}

// 两个内射既可以实现为构造子，也可以实现为函数。比如第一个内射，写成函数 phone_num：
fn phone_num(n: i32) -> Contact {
    Contact { tag: Tag::IsPhone, data: ContactData { phone_num: n } }
}

// 读取联合的字段必须用 unsafe：编译器无法替你保证你读的正是写进去的那个成员
fn describe(c: &Contact) -> String {
    match c.tag {
        Tag::IsPhone => format!("phone: {}", unsafe { c.data.phone_num }),
        Tag::IsEmail => "email".to_string(),
    }
}
```

`phone_num` 把一个整数“射入”`Contact`。

带标签的联合也被称为**变体**（variant）。在 Rust 里你几乎从不需要像上面那样手工拼装，因为 `enum` 就是语言内置的、完全安全的带标签联合：

```rust
enum Contact {
    PhoneNum(i32),
    EmailAddr(String),
}

fn helpdesk() -> Contact {
    Contact::PhoneNum(2222222)
}
```

在 Lean 里，你可以用 `inductive` 把任意数据类型组合成一个带标签的联合，每个构造子占一行、以竖线 `|` 开头。`Contact` 的例子翻译过来就是：

```lean
inductive Contact where
  | phoneNum : Int → Contact
  | emailAddr : String → Contact
```

这里，`phoneNum` 和 `emailAddr` 既是构造子（内射），又是模式匹配时用的标签（后面还会细讲）。例如，下面是用电话号码构造一个联系人的方法：

```lean
def helpdesk : Contact := .phoneNum 2222222
```

（`.phoneNum` 前面的点是“从期望类型中找构造子”的简写：Lean 知道这里要的是 `Contact`，所以 `.phoneNum` 就是 `Contact.phoneNum`。）

积的标准实现是内置的二元组，而余积的标准实现是一个数据类型，Haskell 里叫 `Either`，Lean 核心库里叫 `Sum`，记作 `α ⊕ β`（`⊕` 用 `\oplus` 输入）。它的定义大致是这样：

```lean
namespace MyDefs

inductive Either (α β : Type) where
  | left : α → Either α β
  | right : β → Either α β

end MyDefs

-- Lean 核心库中的版本：
#check @Sum.inl   -- {α β} → α → α ⊕ β
#check @Sum.inr   -- {α β} → β → α ⊕ β
```

它以两个类型 `α` 和 `β` 为参数，有两个构造子：接受 `α` 类型值的 `left`（在 `Sum` 里叫 `inl`，即 “inject left”），以及接受 `β` 类型值的 `right`（`inr`）。

正如我们为积定义了分解子，我们也可以为余积定义一个。给定一个候选类型 `c` 和两个候选内射 `i`、`j`，`Sum` 的分解子会产生那个分解函数：

```lean
def coFactorizer {a b c : Type} (i : a → c) (j : b → c) : a ⊕ b → c
  | .inl x => i x
  | .inr y => j y
```

它在核心库里也有现成的版本，叫 `Sum.elim`。在 Rust 里，它就是一个 `match`：

```rust
enum Either<A, B> {
    Left(A),
    Right(B),
}

fn factorizer<A, B, C>(i: impl Fn(A) -> C, j: impl Fn(B) -> C) -> impl Fn(Either<A, B>) -> C {
    move |e| match e {
        Either::Left(a) => i(a),
        Either::Right(b) => j(b),
    }
}
```

::: tip 补充：余积泛性质的 Lean 证明
和积一样，“存在”是两个 `rfl`，“唯一”需要一个证明。这次的关键不再是“二元组由两个分量决定”，
而是“`a ⊕ b` 的每个值，要么是 `inl x`，要么是 `inr y`”——于是用 `cases` 分两种情况讨论：

```lean
theorem coFactorizer_inl {a b c : Type} (i : a → c) (j : b → c) :
    coFactorizer i j ∘ Sum.inl = i := rfl

theorem coFactorizer_inr {a b c : Type} (i : a → c) (j : b → c) :
    coFactorizer i j ∘ Sum.inr = j := rfl

theorem coFactorizer_unique {a b c : Type} (i : a → c) (j : b → c) (m : a ⊕ b → c)
    (h₁ : m ∘ Sum.inl = i) (h₂ : m ∘ Sum.inr = j) :
    m = coFactorizer i j := by
  funext s
  cases s with
  | inl x => rw [← h₁]; rfl     -- m (inl x) = (m ∘ inl) x
  | inr y => rw [← h₂]; rfl     -- m (inr y) = (m ∘ inr) y

/-- 余积的泛性质：积的定义里所有箭头反向。 -/
structure IsCoproduct {C : Type u} [Category.{u, v} C] (a b s : C) where
  inl : a ⟶ s
  inr : b ⟶ s
  desc : {c : C} → (a ⟶ c) → (b ⟶ c) → (s ⟶ c)
  fac_inl : ∀ {c : C} (f : a ⟶ c) (g : b ⟶ c), desc f g ⊚ inl = f
  fac_inr : ∀ {c : C} (f : a ⟶ c) (g : b ⟶ c), desc f g ⊚ inr = g
  uniq : ∀ {c : C} (f : a ⟶ c) (g : b ⟶ c) (m : s ⟶ c),
    m ⊚ inl = f → m ⊚ inr = g → m = desc f g

def sumIsCoproduct (α β : Type) : IsCoproduct (C := Type) α β (α ⊕ β) where
  inl := Sum.inl
  inr := Sum.inr
  desc f g := coFactorizer f g
  fac_inl _ _ := rfl
  fac_inr _ _ := rfl
  uniq f g m h₁ h₂ := coFactorizer_unique f g m h₁ h₂
```

对比 `IsProduct` 和 `IsCoproduct`：把每个箭头反过来、把 `⊚` 两边对调，一个就变成了另一个。这就是“对偶”在代码里的样子。
:::

## 不对称性

我们已经看到了两组对偶的定义：终对象的定义可以通过反转箭头方向从始对象的定义得到；类似地，余积的定义也可以从积的定义得到。然而在集合范畴中，始对象和终对象非常不同，余积和积也非常不同。我们以后会看到，积的行为像乘法，终对象扮演 1 的角色；而余积的行为更像加法，始对象扮演 0 的角色。特别地，对有限集合来说，积的大小是各个集合大小的乘积，余积的大小是各个集合大小的和。

（比如 `Bool × Bool` 有 $2 \times 2 = 4$ 个值，`Bool ⊕ Bool` 有 $2 + 2 = 4$ 个值——巧了；但 `Bool × Unit` 有 $2 \times 1 = 2$ 个值，`Bool ⊕ Unit` 有 $2 + 1 = 3$ 个值。下一章会把这种“类型的算术”发展成一整套代数。）

这表明集合范畴在箭头反转下并不是对称的。

请注意，空集有到任何集合的唯一态射（`absurd'` 函数），却没有任何态射射回来（除了到它自己的恒等）。单元素集有从任何集合射入的唯一态射，但它**也**有射向每个集合（空集除外）的态射。正如我们之前看到的，这些从终对象射出的态射扮演着非常重要的角色：它们挑出其他集合中的元素（空集没有元素，所以也就没什么可挑的）。

正是单元素集与积之间的关系，使它与余积区别开来。考虑用单元素集（由单位类型 `Unit` 表示）作为积模式的又一个——远远更差的——候选者。给它配上两个投影 `p` 和 `q`：从单元素集到各个组成集合的函数。它们各自从对应的集合里选出一个具体的元素。因为积是泛的，所以也存在一个从我们的候选者（单元素集）到积的（唯一的）态射 `m`。这个态射从积集合中选出一个元素——它选出了一个具体的二元组。它同时也分解了两个投影：

```lean no-check
p = Prod.fst ∘ m
q = Prod.snd ∘ m
```

作用在单元素集唯一的元素 `()` 上，这两个等式就变成：

```lean no-check
p () = Prod.fst (m ())
q () = Prod.snd (m ())
```

既然 `m ()` 是 `m` 从积中挑出的那个元素，这两个等式告诉我们：`p` 从第一个集合中挑出的元素 `p ()`，就是 `m` 挑出的那个二元组的第一个分量。类似地，`q ()` 等于第二个分量。这与我们“积的元素是由各组成集合中元素组成的二元组”的理解完全一致。用 Lean 把这个推理写下来：

```lean
/-- 从 Unit 出发的分解态射 m，挑出的恰好是二元组 (p (), q ())。 -/
theorem unit_candidate {a b : Type} (p : Unit → a) (q : Unit → b) (m : Unit → a × b)
    (h₁ : p = Prod.fst ∘ m) (h₂ : q = Prod.snd ∘ m) :
    m () = (p (), q ()) := by
  rw [h₁, h₂]   -- 目标变成 m () = ((m ()).1, (m ()).2)
  rfl           -- 二元组的 eta 规则
```

对余积，就没有这么简单的解释了。我们可以试着把单元素集当作余积的候选者，企图从中提取元素，但那样我们得到的是两个**射入**它的内射，而不是两个从它**射出**的投影。它们不会告诉我们关于其来源的任何信息（事实上，我们已经看到，它们根本无视自己的输入参数）。从余积到单元素集的那个唯一态射也一样。从始对象那一端看集合范畴，和从终对象那一端看，景色是截然不同的。

这不是集合本身的固有性质，而是函数的性质——我们在 $\mathbf{Set}$ 中用函数作为态射。函数一般来说是不对称的。我来解释一下。

函数必须对其定义域中的每个元素都有定义（在编程里，我们称之为**全函数**（total function）），但它不必覆盖整个陪域。我们已经见过一些极端情况：从单元素集出发的函数——只在陪域中选出一个元素的函数。（实际上，从空集出发的函数才是真正的极端。）当定义域的大小远小于陪域的大小时，我们常常把这样的函数看作把定义域**嵌入**（embedding）到陪域之中。例如，我们可以把一个从单元素集出发的函数，看作把它唯一的元素嵌入到陪域中。我管它们叫**嵌入**函数，但数学家更愿意给反面情况起名字：紧密地填满陪域的函数，被称为**满射**（surjective，或 onto）。

不对称性的另一个来源是：函数允许把定义域中的多个元素映射到陪域中的同一个元素。它们可以把元素**坍缩**到一起。极端情况是把整个集合映射到单元素集的函数。你已经见过那个干的正是这件事的多态函数 `unit`。坍缩只会因复合而加剧：两个坍缩函数的复合，比单独的任何一个都更坍缩。数学家给不坍缩的函数起了名字：他们称之为**单射**（injective，或 one-to-one）。

当然，有一些函数既不嵌入也不坍缩。它们被称为**双射**（bijection），而且它们是真正对称的，因为它们可逆。在集合范畴中，同构就是双射。

::: info 数学小课堂：单射、满射、双射
设 $f \colon A \to B$。

- **单射**（不坍缩）：不同的输入给出不同的输出。等价地说：$f(x) = f(y)$ 蕴含 $x = y$。
  例：`fun (n : Nat) => n + 1` 是单射；`unit : Nat → Unit` 不是（所有输入都坍缩到 `()`）。
- **满射**（填满陪域）：陪域中每个元素都至少被某个输入“打中”。即：对每个 $b \in B$，存在 $a$ 使 $f(a) = b$。
  例：`unit : Nat → Unit` 是满射；`fun (n : Nat) => n + 1` 不是（`0` 没有被打中）。
- **双射**：既单又满，于是陪域中每个元素都**恰好**被一个输入打中——这正好让我们能把箭头反过来，定义出逆函数。

Lean 核心库里有前两个的定义：

```lean no-check
def Function.Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
def Function.Surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b
```
:::

我们可以在 Lean 里证明“同构就是双射”的一个方向：`Type` 中的同构，其正向函数既是单射又是满射。

```lean
theorem iso_injective {α β : Type} (e : Iso (C := Type) α β) : Function.Injective e.hom := by
  intro x y h                                   -- 假设 e.hom x = e.hom y
  have hx : e.inv (e.hom x) = x := congrFun e.inv_hom x
  have hy : e.inv (e.hom y) = y := congrFun e.inv_hom y
  rw [← hx, ← hy, h]                            -- x = inv (hom x) = inv (hom y) = y

theorem iso_surjective {α β : Type} (e : Iso (C := Type) α β) : Function.Surjective e.hom :=
  fun b => ⟨e.inv b, congrFun e.hom_inv b⟩      -- b 被 e.inv b 打中
```

（另一个方向——每个双射都能构造出一个 `Iso`——需要从“存在一个原像”中真正**取出**那个原像来定义逆函数，这在 Lean 里要用到选择公理 `Classical.choose`。我们暂且按下不表。）

## 挑战

1. 证明终对象在唯一同构意义下唯一。
2. 偏序集中两个对象的积是什么？提示：使用泛构造。
3. 偏序集中两个对象的余积是什么？
4. 用你喜欢的语言（Haskell 除外）实现一个与 Haskell 的 `Either` 等价的泛型类型。
5. 证明：`Either`（Lean 中的 `Int ⊕ Bool`）是一个比配备了下面两个内射的 `Int` “更好”的余积：

```lean no-check
def i (n : Int) : Int := n
def j (b : Bool) : Int := if b then 0 else 1
```

   提示：定义一个函数 `m : Int ⊕ Bool → Int`，使它分解 `i` 和 `j`。

6. 接着上一题：你会如何论证，配备了这两个内射 `i` 和 `j` 的 `Int` 不可能比 `Either` “更好”？
7. 还是接着来：换成下面这两个内射呢？

```lean no-check
def i (n : Int) : Int := if n < 0 then n else n + 2
def j (b : Bool) : Int := if b then 0 else 1
```

8. 为 `Int` 和 `Bool` 的余积构想一个较差的候选者，使它不可能比 `Either` 更好，因为它允许存在多个从它到 `Either` 的可接受的态射。

::: details 参考答案

**第 1 题。** 直接仿照始对象的证明，把箭头反过来即可：

```lean
def terminalIso {C : Type u} [Category.{u, v} C] {t₁ t₂ : C}
    (h₁ : IsTerminal t₁) (h₂ : IsTerminal t₂) : Iso t₁ t₂ where
  hom := h₂.from_ t₁    -- t₂ 是终对象，所以有 t₁ ⟶ t₂
  inv := h₁.from_ t₂    -- t₁ 是终对象，所以有 t₂ ⟶ t₁
  inv_hom := by rw [h₁.uniq (h₁.from_ t₂ ⊚ h₂.from_ t₁), h₁.uniq (𝟙 t₁)]
  hom_inv := by rw [h₂.uniq (h₂.from_ t₁ ⊚ h₁.from_ t₂), h₂.uniq (𝟙 t₂)]

/-- 同构是唯一的：任何 t₁ ⟶ t₂ 都等于 h₂.from_ t₁。 -/
theorem terminalIso_unique {C : Type u} [Category.{u, v} C] {t₁ t₂ : C}
    (h₁ : IsTerminal t₁) (h₂ : IsTerminal t₂) (e : Iso t₁ t₂) :
    e.hom = (terminalIso h₁ h₂).hom :=
  h₂.uniq e.hom
```

更“范畴论”的做法是利用对偶：$\mathcal{C}$ 中的终对象是 $\mathcal{C}^{op}$ 中的始对象，而我们已经证明了始对象在唯一同构意义下唯一。
$\mathcal{C}^{op}$ 中 $t_2$ 到 $t_1$ 的同构，翻回 $\mathcal{C}$ 就是 $t_1$ 到 $t_2$ 的同构：

```lean
/-- Cᵒᵖ 中的同构 a ≅ b，就是 C 中的同构 b ≅ a。 -/
def Iso.unop {C : Type u} [Category.{u, v} C] {a b : C} (e : @Iso (Op C) _ a b) : Iso b a where
  hom := e.hom
  inv := e.inv
  inv_hom := e.hom_inv
  hom_inv := e.inv_hom

def terminalIso' {C : Type u} [Category.{u, v} C] {t₁ t₂ : C}
    (h₁ : IsTerminal t₁) (h₂ : IsTerminal t₂) : Iso t₁ t₂ :=
  Iso.unop (initialIso h₂.op h₁.op)
```

这就是“对偶让生产力翻倍”：第二个版本没有重新论证任何东西。

**第 2 题。** 在偏序集中，从 $x$ 到 $y$ 的态射存在，当且仅当 $x \le y$，而且最多只有一个。套用积的泛构造：
$a$ 与 $b$ 的积是一个对象 $c$，带“投影” $c \le a$、$c \le b$——也就是说，$c$ 是 $a$ 和 $b$ 的一个**下界**；
并且对任何其他下界 $c'$（$c' \le a$ 且 $c' \le b$），都有态射 $c' \le c$（唯一性在偏序集里自动成立，因为最多只有一个态射）。
所以积就是**最大下界**（greatest lower bound，又称**交**，meet），记作 $a \wedge b$。
在自然数配 $\le$ 的偏序集里，它就是 $\min(a, b)$；在“整除”偏序集里，它是最大公约数；在集合配 $\subseteq$ 的偏序集里，它是交集。

我们可以把自然数的 $\le$ 做成一个范畴（态射是“$\le$ 的证明”，用 `PLift` 把命题包装成类型），然后证明 `min` 确实满足 `IsProduct`：

```lean
/-- 自然数配 ≤ 构成的瘦范畴。 -/
structure NatLe where
  n : Nat

instance natLeCategory : Category NatLe where
  Hom a b := PLift (a.n ≤ b.n)            -- 从 a 到 b 的态射：a ≤ b 的证明
  id a := ⟨Nat.le_refl a.n⟩               -- 自反性
  comp g f := ⟨Nat.le_trans f.down g.down⟩ -- 传递性
  -- 三条定律都是 rfl：同一命题的任何两个证明在 Lean 中定义上相等（证明无关性）

def minIsProduct (a b : NatLe) : IsProduct a b ⟨min a.n b.n⟩ where
  fst := ⟨Nat.min_le_left a.n b.n⟩        -- min a b ≤ a
  snd := ⟨Nat.min_le_right a.n b.n⟩       -- min a b ≤ b
  lift f g := ⟨Nat.le_min.mpr ⟨f.down, g.down⟩⟩  -- c ≤ a 且 c ≤ b ⇒ c ≤ min a b
  fac_fst _ _ := rfl
  fac_snd _ _ := rfl
  uniq _ _ _ _ _ := rfl                   -- 瘦范畴：两个态射总是相等
```

**第 3 题。** 对偶地，余积是**最小上界**（least upper bound，又称**并**，join），记作 $a \vee b$：
它是 $a$ 和 $b$ 的上界，并且小于等于任何其他上界。在自然数配 $\le$ 中是 $\max(a, b)$；在整除偏序集中是最小公倍数；在集合配 $\subseteq$ 中是并集。

```lean
def maxIsCoproduct (a b : NatLe) : IsCoproduct a b ⟨max a.n b.n⟩ where
  inl := ⟨Nat.le_max_left a.n b.n⟩
  inr := ⟨Nat.le_max_right a.n b.n⟩
  desc f g := ⟨Nat.max_le.mpr ⟨f.down, g.down⟩⟩
  fac_inl _ _ := rfl
  fac_inr _ _ := rfl
  uniq _ _ _ _ _ := rfl
```

**第 4 题。** Rust 版本前面已经写过；完整一点，再配上分解子和几个常用方法：

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A, B> Either<A, B> {
    pub fn either<C>(self, f: impl FnOnce(A) -> C, g: impl FnOnce(B) -> C) -> C {
        match self {
            Either::Left(a) => f(a),
            Either::Right(b) => g(b),
        }
    }

    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }
}
```

Lean 版本就是前面的 `MyDefs.Either`（以及核心库的 `Sum`）。

**第 5 题。**

```lean
namespace Ch5

def i (n : Int) : Int := n
def j (b : Bool) : Int := if b then 0 else 1

def m : Int ⊕ Bool → Int
  | .inl n => i n
  | .inr b => j b

-- m 分解了 i 和 j：两个三角形都交换
example : i = m ∘ Sum.inl := rfl
example : j = m ∘ Sum.inr := rfl

end Ch5
```

而且由 `coFactorizer_unique`，这样的 `m` 是唯一的（`m` 就是 `coFactorizer i j`）。

**第 6 题。** 要让 `Int` 比 `Either` 好，需要一个 `m' : Int → Int ⊕ Bool`，使得 `Sum.inl = m' ∘ i` 且 `Sum.inr = m' ∘ j`。
但 `i 0 = 0 = j true`：于是 `m' 0` 既要等于 `inl 0`，又要等于 `inr true`，不可能。问题出在这两个内射的像**重叠**了，`Int` 无法分辨一个 `0` 是从哪儿来的：

```lean
theorem ch6 : ¬ ∃ m' : Int → Int ⊕ Bool, Sum.inl = m' ∘ Ch5.i ∧ Sum.inr = m' ∘ Ch5.j := by
  intro ⟨m', h₁, h₂⟩
  have e₁ := congrFun h₁ 0          -- inl 0 = m' (i 0) = m' 0
  have e₂ := congrFun h₂ true       -- inr true = m' (j true) = m' 0
  simp [Function.comp, Ch5.i, Ch5.j] at e₁ e₂
  rw [← e₂] at e₁                   -- inl 0 = inr true
  cases e₁                          -- 不同的构造子不可能相等
```

**第 7 题。** 这次 `i` 把负数原样送出、把非负数整体右移 2，于是 `0` 和 `1` 空了出来，恰好留给 `j`。两个内射的像**不重叠**，并且**合起来覆盖了全部整数**。
所以这次 `Int` 和 `Either` 一样好：两个方向都有分解态射，而且它们互逆——这对内射让 `Int` 也成了 `Int` 与 `Bool` 的一个余积（与 `Int ⊕ Bool` 同构）。

```lean
namespace Ch7

def i (n : Int) : Int := if n < 0 then n else n + 2
def j (b : Bool) : Int := if b then 0 else 1

/-- Either 比 Int 好：m 就是分解子。 -/
def m : Int ⊕ Bool → Int
  | .inl n => i n
  | .inr b => j b

/-- 反过来，Int 也比 Either 好：把整数“解码”回去。 -/
def m' (n : Int) : Int ⊕ Bool :=
  if n < 0 then .inl n
  else if n = 0 then .inr true
  else if n = 1 then .inr false
  else .inl (n - 2)

theorem m'_i : m' ∘ i = Sum.inl := by
  funext n
  simp only [Function.comp, m', i]
  by_cases h : n < 0
  · simp [h]                                  -- 负数：原样送回
  · have h0 : ¬ (n + 2 < 0) := by omega       -- omega 自动证明整数线性算术
    have h1 : n + 2 ≠ 0 := by omega
    have h2 : n + 2 ≠ 1 := by omega
    simp [h, h0, h1, h2]                      -- 非负数：(n + 2) - 2 = n

theorem m'_j : m' ∘ j = Sum.inr := by
  funext b
  cases b <;> rfl

/-- m' ∘ m = id：先编码再解码，回到原处。 -/
theorem m'_m : m' ∘ m = id := by
  funext s
  cases s with
  | inl n => exact congrFun m'_i n
  | inr b => exact congrFun m'_j b

end Ch7
```

（`omega` 是一个决策过程：只要目标是关于整数、自然数的线性等式或不等式，它就能自动证明。）

**第 8 题。** 给 `Int ⊕ Bool` 再加一点“垃圾”。比如 `c = Int ⊕ Bool ⊕ Unit`，内射是 `i = inl`、`j = inr ∘ inl`。
那个多出来的 `()` 不在任何内射的像里，所以分解态射可以把它送到任何地方——分解态射不唯一，`c` 就不可能比 `Either` 好：

```lean
namespace Ch8

abbrev C := Int ⊕ Bool ⊕ Unit

def i : Int → C := Sum.inl
def j : Bool → C := fun b => Sum.inr (Sum.inl b)

def m₁ : C → Int ⊕ Bool
  | .inl n => .inl n
  | .inr (.inl b) => .inr b
  | .inr (.inr ()) => .inl 0         -- 垃圾送到 inl 0

def m₂ : C → Int ⊕ Bool
  | .inl n => .inl n
  | .inr (.inl b) => .inr b
  | .inr (.inr ()) => .inr true      -- 垃圾送到 inr true

-- 两者都分解了 inl 和 inr……
example : Sum.inl = m₁ ∘ i ∧ Sum.inr = m₁ ∘ j := ⟨rfl, rfl⟩
example : Sum.inl = m₂ ∘ i ∧ Sum.inr = m₂ ∘ j := ⟨rfl, rfl⟩

-- ……但它们不相等
example : m₁ ≠ m₂ := by
  intro h
  have := congrFun h (.inr (.inr ()))
  simp [m₁, m₂] at this

end Ch8
```

另一个经典例子是 `Int` 配上 `i n = 2 * n`、`j b = if b then 1 else 3`：奇数里除了 `1` 和 `3` 都是“垃圾”，同样能被随意发送。
:::

## 参考文献

1. The Catsters，[Products and Coproducts](https://www.youtube.com/watch?v=upCSDIO9pjc) 视频。

## 本章小结

- **泛构造**的套路：先选一个**模式**（对象与态射组成的形状），在范畴中找出它的所有实例（候选者），再用态射给候选者**排名**，挑出“最好的”那个。
- **始对象**：到每个对象都有且只有一个态射；在 `Type` 中是 `Empty`。**终对象**：从每个对象都有且只有一个态射；在 `Type` 中是 `Unit`。“有且只有一个”= 存在 + 唯一，Lean 里分别对应一个定义和一个 `∀ f g, f = g` 形式的定理。
- **对偶**：把范畴中所有箭头反向得到**对偶范畴** $\mathcal{C}^{op}$。在 Lean 中，`Op C` 的定律直接由 `C` 的定律换个位置得到。每个构造都有一个“余”构造：终对象是对偶范畴中的始对象，余积是对偶范畴中的积。
- **同构**是一对互逆的态射。Lean 的 `structure Iso` 把“互逆”的证明也打包进了数据。泛构造给出的对象**在唯一同构意义下唯一**——我们用 Lean 证明了始对象和积都是如此。
- **积**：带两个投影的对象，任何候选者都能通过**唯一**的态射 $m$ 分解到它上面。在 `Type` 中是 `α × β`，分解子是 `fun x => (p x, q x)`；唯一性来自“二元组由两个分量决定”。
- **余积**：箭头反向。在 `Type` 中是不交并 `α ⊕ β`（Rust 的 `enum`），分解子是模式匹配；唯一性来自“每个值要么是 `inl`、要么是 `inr`”。
- **不对称性**：在 $\mathbf{Set}$ 中积像乘法、余积像加法；终对象能“挑出元素”，始对象不能。根源在于函数本身不对称：它们可以不满（嵌入），也可以不单（坍缩）。在 $\mathbf{Set}$ 中，同构就是双射。
- 偏序集中，积是最大下界（如 `min`），余积是最小上界（如 `max`）。
