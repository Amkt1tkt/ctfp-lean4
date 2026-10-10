# 3.1 一切皆关乎态射

如果读到这里，你还没有被我说服“范畴论说到底是关于态射的”，那只能怪我前面没讲好。接下来的主题是**伴随**（adjunction），
而伴随正是用 hom-集之间的同构来定义的。所以在动身之前，值得把我们对 hom-集——以及构成 hom-集的那些“砖块”——的直觉
重新梳理一遍。另外你会看到，伴随提供了一种更一般的语言，可以把前面学过的许多构造统一描述出来，因此顺手把那些构造也温习一下，
也会有帮助。

这一章是一次“回顾”：没有新定义，主要是换一个角度把旧东西重新看一遍。我们会在关键处用 Lean 把直觉钉牢。

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

end CTFP

open CTFP
```

## 函子

首先，你真的应该把函子首先想成**态射的映射**。Lean 的 `Functor` 类型类（和 Haskell 的一样）正是围绕这一点设计的：
它的核心成员是 `map`，把一个函数 `a → b` 变成 `F a → F b`。

```lean no-check
class Functor (f : Type u → Type v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α := ...
```

当然，函子也映射对象——也就是态射的两个端点。否则我们根本没法谈“保持复合”。对象的作用，是告诉我们哪些态射可以复合：
两个态射要想首尾相接，前一个的终点必须等于后一个的起点。所以，如果我们希望“复合的像”等于“像的复合”——也就是说，
先复合再**提升**（lift）与先提升再复合结果相同——那么端点该被映到哪里，几乎就已经被态射的映射决定了。

```diagram
a: (0, 0)
b: (1.5, 0)
c: (3, 0)
Fa: (0, 1.4) "F a"
Fb: (1.5, 1.4) "F b"
Fc: (3, 1.4) "F c"
f: a -> b
g: b -> c
gf: a -> c "g \circ f" bend=40
pad: (1.5, 2) ""
Ff: Fa -> Fb "F f"
Fg: Fb -> Fc "F g"
Fgf: Fa -> Fc "F(g \circ f)" bend=-40 side=right
path "先提升再复合：F g ∘ F f": Ff Fg
path "先复合再提升：F (g ∘ f)": Fgf color=green
caption: 下排是上排的像。F f 的终点和 F g 的起点必须都是 F b，两支提升后的箭头才能复合——对象的映射因此被“逼”出来了。
```

::: info 数学小课堂：什么叫“提升”
给定函子 $F$ 和态射 $f : a \to b$，态射 $F f : F a \to F b$ 叫作 $f$ 的**提升**（lifting）。
“提升”这个词形象地说出了发生的事：$f$ 原本在“底层”的对象 $a$、$b$ 之间，被函子整个抬到了“上层”的对象 $F a$、$F b$ 之间。
在 Lean 里，`Functor.map f` 就是 `f` 的提升；对列表来说，`List.map (· + 1)` 就是 `(· + 1)` 被提升到列表上的样子。
:::

Lean 的 `LawfulFunctor` 把“保持复合”写进了类型类里（字段 `comp_map`），所以对任何守法的函子，我们都能直接证明
“复合的提升 = 提升的复合”：

```lean
-- 对任意守法函子 F：map (g ∘ f) = map g ∘ map f
theorem lift_comp {F : Type → Type} [Functor F] [LawfulFunctor F] {a b c : Type}
    (f : a → b) (g : b → c) :
    Functor.map (f := F) (g ∘ f) = Functor.map g ∘ Functor.map f := by
  funext x            -- 两个函数相等，只需在每个输入 x 上相等
  exact comp_map f g x -- 这正是 LawfulFunctor 承诺的定律

-- 在具体的列表上，Lean 甚至能直接算出两边相同
example : List.map ((· + 1) ∘ (· * 2)) [1, 2, 3]
        = (List.map (· + 1) ∘ List.map (· * 2)) [1, 2, 3] := rfl
```

::: tip Rust 视角
`Option::map`、`Iterator::map`、`Result::map` 都是“提升”。Rust 不会替你检查
`opt.map(f).map(g) == opt.map(|x| g(f(x)))`，但你写代码时一直默默依赖着它——比如 Clippy 会建议你把两次 `map` 合并成一次，
它敢这么建议，正是因为函子定律成立。在 Lean 里，这条定律是一个可以 `exact` 出来的定理。
:::

## 交换图

态射的许多性质，都是用**交换图**（commuting diagram）来表述的。如果某个态射可以用不止一种方式写成其他态射的复合，
我们就得到了一张交换图：图上从同一起点到同一终点的不同路径，复合出来的是同一个态射。

特别地，交换图几乎是所有泛构造的基础（显著的例外是始对象和终对象，它们只涉及“存在唯一的箭头”）。
在积、余积、其他各种（余）极限、指数对象、自由幺半群等定义中，我们都见过它们的身影。

积是泛构造最简单的例子。我们挑两个对象 $a$ 和 $b$，然后看看有没有一个对象 $c$，连同一对态射 $p$ 和 $q$，
具有“作为它们的积”的泛性质。

![积的泛构造：给候选者排名](/img/3.1/productranking.jpg "积的泛构造：每一个“候选者”c（带着 p 和 q）都通过唯一的 m 分解到真正的积上。")

用交换图来画，泛性质说的是：对任何候选者 $c$，存在唯一的 $m$ 让下面两个三角形同时交换。

```diagram
c: (1, 0)
ab: (1, 1.5) "a \times b"
a: (-0.2, 2.6)
b: (2.2, 2.6)
m: c --> ab "m" pos=0.45
p: c -> a "p" bend=-35 side=right
q: c -> b "q" bend=35
fst: ab -> a "\mathit{fst}" side=right
snd: ab -> b "\mathit{snd}"
path "p": p
path "fst ∘ m": m fst color=green
path "q": q color=purple
path "snd ∘ m": m snd color=orange
caption: 积的泛性质：p = fst ∘ m，q = snd ∘ m。点按钮比较两条路径。
```

在 Lean 里，这个唯一的 $m$ 就是我们在 [1.5 积与余积](/part1/05-products-and-coproducts) 中见过的 `factorizer`。
两个三角形交换，对应两条定理；而且它们都是 `rfl`——Lean 展开定义就能看出两边一样：

```lean
def factorizer {c a b : Type} (p : c → a) (q : c → b) : c → a × b :=
  fun x => (p x, q x)

theorem fst_factorizer {c a b : Type} (p : c → a) (q : c → b) :
    Prod.fst ∘ factorizer p q = p := rfl
theorem snd_factorizer {c a b : Type} (p : c → a) (q : c → b) :
    Prod.snd ∘ factorizer p q = q := rfl

-- 唯一性：任何让两个三角形交换的 m，都只能是 factorizer p q
theorem factorizer_unique {c a b : Type} (p : c → a) (q : c → b)
    (m : c → a × b) (h1 : Prod.fst ∘ m = p) (h2 : Prod.snd ∘ m = q) :
    m = factorizer p q := by
  subst h1; subst h2  -- 用 m 的分量替换掉 p 和 q
  -- 剩下 m = fun x => ((m x).1, (m x).2)，这是积的 η 规则，定义上成立
  rfl
```

::: tip Lean 深入：`subst`
`subst h` 用于形如 `h : x = e`（或 `e = x`）且 `x` 是一个局部变量的假设：它把目标里所有的 `x` 都替换成 `e`，
然后丢掉 `x`。这里 `h1 : Prod.fst ∘ m = p`，于是 `p` 被处处换成 `Prod.fst ∘ m`。
:::

积是极限的一个特例。极限是用锥来定义的；而一般的锥是由一堆交换图搭起来的。这些图的交换性，可以换成“函子之间映射”的某个
自然性条件。这样一来，交换性就退居幕后，成了更高层语言——自然变换——底下的“汇编语言”。

## 自然变换

一般来说，每当我们需要一个“把态射映成交换方块”的映射时，自然变换就特别顺手。自然性方块的两条对边，分别是某个态射 $f$
在两个函子 $F$ 和 $G$ 下的像；另外两条边，则是自然变换的分量（它们本身也是态射）。

![自然性方块](/img/3.1/3_naturality.jpg "自然性方块：上下两边是 f 在 F、G 下的像，左右两边是自然变换的分量。")

```diagram
Fa: (0, 0) "F a"
Fb: (2, 0) "F b"
Ga: (0, 1.5) "G a"
Gb: (2, 1.5) "G b"
Ff: Fa -> Fb "F f"
Gf: Ga -> Gb "G f" side=right
aa: Fa -> Ga "\alpha_a" side=right
ab: Fb -> Gb "\alpha_b"
path "先 α_a 再 G f": aa Gf
path "先 F f 再 α_b": Ff ab color=green
caption: 自然性：G f ∘ α_a = α_b ∘ F f。无论先“横着走”还是先“竖着走”，到达的是同一个态射。
```

自然性的意思是：当你移到“相邻”的分量（所谓相邻，是指两个对象之间有态射相连）时，你既没有违背范畴的结构，也没有违背函子的结构。
先用自然变换的分量跨过两个对象之间的鸿沟、再用函子跳到邻居那里；还是反过来——结果都一样。这两个方向是**正交**的。
打个比方：自然变换让你左右移动，函子让你上下（或者前后）移动。你可以把一个函子的**像**想象成目标范畴里的一张“纸”；
自然变换则把 $F$ 对应的那张纸，映到 $G$ 对应的另一张纸上。

![函子的像是一张纸](/img/3.1/sheets.png "把函子的像想成目标范畴里的一张纸：自然变换把 F 的纸映到 G 的纸上。")

我们在编程中已经见过这种正交性。函子的作用是修改容器里的**内容**而不改变容器的**形状**；
自然变换则把原封不动的内容重新装进另一种容器。这两种操作的先后次序无关紧要。下面这个小实验让你亲手验证这一点：

<Ch3_1Orthogonality />

用 Lean 写出来，“取列表的第一个元素”是一个从 `List` 到 `Option` 的自然变换，它的自然性可以逐个情形地验证：

```lean
def headOpt {α : Type} : List α → Option α
  | [] => none
  | x :: _ => some x

-- 自然性方块：Option.map f ∘ headOpt = headOpt ∘ List.map f
theorem headOpt_natural {α β : Type} (f : α → β) (xs : List α) :
    Option.map f (headOpt xs) = headOpt (List.map f xs) := by
  -- 空列表和非空列表两种情形，各自展开定义就相同
  cases xs <;> rfl
```

::: tip Lean 深入：`cases` 与 `<;>`
`cases xs` 把列表 `xs` 拆成它的两种构造方式：`[]` 和 `x :: xs'`，产生两个子目标。
`t₁ <;> t₂` 的意思是“先执行 `t₁`，再对它产生的**每个**子目标执行 `t₂`”。所以 `cases xs <;> rfl` 就是“分情况，然后每种情况都用 `rfl` 收尾”。
:::

我们还见过：极限定义中的锥，可以换成自然变换。自然性保证了每个锥的各个侧面都交换。不过，极限是用锥**之间**的映射来定义的，
这些映射同样必须满足交换性条件。（例如，积的定义中那两个三角形必须交换。）

这些条件同样可以换成自然性。你也许还记得，**泛**锥——也就是极限——被定义为两个函子之间的自然变换。
第一个是（逆变的）hom-函子：

$$F :: c \to \mathcal{C}(c, \mathrm{Lim}\, D)$$

第二个是（同样逆变的）函子，它把 $\mathcal{C}$ 中的对象映到锥，而锥本身又是自然变换：

$$G :: c \to \mathrm{Nat}(\Delta_c, D)$$

这里 $\Delta_c$ 是常函子，$D$ 是在 $\mathcal{C}$ 中定义“图”的那个函子。$F$ 和 $G$ 对 $\mathcal{C}$ 中的态射都有定义良好的作用。
而恰好，$F$ 与 $G$ 之间的这个特定的自然变换是一个**同构**。

::: info 数学小课堂：为什么这两个函子是“逆变”的
设 $h : c' \to c$。给你一个从 $c$ 出发的箭头 $m : c \to \mathrm{Lim}\, D$，你可以先走 $h$ 再走 $m$，得到 $m \circ h : c' \to \mathrm{Lim}\, D$。
注意方向：$h$ 从 $c'$ 指向 $c$，而诱导出的映射却从 $\mathcal{C}(c, \mathrm{Lim}\, D)$ 指向 $\mathcal{C}(c', \mathrm{Lim}\, D)$——**方向反了**。
这就是“逆变”。锥也一样：以 $c$ 为顶点的锥，前面接上 $h$，就成了以 $c'$ 为顶点的锥。

以积为例（此时 $D$ 选出两个对象 $a$、$b$）：以 $c$ 为顶点的锥就是一对箭头 $(p, q)$，即 `(c → a) × (c → b)`；
而 $\mathcal{C}(c, \mathrm{Lim}\, D)$ 就是 `c → a × b`。上面的 `factorizer` 和“分别后接 `fst`、`snd`”正是这两者之间互逆的映射。
:::

## 自然同构

**自然同构**（natural isomorphism）是每个分量都可逆的自然变换。它是范畴论里说“两样东西是一样的”的方式。
这种变换的每个分量都必须是对象之间的同构——一个有逆的态射。如果你把函子的像想象成纸张，那么自然同构就是两张纸之间
一一对应、可以反向撤销的映射。

举个 Lean 的例子：`Option α` 和 `Unit ⊕ α` 携带的信息完全一样（“要么什么都没有，要么有一个 `α`”）。
它们之间有一对互逆的函数，而且这对函数对 `α` 是自然的：

```lean
def toSum {α : Type} : Option α → Unit ⊕ α
  | none => .inl ()
  | some x => .inr x

def ofSum {α : Type} : Unit ⊕ α → Option α
  | .inl () => none
  | .inr x => some x

-- 两个方向互逆：每个分量都是同构
theorem ofSum_toSum {α : Type} (o : Option α) : ofSum (toSum o) = o := by
  cases o <;> rfl
theorem toSum_ofSum {α : Type} (s : Unit ⊕ α) : toSum (ofSum s) = s := by
  rcases s with ⟨⟩ | x <;> rfl

-- 自然性：先 map 再换容器 = 先换容器再 map
theorem toSum_natural {α β : Type} (f : α → β) (o : Option α) :
    Sum.map id f (toSum o) = toSum (Option.map f o) := by
  cases o <;> rfl
```

::: tip Lean 深入：`rcases`
`rcases s with ⟨⟩ | x` 是 `cases` 的“带花样”版本：`|` 分隔各个构造子的情形，`⟨⟩` 表示把 `Unit` 的唯一值 `()` 也一并拆开。
它在需要一口气拆好几层时非常方便。
:::

## Hom-集

那么，态射究竟是什么？态射确实比对象有更多的结构：和对象不同，态射有两个端点。可是，一旦你固定了起点对象和终点对象，
它们之间的态射就构成了一个平淡无奇的集合（至少在局部小范畴里是这样）——这就是 **hom-集**（hom-set），即“从 $a$ 到 $b$ 的态射集合”，
记作 $\mathcal{C}(a, b)$。我们可以给这个集合里的元素起名字，比如 $f$、$g$，以便区分它们——但说到底，究竟是什么让它们不同呢？

同一个 hom-集里的态射之间的本质区别，在于它们与其他态射（来自首尾相接的那些 hom-集）复合的方式。如果存在一个态射 $h$，
它与 $f$ 的复合（前复合或后复合皆可）不同于与 $g$ 的复合，例如：

$$h \circ f \neq h \circ g$$

那我们就能直接“观察”到 $f$ 和 $g$ 的区别。

```lean
-- 在 Bool → Bool 中，not 与 id 是不同的态射。
-- 用常函数 h = fun _ => true 去“观察”，看不出区别：
example : (fun _ => true : Bool → Bool) ∘ not = (fun _ => true) ∘ id := rfl
-- 换一个观察者 h = id，区别就暴露了：
example : id ∘ not ≠ id ∘ (id : Bool → Bool) := by
  intro h                       -- 假设两者相等……
  have := congrFun h true       -- ……那么在输入 true 上也相等：not true = true
  simp at this                  -- 化简得 false = true，矛盾
```

不过，即使区别不能被直接观察到，我们也可以用函子把这个 hom-集“放大”来看。函子 $F$ 可能把这两个态射映成更丰富的范畴中
两个不同的态射：

$$F f \neq F g$$

在那个范畴里，首尾相接的 hom-集提供了更高的“分辨率”，例如：

$$h' \circ F f \neq h' \circ F g$$

其中 $h'$ 并不在 $F$ 的像里。

::: tip Lean 深入：在 Type 中，“点”就足以区分一切
在类型与函数的范畴中，观察者不用找得太辛苦：从单元素类型 `Unit` 出发的箭头 `x : Unit → a` 恰好对应 `a` 的一个元素（一个“点”），
而只要用所有的点去前复合，就能把任何两个不同的函数区分开。这正是函数外延性（`funext`）的范畴论说法：

```lean
theorem points_separate {a b : Type} (f g : a → b)
    (h : ∀ x : Unit → a, f ∘ x = g ∘ x) : f = g := by
  funext y                                -- 只需在每个 y : a 上相等
  -- 选“点” x = fun _ => y，在 () 处取值
  exact congrFun (h (fun _ => y)) ()
```

具有这种性质的范畴叫作“良点的”（well-pointed）。一般的范畴没有这么好的性质，所以才需要上面说的“借助函子放大”。
:::

## Hom-集同构

许多范畴论构造都依赖于 hom-集之间的同构。但是 hom-集只是集合，两个集合之间光秃秃的同构说明不了多少东西。对有限集合来说，
同构只意味着它们元素个数相同；对无限集合，则是它们的基数相同。任何**有意义**的 hom-集同构，都必须考虑到复合。而复合牵涉到不止一个
hom-集。我们需要定义横跨一整批 hom-集的同构，并且要求它满足一些与复合相容的条件。**自然**同构恰好满足这个要求。

::: info 数学小课堂：“光秃秃的同构”有多廉价
`Bool → Bool` 有 4 个元素，`Bool × Bool` 也有 4 个元素，所以它们之间有 $4! = 24$ 个双射。其中大多数是随手乱配的，毫无意义。
真正“有意义”的那一个，是把函数 `f` 送到 `(f false, f true)`；它的特殊之处在于它和复合相容：你在函数后面接一个 `k`，
在对子这边就相当于对两个分量各做一次 `k`。“相容”这件事，就是下面要说的自然性。
:::

可是，hom-集的自然同构是什么意思呢？自然性是函子之间映射的性质，而不是集合之间映射的性质。所以我们真正谈论的，
是取值为 hom-集的函子之间的自然同构。这些函子不只是一般的“取值为集合的函子”：它们对态射的作用，是由相应的 hom-函子诱导出来的。
hom-函子用前复合或后复合（取决于函子的协变性）以一种典范的方式映射态射：

```lean
-- 协变的 hom-函子 C(a, -)：沿 k 后复合
def postcomp {a b b' : Type} (k : b → b') : (a → b) → (a → b') :=
  fun f => k ∘ f
-- 逆变的 hom-函子 C(-, b)：沿 h 前复合（注意方向反了）
def precomp {a a' b : Type} (h : a' → a) : (a → b) → (a' → b) :=
  fun f => f ∘ h
```

米田嵌入（Yoneda embedding）就是这样一个同构的例子。它把 $\mathcal{C}$ 中的 hom-集映到函子范畴中的 hom-集，并且是自然的。
米田嵌入中的一个函子是 $\mathcal{C}$ 中的 hom-函子，另一个则把对象映到 hom-集之间的自然变换的集合。

极限的定义同样是 hom-集之间的自然同构（第二个 hom-集同样位于函子范畴中）：

$$\mathcal{C}(c, \mathrm{Lim}\, D) \simeq \mathrm{Nat}(\Delta_c, D)$$

事实上，我们对指数对象的构造、对自由幺半群的构造，也都可以改写成 hom-集之间的自然同构。

这并非巧合——下一章我们就会看到，这些都只是**伴随**的不同例子，而伴随正是用 hom-集的自然同构来定义的。

先偷看一眼：指数对象的泛构造，说的就是 `z × a → b` 与 `z → (a → b)` 之间的一一对应（柯里化）。
下面这条定理说的是，这个对应对 `z` 是自然的——先在 `z` 这一侧沿 `h` 前复合再柯里化，等于先柯里化再前复合 `h`。证明只需 `rfl`：

```lean
theorem curry_natural {z z' a b : Type} (h : z' → z) (f : z × a → b) :
    Function.curry (f ∘ (fun p => (h p.1, p.2)))
      = Function.curry f ∘ h := rfl
```

## Hom-集的不对称性

还有一个观察能帮助我们理解伴随。hom-集一般来说是**不对称**的：hom-集 $\mathcal{C}(a, b)$ 往往和 $\mathcal{C}(b, a)$ 截然不同。
这种不对称性最极致的展示，就是把偏序看作范畴。在偏序中，从 $a$ 到 $b$ 的态射存在，当且仅当 $a$ 小于或等于 $b$。
如果 $a$ 和 $b$ 不同，那就不可能还有反方向、从 $b$ 到 $a$ 的态射。所以，如果 hom-集 $\mathcal{C}(a, b)$ 非空（在这里意味着它是单元素集合），
那么除非 $a = b$，否则 $\mathcal{C}(b, a)$ 一定是空的。这个范畴里的箭头有着确定的、朝一个方向的“流向”。

预序所基于的关系不一定是反对称的，所以除了偶尔出现的环，它也“基本上”是有方向的。把任意一个范畴想成预序的推广，是很方便的。

预序是一种瘦范畴——所有的 hom-集要么是单元素集合，要么是空集。我们可以把一般的范畴想象成一个“厚的”预序。

<Ch3_1HomSetAsymmetry />

用 Lean 可以把“自然数的 ≤ 是一个瘦范畴”原原本本地写出来。态射 $a \to b$ 就是“$a \le b$ 的证明”。
证明是命题（`Prop`）里的东西，而 `Category` 要求 hom 是一个 `Type`，所以我们用 `PLift` 把它包一层：

```lean
structure NatLE where
  n : Nat

instance : Category NatLE where
  Hom a b := PLift (a.n ≤ b.n)               -- 态射 = “a ≤ b”的一个证明
  id a := ⟨Nat.le_refl a.n⟩                   -- 恒等态射：自反性 a ≤ a
  comp g f := ⟨Nat.le_trans f.down g.down⟩    -- 复合：传递性
  -- 三条定律由默认的 `by intros; rfl` 自动完成：同一命题的两个证明在定义上相等

-- 瘦：同一个 hom-集里的任意两个态射都相等
theorem thin {a b : NatLE} (f g : a ⟶ b) : f = g := by
  cases f; cases g; rfl

-- 不对称：3 ⟶ 5 有态射，5 ⟶ 3 一个也没有
example : (⟨3⟩ : NatLE) ⟶ ⟨5⟩ := ⟨by decide⟩
example : ((⟨5⟩ : NatLE) ⟶ ⟨3⟩) → False := fun f => absurd f.down (by decide)

-- 偏序（反对称）：两个方向都有箭头，只能是同一个对象
theorem antisymm_hom {a b : NatLE} (f : a ⟶ b) (g : b ⟶ a) : a = b := by
  cases a; cases b
  congr
  exact Nat.le_antisymm f.down g.down
```

::: tip Lean 深入：`PLift` 与证明无关性
`PLift p` 把一个命题 `p : Prop` 提升成一个类型：它的元素是 `⟨h⟩`，其中 `h : p`；用 `.down` 取回证明。
Lean 有一条内建规则叫**证明无关性**（proof irrelevance）：同一命题的任意两个证明在定义上相等。
所以 `thin` 的证明里，拆开后的 `⟨h₁⟩ = ⟨h₂⟩` 直接 `rfl` 就成立——“瘦”在 Lean 里几乎是免费的。
:::

::: tip Rust 视角
Rust 的 trait 解析里也有类似的“瘦”结构：`T: Into<U>` 要么成立、要么不成立，你从不关心它是“哪一个”证明。
而函数类型 `fn(A) -> B` 则是“厚”的：同一对类型之间可以有无数个不同的函数。
:::

## 挑战

1. 考虑自然性条件的几种退化情形，并画出相应的图。例如，如果函子 $F$ 或 $G$ 把 $a$ 和 $b$ 两个对象（即 $f : a \to b$ 的两端）
   映到同一个对象，比如 $F a = F b$ 或 $G a = G b$，会发生什么？（注意，这样你会得到一个锥或余锥。）
   然后考虑 $F a = G a$ 或 $F b = G b$ 的情形。最后，如果你从一个自环态射 $f : a \to a$ 出发，又会怎样？

::: details 参考答案
**情形一：$F a = F b$（记为 $x$），且 $F f = \mathrm{id}_x$。** 方块的上边塌缩成一个点，方块变成了一个三角形：

```diagram
x: (1, 0) "x"
Ga: (0, 1.5) "G a"
Gb: (2, 1.5) "G b"
aa: x -> Ga "\alpha_a" side=right
ab: x -> Gb "\alpha_b"
Gf: Ga -> Gb "G f" side=right
path "G f ∘ α_a": aa Gf
path "α_b": ab color=green
caption: F 把 a、b 都映到 x（F f 是恒等）：自然性变成 G f ∘ α_a = α_b——这正是一个以 x 为顶点的锥的一面。
```

当 $F$ 是常函子 $\Delta_x$ 时，所有分量从同一个顶点 $x$ 出发，自然性条件说的恰好是“锥的每个侧面都交换”。

（如果 $F a = F b$ 但 $F f$ 不是恒等态射，而是 $x$ 上的某个自环 $e$，那么条件是 $G f \circ \alpha_a = \alpha_b \circ e$，图里多一个自环。）

**情形二：$G a = G b$（记为 $y$），且 $G f = \mathrm{id}_y$。** 对偶地，下边塌缩，得到 $\alpha_a = \alpha_b \circ F f$：所有分量汇聚到同一个点 $y$，
这是一个**余锥**（cocone）的一面。

```diagram
Fa: (0, 0) "F a"
Fb: (2, 0) "F b"
y: (1, 1.5) "y"
Ff: Fa -> Fb "F f"
aa: Fa -> y "\alpha_a" side=right
ab: Fb -> y "\alpha_b"
path "α_a": aa
path "α_b ∘ F f": Ff ab color=green
caption: G 把 a、b 都映到 y：自然性变成 α_a = α_b ∘ F f——余锥的一面。
```

**情形三：$F a = G a$。** 如果分量 $\alpha_a$ 恰好是恒等态射，左边塌缩，条件变成 $G f = \alpha_b \circ F f$：
$G f$ 可以分解为“先 $F f$ 再 $\alpha_b$”。同理，$F b = G b$ 且 $\alpha_b = \mathrm{id}$ 时，条件变成 $G f \circ \alpha_a = F f$。
（如果 $\alpha_a$ 只是 $F a = G a$ 上的某个自同态而非恒等，方块不塌缩，只是左边变成一个自环。）

**情形四：自环 $f : a \to a$。** 此时方块的上下两边都是自环：$F f : F a \to F a$，$G f : G a \to G a$，
而左右两边是同一个分量 $\alpha_a$。自然性条件是 $G f \circ \alpha_a = \alpha_a \circ F f$：分量 $\alpha_a$ “交换”了两个自环——
用代数的话说，$\alpha_a$ 是一个**等变映射**（intertwiner）。

```diagram
Fa: (0, 0) "F a"
Ga: (2, 0) "G a"
aa: Fa -> Ga "\alpha_a"
Ff: Fa -> Fa "F f" loop=left
Gf: Ga -> Ga "G f" loop=right
caption: 自环的自然性：α_a ∘ F f = G f ∘ α_a。
```

在 Lean 中，`List.reverse` 与“对列表中每个元素取反”这个自环 `List.map not : List Bool → List Bool` 就是一例：

```lean
example (xs : List Bool) :
    List.reverse (List.map not xs) = List.map not (List.reverse xs) := by
  simp [List.map_reverse]
```
:::

## 本章小结

- 函子首先是**态射的映射**（`Functor.map`）；对象的映射几乎被“保持复合”这一要求逼了出来。
- 交换图表达“同一个态射有多种分解方式”，是几乎所有泛构造的基础；在 Lean 里，它们常常就是 `rfl` 能证明的等式。
- 自然变换把态射映成交换方块。直观上：函子改内容、不动形状；自然变换换容器、不看内容——两者正交，先后无关。
- 极限、锥及锥之间的映射，都可以用自然性来表述；极限是 $\mathcal{C}(c, \mathrm{Lim}\, D) \simeq \mathrm{Nat}(\Delta_c, D)$。
- 自然同构是每个分量都可逆的自然变换，是范畴论中“二者相同”的说法。
- 同一 hom-集中的态射，靠与其他态射的复合方式来区分；必要时可以用函子“放大”。在 Type 中，“点”就足以区分一切函数。
- 光秃秃的集合同构只比较大小；有意义的 hom-集同构必须是**自然**的。米田嵌入、极限、指数、自由幺半群都是这种同构——它们都是伴随。
- hom-集通常不对称。偏序是最极端的例子（瘦范畴）；一般范畴可以想成“厚的预序”。
