# 2.2 极限与余极限

```lean hidden
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

namespace CTFP

/-- 范畴：对象 + 态射 + 复合 + 恒等，满足单位律与结合律。 -/
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

structure CFunctor (C : Type u₁) [Category.{u₁, v₁} C] (D : Type u₂) [Category.{u₂, v₂} D] where
  obj : C → D
  map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id : ∀ (a : C), map (𝟙 a) = 𝟙 (obj a)
  map_comp : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c), map (g ⊚ f) = map g ⊚ map f

structure NatTrans {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    (F G : CFunctor C D) where
  app : (a : C) → (F.obj a ⟶ G.obj a)
  naturality : ∀ {a b : C} (f : a ⟶ b), G.map f ⊚ app a = app b ⊚ F.map f

infixr:50 " ⟹ " => NatTrans

end CTFP

open CTFP Category
```

在范畴论里，似乎什么东西都和别的什么东西有关系，而且每样东西都能从好几个角度去看。就拿[积](/part1/05-products-and-coproducts)的泛构造来说吧。现在我们已经懂了[函子](/part1/07-functors)和[自然变换](/part1/10-natural-transformations)，能不能把这个构造说得更简单、甚至推广得更一般？我们来试试。

::: info 数学小课堂：先回顾一下积是怎么来的
在 1.5 节里，我们是这样“找出”两个对象 $a$ 和 $b$ 的积的：

1. 先**选定**两个对象 $a$、$b$；
2. 考虑所有**候选者**：一个对象 $c$，外加两个态射 $p : c \to a$、$q : c \to b$（两条“投影”）；
3. 给候选者**排名**：如果存在态射 $m : c' \to c$，使得 $p' = p \circ m$、$q' = q \circ m$，就说 $c$ 比 $c'$ “更好”——$c'$ 的两条投影可以先走 $m$、再走 $c$ 的投影得到；
4. **最好的那个**候选者（所有别的候选者都能*唯一地*经由它分解）就是积 $a \times b$。

在 Lean 里，$a \times b$ 就是 `a × b`，两条投影是 `Prod.fst` 和 `Prod.snd`。对任意候选者 `(c, p, q)`，那个唯一的 $m$ 就是 `fun x => (p x, q x)`。

本章要做的事情是：把“选定两个对象”“候选者”“排名”“最好的”这几个词，全部换成函子与自然变换的语言。换完之后你会发现，积只是一个巨大家族——**极限**——里最简单的成员之一。
:::

![积的模式：两个对象 a 与 b](/img/2.2/productpattern.jpg "积的构造从“选两个对象”开始。")

构造积的第一步，是选定两个对象 $a$ 和 $b$——我们要构造的就是它们的积。可是“选定对象”到底是什么意思？能不能用更“范畴”的方式来说这件事？两个对象构成了一个模式（pattern）——一个非常简单的模式。我们可以把这个模式抽象成一个范畴：一个非常简单的范畴，但毕竟是个范畴。我们把它叫作 $\mathbf{2}$。它只有两个对象 $1$ 和 $2$，除了两条必不可少的恒等态射之外，再没有别的态射。这样一来，“在 $\mathcal{C}$ 中选定两个对象”就可以改说成：定义一个从范畴 $\mathbf{2}$ 到 $\mathcal{C}$ 的函子 $D$。函子把对象映到对象，所以它的像就是两个对象（也可能只有一个——如果函子把两个对象压到了一起，这也完全没问题）。函子还要映射态射——在这里，它只是把恒等态射映到恒等态射。

这种做法的妙处在于：它完全建立在范畴论的概念之上，摆脱了“选几个对象”这种直接从我们狩猎采集时代的祖先那里继承来的、含糊不清的说法。而且顺带一提，它也很容易推广，因为没有任何东西能阻止我们用比 $\mathbf{2}$ 更复杂的范畴来定义模式。

![范畴 2 经函子 D 映到范畴 C](/img/2.2/two.jpg "函子 D 把范畴 2 的两个对象送到 C 中的 a 和 b。")

::: tip Lean 深入：把“只有恒等态射的范畴”写出来
像 $\mathbf{2}$ 这样“除了恒等态射什么都没有”的范畴叫作**离散范畴**（discrete category）。任何一个类型 `α` 都能变成一个离散范畴：对象就是 `α` 的元素，从 `a` 到 `b` 的态射只在 `a` 和 `b` 是同一个元素时才有（而且只有一条）。

在 Lean 里，“只在 `a = b` 时才有元素”可以用一个**索引归纳类型**（indexed inductive type）精确表达：`DHom a b` 只有一个构造子 `refl a : DHom a a`，它的两个索引被强制相同。对它做 `match`/`cases` 时，Lean 会自动知道 `a` 和 `b` 是同一个东西——这叫**依值模式匹配**（dependent pattern matching），Rust 的 `match` 做不到这一点。

`Discrete α` 只是 `α` 的一个别名（和 Prelude 里的 `Op` 同一个套路），用来挂上一个不同的范畴实例。
:::

```lean
/-- 离散范畴的态射：只有恒等态射。 -/
inductive DHom {α : Type} : α → α → Type
  | refl (a : α) : DHom a a

def Discrete (α : Type) : Type := α

instance discreteCategory (α : Type) : Category.{0, 0} (Discrete α) where
  Hom a b := DHom (α := α) a b
  id a := DHom.refl a
  -- 两条态射都只能是 refl，复合自然还是 refl
  comp g f := match g, f with
    | .refl _, .refl _ => .refl _
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

/-- 范畴 2 的两个对象。 -/
inductive Two | one | two
```

从离散范畴出发的函子特别好造：只需说清每个对象映到哪里，恒等态射只能映到恒等态射。

```lean
/-- 从离散范畴到 Type 的图：只要给出每个对象映到哪个类型。 -/
def discreteDiagram {α : Type} (F : α → Type) : CFunctor (Discrete α) Type where
  obj := F
  map f := match f with
    | .refl _ => fun x => x
  map_id _ := rfl
  map_comp f g := by cases f; cases g; rfl

/-- 函子 D : 2 → Type，把 1 送到 a，把 2 送到 b —— 也就是“选定 a 和 b”。 -/
def pairDiagram (a b : Type) : CFunctor (Discrete Two) Type :=
  discreteDiagram fun | .one => a | .two => b
```

我们继续。积的定义的下一步，是选出候选对象 $c$。同样，我们可以把这次“选择”改说成一个从单对象范畴出发的函子。事实上，如果我们用的是 Kan 扩张，这才是正确的做法。但我们还没准备好讲 Kan 扩张，所以这里换一个技巧：用一个同样从 $\mathbf{2}$ 到 $\mathcal{C}$ 的**常函子** $\Delta$。在 $\mathcal{C}$ 中选出 $c$，可以用 $\Delta_c$ 来完成。还记得吧，$\Delta_c$ 把所有对象都映到 $c$，把所有态射都映到 $\mathrm{id}_c$。

![常函子 Δc 把范畴 2 整个压到 c 上](/img/2.2/twodelta.jpg "常函子 Δc：两个对象都被送到 c，恒等态射被送到 c 上的恒等态射。")

```lean
section Limits
variable {I : Type u₁} [Category.{u₁, v₁} I] {C : Type u₂} [Category.{u₂, v₂} C]

/-- 常函子 Δ c : I → C —— 所有对象都送到 c，所有态射都送到 𝟙 c。 -/
@[reducible] def Δ (c : C) : CFunctor I C where
  obj _ := c
  map _ := 𝟙 c
  map_id _ := rfl
  -- 𝟙 c = 𝟙 c ⊚ 𝟙 c，正是左单位律反过来读
  map_comp _ _ := (Category.id_comp (𝟙 c)).symm
```

::: tip Lean 深入：`variable` 与 `@[reducible]`
- `section ... end` 配合 `variable`，可以一次性声明一批“这一节里的所有定义都要用到的参数”。下面每个定义都会自动带上 `{I : Type u₁} [Category I] {C : Type u₂} [Category C]`，省得反复写。Rust 里没有直接对应物，最接近的是在 `impl<I, C> ...` 块上统一写泛型参数。
- 这里第一次需要 `Type u₁`、`Type u₂` 这样的**宇宙变量**：因为我们要讨论“任意范畴”，而 `Type` 本身作为范畴（对象是类型）就住在 `Type 1` 里。如果只写 `Type`，就没法把 `Type` 本身当作 `C` 代进来了。
- `@[reducible]` 告诉 Lean：做类型检查和改写时可以随手把 `Δ c` 展开。这样 `(Δ c).obj i` 会被直接看成 `c`，`(Δ c).map f` 会被看成 `𝟙 c`。不加的话，后面的 `rw` 会因为“看起来不一样”而失败。
:::

现在我们有两个函子 $\Delta_c$ 和 $D$，都是从 $\mathbf{2}$ 到 $\mathcal{C}$，所以很自然地会问：它们之间有没有自然变换？因为 $\mathbf{2}$ 里只有两个对象，一个自然变换就只有两个分量。$\mathbf{2}$ 中的对象 $1$ 被 $\Delta_c$ 映到 $c$，被 $D$ 映到 $a$。所以从 $\Delta_c$ 到 $D$ 的自然变换在 $1$ 处的分量，是一个从 $c$ 到 $a$ 的态射，我们叫它 $p$。类似地，第二个分量是从 $c$ 到 $b$（对象 $2$ 在 $D$ 下的像）的态射 $q$。这不正是我们当初定义积时用的那两条投影吗！所以，与其说“选定对象和投影”，不如直接说“选定函子和自然变换”。碰巧的是，在这个简单的例子里，自然性条件自动满足，因为 $\mathbf{2}$ 里除了恒等态射没有别的态射。

![积的锥：从 c 到 a、b 的两条腿 p、q](/img/2.2/productcone.jpg "从 Δc 到 D 的自然变换，两个分量正是两条投影 p 和 q。")

```diagram
c: (1, 0) "c"
a: (0, 1.3) "a = D\,1"
b: (2, 1.3) "b = D\,2"
p: c -> a "p = \alpha_1" side=right
q: c -> b "q = \alpha_2"
caption: 范畴 2 上的锥：顶点 c，两条腿就是两条“投影”。
```

把这个构造推广到 $\mathbf{2}$ 以外的范畴——比如说含有非平凡态射的范畴——时，$\Delta_c$ 和 $D$ 之间的变换就要受自然性条件的约束了。我们把这样的变换叫作**锥**（cone），因为 $\Delta$ 的像是一个圆锥（或者说金字塔）的顶点，而锥的侧面由自然变换的各个分量构成；$D$ 的像则构成锥的底面。

一般来说，要造一个锥，我们先找一个定义模式的范畴 $\mathcal{I}$。它是一个小范畴，通常是有限的。我们挑一个从 $\mathcal{I}$ 到 $\mathcal{C}$ 的函子 $D$，把它（或者它的像）叫作一个**图**（diagram）。我们在 $\mathcal{C}$ 中选某个 $c$ 作为锥的顶点，并用它定义从 $\mathcal{I}$ 到 $\mathcal{C}$ 的常函子 $\Delta_c$。于是，从 $\Delta_c$ 到 $D$ 的一个自然变换就是我们的锥。对于有限的 $\mathcal{I}$，它不过是把 $c$ 连到图（$\mathcal{I}$ 在 $D$ 下的像）上的一束态射。

::: info 数学小课堂：“图”这个词在这里是什么意思
日常说“图”，是指一张画。范畴论里的**图**（diagram）是一个严格的东西：**一个函子 $D : \mathcal{I} \to \mathcal{C}$**。

- $\mathcal{I}$ 叫**索引范畴**（index category），它只负责提供“形状”：有几个点、点之间有哪些箭头；
- $D$ 负责把这个形状“画”进 $\mathcal{C}$ 里：每个点画成 $\mathcal{C}$ 中的一个对象，每条箭头画成 $\mathcal{C}$ 中的一个态射，而且要尊重复合。

打个比方：$\mathcal{I}$ 像是 Rust 里的一个泛型 `struct` 的“字段布局”，$D$ 则是一次具体的实例化。“形状为 $\bullet \to \bullet \leftarrow \bullet$ 的图”就是三个对象加两个指向同一个对象的态射。本章所有极限，区别只在于用了什么形状的 $\mathcal{I}$。
:::

![一般的锥：I 的像构成底面，c 是顶点](/img/2.2/cone.jpg "一般的锥：I 经 D 映为 C 中的图（锥的底面），常函子 Δc 把一切送到顶点 c，自然变换的分量构成锥的侧棱。")

```lean
/-- 以 c 为顶点、以图 D 为底的锥 = 从常函子 Δ c 到 D 的自然变换。 -/
abbrev Cone (c : C) (D : CFunctor I C) := (Δ c : CFunctor I C) ⟹ D
```

自然性要求这个图里所有的三角形（金字塔的各个侧面）都交换。确实如此：取 $\mathcal{I}$ 中任意一个态射 $f$。函子 $D$ 把它映成 $\mathcal{C}$ 中的态射 $D f$，这个态射构成某个三角形的底边。常函子 $\Delta_c$ 则把 $f$ 映到 $c$ 上的恒等态射。$\Delta$ 把态射的两端捏成了同一个对象，于是自然性方块就塌缩成了一个交换三角形。这个三角形的两条腰，就是自然变换的两个分量。

![自然性方块塌缩成交换三角形](/img/2.2/conenaturality.jpg "常函子把 f 的两端捏到同一个顶点 c，自然性方块变成了交换三角形。")

```diagram
c: (1, 0) "c"
Di: (0, 1.4) "D\,i"
Dj: (2, 1.4) "D\,j"
ai: c -> Di "\alpha_i" side=right
aj: c -> Dj "\alpha_j"
Df: Di -> Dj "D f" side=right
path "先 α_i 再 D f": ai Df
path "直接走 α_j": aj color=green
caption: 锥的一个侧面：对 I 中每个 f : i → j，都有 D f ∘ α_i = α_j。
```

在 Lean 里，这正是把自然性方块里的 `(Δ c).map f` 换成 `𝟙 c`，再用一次右单位律：

```lean
/-- 锥的每个侧面都交换：D.map f ⊚ α_i = α_j。 -/
theorem Cone.comm {c : C} {D : CFunctor I C} (α : Cone c D) {i j : I} (f : i ⟶ j) :
    D.map f ⊚ α.app i = α.app j := by
  -- 自然性方块：D.map f ⊚ α_i = α_j ⊚ (Δ c).map f，而 (Δ c).map f 就是 𝟙 c
  rw [α.naturality f]
  exact Category.comp_id (α.app j)
```

回到范畴 $\mathbf{2}$：Lean 可以帮我们确认，以 `a × b` 为顶点、以两条投影为腿，确实构成 `pairDiagram a b` 上的一个锥。这里的自然性条件只涉及恒等态射，逐个检查即可：

```lean
/-- 把锥和它的顶点打包在一起。 -/
structure ConeOver (D : CFunctor I C) where
  apex : C
  leg : Cone apex D

end Limits

/-- 积 a × b 连同两条投影，是范畴 2 上的一个锥。 -/
def productCone (a b : Type) : ConeOver (pairDiagram a b) where
  apex := a × b
  leg := {
    app := fun | .one => Prod.fst | .two => Prod.snd
    naturality := fun {i _} f => match i, f with
      | .one, .refl _ => rfl
      | .two, .refl _ => rfl }
```

好，这就是一个锥。我们真正关心的是**泛锥**（universal cone）——就像在积的定义里我们挑出了一个泛对象一样。

做法有很多。比如说，我们可以针对给定的函子 $D$ 定义一个**锥范畴**（category of cones）。这个范畴的对象就是锥。不过要注意，并不是 $\mathcal{C}$ 中每个对象 $c$ 都能当锥的顶点，因为 $\Delta_c$ 和 $D$ 之间可能根本没有自然变换。

要让它成为一个范畴，还得定义锥与锥之间的态射。这些态射完全由锥顶点之间的态射决定。但并不是随便哪个态射都可以。回想一下，在积的构造里，我们要求候选对象（顶点）之间的态射必须是投影的公共因子。例如：

```diagram
c2: (0, 0) "c'"
c: (1.5, 0.9) "c"
a: (0.5, 2) "a"
b: (2.6, 2) "b"
m: c2 -> c "m" dashed
p2: c2 -> a "p'" side=right
q2: c2 -> b "q'" bend=10
p: c -> a "p"
q: c -> b "q"
path "p'": p2
path "p ∘ m": m p color=green
path "q'": q2 color=orange
path "q ∘ m": m q color=purple
caption: 积的排名：p' = p ∘ m，q' = q ∘ m。m 是两条投影的公共因子。
```

![积的排名](/img/2.2/productranking.jpg "c' 的两条投影都经由 m 分解为 c 的投影：c 是更好的候选者。")

推广到一般情形，这个条件就变成：所有以分解态射为一边的三角形都要交换。

![两个锥之间的交换三角形](/img/2.2/conecommutativity.jpg "连接两个锥的交换三角形，h 是分解态射（这里下面那个锥是泛锥，顶点为 Lim D）。")

```diagram
c2: (0, 0) "c'"
L: (1.6, 0.6) "c"
Di: (0.8, 1.9) "D\,i"
h: c2 -> L "h" dashed
a2: c2 -> Di "\alpha'_i" side=right
a: L -> Di "\alpha_i"
path "α'_i": a2
path "α_i ∘ h": h a color=green
caption: 锥态射 h：对 I 中每个对象 i，都有 α_i ∘ h = α'_i。
```

我们就把这些分解态射取作锥范畴中的态射。很容易验证这些态射确实可以复合，恒等态射也确实是一个分解态射。所以，锥构成一个范畴。

原书把“很容易验证”留给了读者。我们来真正验证一下：

```lean
section Limits
variable {I : Type u₁} [Category.{u₁, v₁} I] {C : Type u₂} [Category.{u₂, v₂} C]

/-- 锥态射：顶点之间的一个态射 hom，使所有三角形交换。 -/
structure ConeHom {D : CFunctor I C} (s t : ConeOver D) where
  hom : s.apex ⟶ t.apex
  comm : ∀ i, t.leg.app i ⊚ hom = s.leg.app i

/-- 两个锥态射只要底下的 hom 相同就相同（comm 是命题，证明无关）。 -/
theorem ConeHom.ext' {D : CFunctor I C} {s t : ConeOver D} {f g : ConeHom s t}
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; cases h; rfl

/-- 锥范畴：对象是锥，态射是锥态射。 -/
instance coneCategory (D : CFunctor I C) : Category (ConeOver D) where
  Hom := ConeHom
  -- 恒等态射是分解态射：α_i ⊚ 𝟙 = α_i
  id s := ⟨𝟙 s.apex, fun i => Category.comp_id _⟩
  -- 分解态射的复合还是分解态射：α''_i ⊚ (g ⊚ f) = (α''_i ⊚ g) ⊚ f = α'_i ⊚ f = α_i
  comp g f := ⟨g.hom ⊚ f.hom, fun i => by rw [Category.assoc, g.comm, f.comm]⟩
  id_comp f := ConeHom.ext' (Category.id_comp f.hom)
  comp_id f := ConeHom.ext' (Category.comp_id f.hom)
  assoc f g h := ConeHom.ext' (Category.assoc f.hom g.hom h.hom)
```

::: tip Lean 深入：为什么 `ConeHom.ext'` 成立
`ConeHom` 有两个字段：数据 `hom` 和证明 `comm`。Lean 有一条内置原则叫**证明无关性**（proof irrelevance）：同一个命题的任意两个证明都被视为相等。所以两个 `ConeHom` 只要 `hom` 相同，`comm` 自动相同，整个结构就相同。`cases h` 把等式 `f.hom = g.hom` “用掉”，让两边的 `hom` 变成同一个变量，剩下的 `rfl` 由证明无关性兜底。

这种“数据 + 关于数据的证明”打包在一起的结构，在 Lean 中随处可见，是用类型表达不变量的标准手法。
:::

现在可以把泛锥定义为锥范畴中的**终对象**了。终对象的定义说：从任何别的对象到它，都恰好有一个态射。在我们这里，这就意味着：从任何别的锥的顶点到泛锥的顶点，都恰好有一个分解态射。我们把这个泛锥叫作图 $D$ 的**极限**（limit），记作 $\mathrm{Lim}\,D$（在文献里你经常会看到 $\mathrm{Lim}$ 下面有一个指向 $\mathcal{I}$ 的左箭头）。为了省事，我们常常也把这个锥的顶点叫作极限（或极限对象）。

```lean
/-- L 是 D 的极限：L 是锥范畴的终对象。
    lift 给出从任意锥到 L 的锥态射（存在性），uniq 说它是唯一的（唯一性）。 -/
structure IsLimit {D : CFunctor I C} (L : ConeOver D) where
  lift : (s : ConeOver D) → ConeHom s L
  uniq : ∀ (s : ConeOver D) (h : ConeHom s L), h = lift s
```

直觉上，极限把整个图的性质浓缩进了一个对象里。例如，我们那个双对象图的极限就是两个对象的积。积（连同两条投影）包含了这两个对象的全部信息。而“泛”意味着它没有多余的杂质。

我们可以在 Lean 里把这句话坐实：`a × b` 连同两条投影，就是 `pairDiagram a b` 的极限。

```lean
end Limits

/-- 积是范畴 2 上的图的极限。 -/
def productIsLimit (a b : Type) : IsLimit (productCone a b) where
  -- 存在性：任意锥 (c, α) 经由 fun x => (α₁ x, α₂ x) 分解
  lift s := ⟨fun x => (s.leg.app .one x, s.leg.app .two x),
             fun | .one => rfl | .two => rfl⟩
  -- 唯一性：若 h 也让两个三角形交换，那么 h x 的两个分量只能是 α₁ x 和 α₂ x
  uniq s h := by
    apply ConeHom.ext'
    funext x
    show h.hom x = (s.leg.app .one x, s.leg.app .two x)
    rw [← h.comm .one, ← h.comm .two]
    rfl
```

::: tip Rust 视角
在 Rust 里，“极限是最好的候选者”这件事你天天在用，只是没起名字。任何返回一对值的函数 `fn h(x: C) -> (A, B)` 都等价于一对函数 `(fn(C) -> A, fn(C) -> B)`：给定两个函数 `p`、`q`，唯一能让 `h(x).0 == p(x)` 且 `h(x).1 == q(x)` 的写法就是 `|x| (p(x), q(x))`。上面的 `uniq` 证明，就是把“唯一能这么写”变成了机器检查过的定理。
:::

## 作为自然同构的极限

这个极限的定义还是有一点让人不太满意的地方。我的意思是，它能用，但我们仍然要面对那个连接任意两个锥的三角形交换条件。如果能把它换成某种自然性条件，那就优雅多了。可是怎么换呢？

我们现在面对的已经不是一个锥，而是一整族（实际上是一个范畴的）锥。如果极限存在（先说清楚：极限不一定存在），这些锥中有一个就是泛锥。对于其他每一个锥，都有唯一一个分解态射，把它的顶点（我们叫它 $c$）映到泛锥的顶点 $\mathrm{Lim}\,D$。（其实“其他”两个字可以去掉，因为恒等态射把泛锥映到它自己，泛锥平凡地经由自己分解。）让我把重点再说一遍：给定任意一个锥，就有唯一一个特殊的态射。我们有一个从锥到特殊态射的映射，而且这是一个一一对应。

这个特殊的态射是 hom-集 $\mathcal{C}(c, \mathrm{Lim}\,D)$ 的一个成员。这个 hom-集里的其他成员就没那么幸运了：它们不能分解两个锥之间的映射。我们想要的是：对每个 $c$，从集合 $\mathcal{C}(c, \mathrm{Lim}\,D)$ 中挑出一个态射——一个满足那个特定交换条件的态射。这听起来像不像在定义一个自然变换？简直太像了！

可是，这个变换联系的是哪两个函子呢？

一个函子是把 $c$ 映到集合 $\mathcal{C}(c, \mathrm{Lim}\,D)$ 的映射。它是一个从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的函子——把对象映到集合。实际上它是个逆变函子。它在态射上的作用是这样定义的：取一个从 $c'$ 到 $c$ 的态射 $f$：

$$f : c' \to c$$

我们的函子把 $c'$ 映到集合 $\mathcal{C}(c', \mathrm{Lim}\,D)$。要定义这个函子对 $f$ 的作用（换句话说，要“提升” $f$），我们得给出 $\mathcal{C}(c, \mathrm{Lim}\,D)$ 和 $\mathcal{C}(c', \mathrm{Lim}\,D)$ 之间对应的映射。那就从 $\mathcal{C}(c, \mathrm{Lim}\,D)$ 中挑一个元素 $u$，看看能不能把它映成 $\mathcal{C}(c', \mathrm{Lim}\,D)$ 的某个元素。hom-集的元素是态射，所以我们有：

$$u : c \to \mathrm{Lim}\,D$$

把 $u$ 和 $f$ 做预复合（先走 $f$），得到：

$$u \circ f : c' \to \mathrm{Lim}\,D$$

这正是 $\mathcal{C}(c', \mathrm{Lim}\,D)$ 的一个元素——所以我们确实找到了态射的映射：

```lean
/-- hom 函子 C(-, L) 在态射上的作用：预复合。注意 c 与 c' 的顺序反过来了。 -/
def contramapHom {c c' L : Type} (f : c' → c) (u : c → L) : c' → L := u ∘ f
```

注意 $c$ 和 $c'$ 的顺序颠倒了，这是**逆变**函子的典型特征。

::: info 数学小课堂：逆变是什么意思
普通（协变）函子 $F$ 把 $f : c' \to c$ 送到 $F f : F c' \to F c$，方向不变。**逆变**函子 $G$ 则把它送到 $G f : G c \to G c'$——方向倒过来了。

$\mathcal{C}(-, L)$ 就是这样：你手里有一个“从 $c$ 出发到 $L$”的态射 $u$，又有一个“从 $c'$ 到 $c$”的态射 $f$，你能拼出的是“从 $c'$ 出发到 $L$”的态射 $u \circ f$。所以输入是 $\mathcal{C}(c, L)$ 的元素，输出是 $\mathcal{C}(c', L)$ 的元素，和 $f$ 的方向相反。

Rust 里的直觉：一个“消费者” `impl Fn(C) -> L`，如果你有 `f: impl Fn(C2) -> C`，就能造出一个 `impl Fn(C2) -> L` 的消费者：`move |x| u(f(x))`。“消费者”总是逆变的。
:::

![hom 函子对 f 的提升](/img/2.2/homsetmapping.jpg "f : c' → c 被提升为 C(c, Lim D) → C(c', Lim D) 的映射：u ↦ u ∘ f。")

```diagram
c2: (0, 0) "c'"
c: (1.6, 0) "c"
L: (3.2, 0) "\mathrm{Lim}\,D"
f: c2 -> c "f"
u: c -> L "u"
uf: c2 -> L "u \circ f" bend=-40 side=right color=brand
path "先 f 再 u": f u
path "u ∘ f": uf color=green
caption: 预复合：hom-集 C(c, Lim D) 中的 u 被送到 C(c', Lim D) 中的 u ∘ f。
```

要定义一个自然变换，我们还需要另一个同样从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的函子。这一次我们考虑的是锥的集合。锥就是自然变换，所以我们考察的是自然变换的集合 $\mathit{Nat}(\Delta_c, D)$。从 $c$ 到这个特定的自然变换集合的映射，也是一个（逆变）函子。怎么证明呢？还是定义它在态射上的作用：

$$f : c' \to c$$

$f$ 的提升应该是两个从 $\mathcal{I}$ 到 $\mathcal{C}$ 的函子之间的自然变换的映射：

$$\mathit{Nat}(\Delta_c, D) \to \mathit{Nat}(\Delta_{c'}, D)$$

怎么映射自然变换呢？每个自然变换都是一组态射的选择——它的分量——$\mathcal{I}$ 的每个对象对应一个态射。某个 $\alpha$（$\mathit{Nat}(\Delta_c, D)$ 的成员）在 $a$（$\mathcal{I}$ 中的对象）处的分量是一个态射：

$$\alpha_a : \Delta_c\, a \to D\, a$$

或者，按常函子 $\Delta$ 的定义，

$$\alpha_a : c \to D\, a$$

给定 $f$ 和 $\alpha$，我们要构造一个 $\beta$，它是 $\mathit{Nat}(\Delta_{c'}, D)$ 的成员。它在 $a$ 处的分量应该是一个态射：

$$\beta_a : c' \to D\, a$$

后者（$\beta_a$）很容易从前者（$\alpha_a$）得到：和 $f$ 做预复合即可：

$$\beta_a = \alpha_a \circ f$$

要证明这些分量确实拼成了一个自然变换，也不太难。

![锥的映射：逐个分量预复合 f](/img/2.2/natmapping.jpg "给定 f : c' → c，把锥 α 的每条腿都预复合上 f，就得到以 c' 为顶点的锥 β。")

原书说“相对容易证明”，Lean 让我们真的证明它。自然性的证明只需要结合律和锥的侧面交换：

```lean
section Limits
variable {I : Type u₁} [Category.{u₁, v₁} I] {C : Type u₂} [Category.{u₂, v₂} C]

/-- 逆变函子 c ↦ Nat(Δ c, D) 在态射 f : c' ⟶ c 上的作用：每条腿都预复合 f。 -/
def Cone.precomp {c c' : C} {D : CFunctor I C} (α : Cone c D) (f : c' ⟶ c) : Cone c' D where
  app i := α.app i ⊚ f
  naturality g := by
    -- 目标：D.map g ⊚ (α_i ⊚ f) = (α_j ⊚ f) ⊚ 𝟙 c'
    show D.map g ⊚ (α.app _ ⊚ f) = (α.app _ ⊚ f) ⊚ 𝟙 c'
    rw [Category.comp_id, Category.assoc, Cone.comm]
```

为了说两个自然变换相等，只需说它们的每个分量相等（自然性那部分是证明，证明无关）：

```lean
theorem NatTrans.ext' {F G : CFunctor I C} {α β : F ⟹ G}
    (h : ∀ i, α.app i = β.app i) : α = β := by
  cases α with
  | mk a na =>
    cases β with
    | mk b nb =>
      have : a = b := funext h
      subst this
      rfl
```

于是可以验证 `precomp` 真的满足（逆变）函子的两条定律——保持恒等、把复合反过来保持：

```lean
theorem Cone.precomp_id {c : C} {D : CFunctor I C} (α : Cone c D) :
    α.precomp (𝟙 c) = α :=
  NatTrans.ext' fun i => Category.comp_id (α.app i)

/-- 先沿 f : c' ⟶ c 拉、再沿 g : c'' ⟶ c' 拉 = 一次沿 f ⊚ g 拉（顺序反过来了）。 -/
theorem Cone.precomp_comp {c c' c'' : C} {D : CFunctor I C} (α : Cone c D)
    (f : c' ⟶ c) (g : c'' ⟶ c') :
    α.precomp (f ⊚ g) = (α.precomp f).precomp g :=
  NatTrans.ext' fun i => Category.assoc g f (α.app i)
```

这样，给定态射 $f$，我们就逐个分量地构造出了两个自然变换之间的映射。这个映射就定义了函子

$$c \mapsto \mathit{Nat}(\Delta_c, D)$$

的 `contramap`。我刚才所做的，就是向你展示：存在两个从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的（逆变）函子。我没有做任何假设——这两个函子总是存在的。

顺便说一句，这两个函子中的第一个在范畴论里扮演着重要角色，我们讲米田引理（Yoneda lemma）时还会再见到它。从任意范畴 $\mathcal{C}$ 到 $\mathbf{Set}$ 的逆变函子有一个专门的名字：**预层**（presheaf）。第一个函子叫作**可表预层**（representable presheaf）。第二个函子也是一个预层。

既然有了两个函子，就可以谈它们之间的自然变换了。那么，不再绕弯子，结论如下：从 $\mathcal{I}$ 到 $\mathcal{C}$ 的函子 $D$ 有极限 $\mathrm{Lim}\,D$，**当且仅当**我刚才定义的两个函子之间存在一个自然同构：

$$\mathcal{C}(c, \mathrm{Lim}\,D) \cong \mathit{Nat}(\Delta_c, D)$$

我来提醒你一下什么是自然同构。它是一个自然变换，并且每个分量都是同构，也就是可逆的态射。

::: info 数学小课堂：读懂 $\mathcal{C}(c, \mathrm{Lim}\,D) \cong \mathit{Nat}(\Delta_c, D)$
把这个式子拆成大白话：

- 左边：从 $c$ 到极限对象的**一个态射**；
- 右边：以 $c$ 为顶点的**一个锥**（一整束腿，还要满足所有侧面交换）；
- $\cong$：这两样东西**一一对应**，而且这个对应对 $c$ 是“自然”的（换一个顶点，对应方式跟着协调地变）。

拿积来说：左边是 `c → a × b`，右边是一对 `(c → a, c → b)`。“一一对应”就是：一个返回二元组的函数，和一对函数，是一回事。这个式子把“极限是最好的锥”压缩成了一句话：**指向极限的态射 = 锥**。

“当且仅当”（if and only if）是数学里的双向箭头 $\Leftrightarrow$：A 当且仅当 B，意思是“A 推出 B”且“B 推出 A”。下面我们两个方向都证明。
:::

我不打算完整走一遍这个命题的证明。过程很直接，只是有点繁琐。处理自然变换时，你通常关注的是分量，也就是态射。在这里，因为两个函子的目标范畴都是 $\mathbf{Set}$，自然同构的分量就是函数。这些是高阶函数，因为它们把 hom-集映到自然变换的集合。同样地，你可以通过考察一个函数对它的参数做了什么来分析它：这里参数是一个态射——$\mathcal{C}(c, \mathrm{Lim}\,D)$ 的成员——结果是一个自然变换——$\mathit{Nat}(\Delta_c, D)$ 的成员，也就是我们说的锥。这个自然变换又有它自己的分量，而它们是态射。所以这是一路到底的态射，只要你能理清它们，就能证明这个命题。

原作者跳过了证明。有了 Lean，我们可以不跳。先看“极限 ⇒ 自然同构”这个方向：

```lean
namespace IsLimit
variable {D : CFunctor I C} {L : ConeOver D} (hL : IsLimit L)

/-- 从态射到锥：把极限锥沿 u 拉回来。 -/
def toCone {c : C} (u : c ⟶ L.apex) : Cone c D := L.leg.precomp u

/-- 从锥到态射：取那个唯一的分解态射。 -/
def fromCone {c : C} (α : Cone c D) : c ⟶ L.apex := (hL.lift ⟨c, α⟩).hom

/-- 往返一：态射 → 锥 → 态射，回到原处（用唯一性）。 -/
theorem from_to {c : C} (u : c ⟶ L.apex) : hL.fromCone (toCone u) = u := by
  have h := hL.uniq ⟨c, toCone u⟩ ⟨u, fun _ => rfl⟩
  exact (congrArg ConeHom.hom h).symm

/-- 往返二：锥 → 态射 → 锥，回到原处（用存在性中的交换三角形）。 -/
theorem to_from {c : C} (α : Cone c D) : toCone (hL.fromCone α) = α :=
  NatTrans.ext' fun i => (hL.lift ⟨c, α⟩).comm i

/-- 自然性：先预复合 f 再变成锥 = 先变成锥再预复合 f。 -/
theorem toCone_natural {c c' : C} (u : c ⟶ L.apex) (f : c' ⟶ c) :
    toCone (u ⊚ f) = (toCone u).precomp f :=
  NatTrans.ext' fun i => Category.assoc f u (L.leg.app i)

end IsLimit
```

自然性方块长这样（两个逆变函子，所以竖直箭头都是“沿 $f$ 往回拉”）：

```diagram
A: (0, 0) "\mathcal{C}(c, \mathrm{Lim}\,D)"
B: (2.6, 0) "\mathit{Nat}(\Delta_c, D)"
A2: (0, 1.4) "\mathcal{C}(c', \mathrm{Lim}\,D)"
B2: (2.6, 1.4) "\mathit{Nat}(\Delta_{c'}, D)"
t: A -> B "\varphi_c"
t2: A2 -> B2 "\varphi_{c'}" side=right
l: A -> A2 "- \circ f" side=right
r: B -> B2 "- \circ f"
path "先变成锥，再拉回": t r
path "先拉回，再变成锥": l t2 color=green
caption: φ 的自然性：toCone (u ∘ f) = (toCone u).precomp f。
```

反方向“自然同构 ⇒ 极限”更有意思，因为它展示了最重要的那一点：

> 最重要的结论是：这个同构的自然性条件，恰好就是锥映射的交换条件。

下面的证明里，泛锥被取为 $\varphi(\mathrm{id}_L)$（“恒等态射对应的那个锥”）；而“三角形交换”和“唯一性”**全部**是从自然性 `nat` 推出来的：

```lean
/-- 如果对每个 c 都有自然的双射 (c ⟶ L) ≅ Cone c D，那么 φ(𝟙 L) 就是一个极限锥。 -/
def limitOfIso {D : CFunctor I C} (L : C)
    (φ : ∀ {c : C}, (c ⟶ L) → Cone c D) (ψ : ∀ {c : C}, Cone c D → (c ⟶ L))
    (ψφ : ∀ {c : C} (u : c ⟶ L), ψ (φ u) = u)
    (φψ : ∀ {c : C} (α : Cone c D), φ (ψ α) = α)
    (nat : ∀ {c c' : C} (u : c ⟶ L) (f : c' ⟶ c), φ (u ⊚ f) = (φ u).precomp f) :
    IsLimit (⟨L, φ (𝟙 L)⟩ : ConeOver D) where
  -- 存在性：分解态射取 ψ α。三角形交换来自自然性：
  -- α = φ (ψ α) = φ (𝟙 ⊚ ψ α) = (φ 𝟙).precomp (ψ α)
  lift s := ⟨ψ s.leg, fun i => by
    have h := nat (𝟙 L) (ψ s.leg)
    rw [Category.id_comp, φψ] at h
    exact (congrArg (fun β => NatTrans.app β i) h).symm⟩
  -- 唯一性：若 h 让三角形交换，则 φ h = (φ 𝟙).precomp h = α，于是 h = ψ (φ h) = ψ α
  uniq s h := by
    apply ConeHom.ext'
    show h.hom = ψ s.leg
    have e : φ h.hom = s.leg := by
      rw [← Category.id_comp h.hom, nat]
      exact NatTrans.ext' h.comm
    rw [← e, ψφ]

end Limits
```

::: tip Lean 深入：`congrArg`、`calc` 式的思考
- `congrArg f h`：如果 `h : x = y`，那么 `congrArg f h : f x = f y`。“等式两边同时套上同一个函数”。上面用它从“两个锥相等”得到“它们在 `i` 处的分量相等”。
- `rw [← e]`：`←` 表示把等式**从右往左**用，即把目标里的 `s.leg` 换回 `φ h.hom`。
- 证明 `uniq` 的思路完全照搬数学证明，只是每一步都要被 Lean 检查。读这类证明时，建议把鼠标停在每个 tactic 上（在 Lean 编辑器里）看目标如何变化。
:::

先预告一下后面的精彩内容：集合 $\mathit{Nat}(\Delta_c, D)$ 可以看作函子范畴中的一个 hom-集；所以我们这个自然同构联系的是两个 hom-集，这指向一个更加一般的关系，叫作**伴随**（adjunction）。

## 极限的例子

我们已经看到，范畴论意义下的积，是由我们称为 $\mathbf{2}$ 的简单范畴生成的图的极限。

还有一个更简单的极限例子：终对象。第一反应可能是：单对象范畴会给出终对象。但真相比这还要“赤裸”：终对象是由**空范畴**生成的极限。从空范畴出发的函子不选任何对象，所以锥缩成了只剩一个顶点。泛锥就是那个孤零零的顶点，从任何别的顶点到它都有唯一一个态射。你会认出来，这正是终对象的定义。

在 Lean 中，空范畴就是 `Discrete Empty`。锥的“腿”一条都没有（`nomatch` 表示“不存在需要处理的情形”），而 `Unit` 就是它的极限：

```lean
/-- 空图：从空范畴出发，什么都不选。 -/
def emptyDiagram : CFunctor (Discrete Empty) Type := discreteDiagram Empty.elim

/-- 以 Unit 为顶点、没有腿的锥。 -/
def unitCone : ConeOver emptyDiagram where
  apex := Unit
  leg := {
    app := fun i => (nomatch (i : Empty))
    naturality := fun {i} _ => (nomatch (i : Empty)) }

/-- Unit 是空图的极限，也就是终对象：到 Unit 的函数只有一个。 -/
def unitIsLimit : IsLimit unitCone where
  lift s := ⟨fun _ => (), fun i => nomatch (i : Empty)⟩
  uniq s h := by apply ConeHom.ext'; funext x; rfl
```

下一个有意思的极限叫**等化子**（equalizer）。它是由这样一个范畴生成的极限：两个对象，它们之间有两条平行的态射（当然还有恒等态射）。这个范畴在 $\mathcal{C}$ 中选出一个图，由两个对象 $a$、$b$ 和两个态射组成：

```lean no-check
f : a → b
g : a → b
```

在 Type 中，这就是两个同类型的函数。要在这个图上造一个锥，我们需要加上顶点 $c$ 和两条投影：

```lean no-check
p : c → a
q : c → b
```

![等化子的锥](/img/2.2/equalizercone.jpg "等化子形状的图上的锥：顶点 c 有两条腿 p 和 q。")

我们有两个必须交换的三角形：

```lean no-check
q = f ∘ p
q = g ∘ p
```

```diagram
c: (0, 0) "c"
a: (0, 1.5) "a"
b: (1.8, 1.5) "b"
p: c -> a "p" side=right
q: c -> b "q"
f: a -> b "f" bend=14
g: a -> b "g" bend=-14 side=right
path "f ∘ p": p f
path "q": q color=green
path "g ∘ p": p g color=orange
caption: 等化子的锥：两个三角形都要交换，于是 f ∘ p = q = g ∘ p。
```

这告诉我们，$q$ 由其中一个方程（比如 $q = f \circ p$）唯一确定，可以从图里略去。于是只剩下一个条件：

$$f \circ p = g \circ p$$

理解它的方式是：如果把注意力限制在 $\mathbf{Set}$ 上，函数 $p$ 的像选出了 $a$ 的一个子集。限制在这个子集上，函数 $f$ 和 $g$ 相等。

::: info 数学小课堂：子集、像，以及“方程的解集”
- 函数 $p : c \to a$ 的**像**（image）是 $a$ 中所有“被 $p$ 打中”的元素组成的子集 $\{p(x) \mid x \in c\}$。
- $f \circ p = g \circ p$ 的意思是：对每个 $x \in c$，$f(p(x)) = g(p(x))$。换句话说，$p$ 打中的每个点都满足方程 $f(y) = g(y)$。
- 所有满足 $f(y) = g(y)$ 的 $y$ 组成的子集 $\{y \in a \mid f(y) = g(y)\}$，就是这个方程的**解集**。等化子就是这个解集——外加把它嵌回 $a$ 的那个包含映射。

所以在集合的世界里，“求等化子”就是“解方程 $f(y) = g(y)$”。
:::

在 Lean（以及 $\mathbf{Type}$ 范畴）里，“满足某个条件的元素组成的子集”有一个现成的写法：**子类型**（subtype）`{x : a // f x = g x}`。它的每个元素是一个二元组：一个 `x : a`，外加一个证明 `f x = g x`。

::: tip Lean 深入：子类型 `Subtype`
`{x : a // P x}` 是 `Subtype (fun x => P x)` 的记号。它的元素写作 `⟨x, h⟩`，其中 `h : P x`。

- `e.val`（或 `e.1`）取出底下的 `x : a`；`e.property`（或 `e.2`）取出证明；
- `Subtype.ext`：两个子类型元素只要 `val` 相等就相等（又是证明无关性在起作用）。

和 Rust 的“新类型 + 私有构造函数”很像：`struct NonZero(u32)` 加上一个检查过的 `new`，保证内部值满足不变量。区别是，Lean 的不变量写进了类型里、由编译器检查，而不是靠程序员自觉。
:::

现在把等化子定义出来，并**证明它的泛性质**——存在性加唯一性：

```lean
/-- Type 中 f 与 g 的等化子：方程 f x = g x 的解集。 -/
def Equalizer {a b : Type} (f g : a → b) : Type := {x : a // f x = g x}

/-- 锥的腿：把解集嵌回 a。 -/
def Equalizer.ι {a b : Type} {f g : a → b} : Equalizer f g → a := Subtype.val

/-- 它确实是一个锥：f ∘ ι = g ∘ ι。 -/
theorem Equalizer.condition {a b : Type} (f g : a → b) :
    f ∘ Equalizer.ι = g ∘ (Equalizer.ι : Equalizer f g → a) := by
  funext e; exact e.property

/-- 存在性：任何满足 f ∘ p = g ∘ p 的 p 都经由等化子分解。 -/
def Equalizer.lift {a b c : Type} {f g : a → b} (p : c → a) (hp : f ∘ p = g ∘ p) :
    c → Equalizer f g :=
  fun x => ⟨p x, congrFun hp x⟩

theorem Equalizer.lift_fac {a b c : Type} {f g : a → b} (p : c → a) (hp : f ∘ p = g ∘ p) :
    Equalizer.ι ∘ Equalizer.lift p hp = p := rfl

/-- 唯一性：任何满足 ι ∘ h = p 的 h 都等于 lift p。 -/
theorem Equalizer.lift_uniq {a b c : Type} {f g : a → b} (p : c → a) (hp : f ∘ p = g ∘ p)
    (h : c → Equalizer f g) (hh : Equalizer.ι ∘ h = p) : h = Equalizer.lift p hp := by
  funext x
  apply Subtype.ext       -- 只需比较底下的 a 中的元素
  exact congrFun hh x     -- 而 ι (h x) = p x 正是 hh 在 x 处的值
```

举个例子。取 $a$ 为以坐标 $x$ 和 $y$ 为参数的二维平面，取 $b$ 为实数直线，并取：

$$f(x, y) = 2y + x, \qquad g(x, y) = y - x$$

这两个函数的等化子是实数集（顶点 $c$），以及函数：

$$p(t) = (t, -2t)$$

注意，$p\,t$ 在二维平面上定义了一条直线。沿着这条直线，两个函数相等。

Lean 核心库里没有实数（实数在 Mathlib 里），所以我们用整数 `Int` 来演示——道理完全一样，方程 $2y + x = y - x$ 化简为 $y = -2x$：

```lean
def ef (v : Int × Int) : Int := 2 * v.2 + v.1
def eg (v : Int × Int) : Int := v.2 - v.1
def ep (t : Int) : Int × Int := (t, -2 * t)

/-- 沿着直线 p t = (t, -2t)，f 和 g 相等。 -/
theorem ep_eq : ef ∘ ep = eg ∘ ep := by
  funext t
  simp only [Function.comp, ef, eg, ep]
  omega   -- 线性整数算术：2 * (-2 * t) + t = -2 * t - t
```

::: tip Lean 深入：`omega`
`omega` 是 Lean 内置的决策过程，专门对付**整数与自然数上的线性算术**（加减、乘常数、比较、整除常数……）。只要目标是这类不等式/等式的逻辑组合，它就能自动证明，或告诉你证不出来。上面 `simp only [...]` 先把定义展开成纯算术式，再交给 `omega`。
:::

当然，还有别的集合 $c'$ 和函数 $p'$ 也能让等式成立：

$$f \circ p' = g \circ p'$$

但它们全都唯一地经由 $p$ 分解。例如，我们可以取单元素集 $()$ 作为 $c'$，并取函数：

```lean
def ep' (_ : Unit) : Int × Int := (0, 0)
```

它是一个好锥，因为 $f(0, 0) = g(0, 0)$。但它不是泛锥，因为它唯一地经由 $h$ 分解：

```lean
/-- (0, 0) 也在直线上，所以 p' 也是一个锥…… -/
theorem ep'_eq : ef ∘ ep' = eg ∘ ep' := rfl

/-- ……但它经由 p 分解：p' = p ∘ h，其中 h () = 0。 -/
def eh (_ : Unit) : Int := 0
example : ep' = ep ∘ eh := rfl
```

![等化子作为极限](/img/2.2/equilizerlimit.jpg "单点集上的锥 p' 经由 h 唯一地分解到等化子 p 上。")

```diagram
c2: (0, 0) "()"
c: (0, 1.4) "\mathbb{Z}"
a: (1.8, 1.4) "\mathbb{Z} \times \mathbb{Z}"
b: (3.6, 1.4) "\mathbb{Z}"
h: c2 -> c "h" dashed side=right
p2: c2 -> a "p'"
p: c -> a "p" side=right
f: a -> b "f" bend=14
g: a -> b "g" bend=-14 side=right
path "p'": p2
path "p ∘ h": h p color=green
caption: 等化子的泛性质：任何满足 f ∘ p' = g ∘ p' 的 p' 都唯一地经由 p 分解。
```

::: details 补充：直线 $\{(t, -2t)\}$ 恰好就是这个等化子（完整证明）
前面我们说“等化子是实数集连同 $p$”。在 Lean 里，`Equalizer ef eg` 是“满足方程的点”组成的子类型，而 `Int` 是参数 $t$。它们**同构**：

```lean
/-- 两个类型之间的同构：一对互逆的函数。 -/
structure TypeIso (α β : Type) where
  to : α → β
  inv : β → α
  inv_to : ∀ x, inv (to x) = x
  to_inv : ∀ y, to (inv y) = y

infix:25 " ≅ " => TypeIso

def lineIso : Int ≅ Equalizer ef eg where
  to := Equalizer.lift ep ep_eq
  inv e := e.val.1
  inv_to _ := rfl
  to_inv := by
    rintro ⟨⟨x, y⟩, h⟩
    apply Subtype.ext
    simp only [ef, eg] at h
    -- h : 2 * y + x = y - x，所以 y = -2 * x
    show (x, -2 * x) = (x, y)
    congr 1
    omega
```
:::

所以，等化子可以用来求解形如 $f\,x = g\,x$ 的方程。但它的意义要广泛得多，因为它是用对象和态射来定义的，而不是用代数的方式。

求解方程的一个更一般的思想，体现在另一个极限中——**拉回**（pullback）。这里，我们仍然有两个想让它们相等的态射，但这一次它们的定义域不同。我们从形状为 $1 \rightarrow 2 \leftarrow 3$ 的三对象范畴出发。与这个范畴对应的图由三个对象 $a$、$b$、$c$ 和两个态射组成：

```lean no-check
f : a → b
g : c → b
```

这个图常常被称为**余跨**（cospan）。

建立在这个图上的锥由顶点 $d$ 和三个态射组成：

```lean no-check
p : d → a
q : d → c
r : d → b
```

![拉回的锥](/img/2.2/pullbackcone.jpg "余跨上的锥：顶点 d 有三条腿 p、q、r。")

交换条件告诉我们，$r$ 完全由其他态射决定，可以从图中略去。所以只剩下这个条件：

$$g \circ q = f \circ p$$

拉回就是这种形状的泛锥。

![拉回作为极限](/img/2.2/pullbacklimit.jpg "拉回：任何满足 g ∘ q' = f ∘ p' 的锥都唯一地经由拉回分解。")

```diagram
e: (0, 0) "e"
d: (1.3, 1) "d"
c: (3, 1) "c"
a: (1.3, 2.5) "a"
b: (3, 2.5) "b"
h: e -> d "h" dashed
q2: e -> c "q'" bend=-12
p2: e -> a "p'" bend=12 side=right
q: d -> c "q"
p: d -> a "p" side=right
g: c -> b "g"
f: a -> b "f" side=right
path "g ∘ q": q g
path "f ∘ p": p f color=green
path "q'": q2 color=orange
path "q ∘ h": h q color=purple
caption: 拉回 d 及其泛性质。方块交换（g ∘ q = f ∘ p），任何别的锥 e 都唯一地经由 h 分解。
```

同样，如果把视野收窄到集合，你可以把对象 $d$ 看成由 $a$ 和 $c$ 中元素组成的对子，满足“$f$ 作用在第一个分量上”等于“$g$ 作用在第二个分量上”。在 Lean 中，这又是一个子类型。注意，为了与 Lean 的习惯一致，下面把余跨写成 `f : a → c`、`g : b → c`（拉回落在 `a × b` 里）：

```lean
/-- Type 中余跨 a —f→ c ←g— b 的拉回：使 f x = g y 的对子 (x, y)。 -/
def Pullback {a b c : Type} (f : a → c) (g : b → c) : Type := {p : a × b // f p.1 = g p.2}

namespace Pullback
variable {a b c d : Type} {f : a → c} {g : b → c}

def π₁ : Pullback f g → a := fun p => p.val.1
def π₂ : Pullback f g → b := fun p => p.val.2

/-- 方块交换：f ∘ π₁ = g ∘ π₂。 -/
theorem condition : f ∘ (π₁ : Pullback f g → a) = g ∘ π₂ := by
  funext p; exact p.property

/-- 存在性：任何满足 f ∘ p = g ∘ q 的锥 (d, p, q) 都经由 lift 分解…… -/
def lift (p : d → a) (q : d → b) (h : f ∘ p = g ∘ q) : d → Pullback f g :=
  fun x => ⟨(p x, q x), congrFun h x⟩

theorem lift_fst (p : d → a) (q : d → b) (h : f ∘ p = g ∘ q) : π₁ ∘ lift p q h = p := rfl
theorem lift_snd (p : d → a) (q : d → b) (h : f ∘ p = g ∘ q) : π₂ ∘ lift p q h = q := rfl

/-- ……唯一性：两个三角形都交换的 k 只能是 lift。 -/
theorem lift_uniq (p : d → a) (q : d → b) (h : f ∘ p = g ∘ q)
    (k : d → Pullback f g) (h₁ : π₁ ∘ k = p) (h₂ : π₂ ∘ k = q) : k = lift p q h := by
  funext x
  apply Subtype.ext
  show (k x).val = (p x, q x)
  rw [← h₁, ← h₂]
  rfl

end Pullback
```

::: tip Rust 视角：拉回就是数据库里的内连接
如果 `a` 是“人”的表、`b` 是“餐馆”的表，`f` 和 `g` 分别给出“人所在的城市”和“餐馆所在的城市”，那么拉回 `Pullback f g` 就是

```sql
SELECT * FROM people JOIN restaurants ON people.city = restaurants.city
```

用 Rust 写，大致是：

```rust
fn pullback<A: Clone, B: Clone, C: PartialEq>(
    xs: &[A], ys: &[B], f: impl Fn(&A) -> C, g: impl Fn(&B) -> C,
) -> Vec<(A, B)> {
    let mut out = Vec::new();
    for x in xs {
        for y in ys {
            if f(x) == g(y) {
                out.push((x.clone(), y.clone()));
            }
        }
    }
    out
}
```

泛性质则说：任何“把每个订单同时关联到一个人和一家同城餐馆”的数据 `d`，都唯一地对应一个 `d → Pullback` 的映射——每个订单映到它对应的那一行连接结果。下面的交互组件就用这个例子。
:::

<Ch2_2ConeExplorer />

如果这还是太一般，那就考虑 $g$ 是常函数的特殊情形，比如 $g\,\_ = 1.23$（假设 $b$ 是实数集）。那么你实际上是在解方程：

$$f\,x = 1.23$$

在这种情况下，$c$ 是什么无关紧要（只要它不是空集），所以我们可以取它为单元素集。例如，集合 $a$ 可以是三维向量的集合，$f$ 是向量的长度。那么拉回就是对子 $(v, ())$ 的集合，其中 $v$ 是长度为 $1.23$ 的向量（方程 $\sqrt{x^2+y^2+z^2} = 1.23$ 的解），$()$ 是单元素集里那个充数的元素。

同样因为核心库没有实数，我们在 Lean 里换成整数向量与“长度的平方等于 25”。拉回中的元素是一个向量、一个 `()`，以及一份“它确实在球面上”的证明：

```lean
def lenSq (v : Int × Int × Int) : Int := v.1 * v.1 + v.2.1 * v.2.1 + v.2.2 * v.2.2

/-- 半径为 5 的“整数球面”：f 是长度平方，g 是取常值 25 的函数。 -/
def sphere : Type := Pullback lenSq (fun (_ : Unit) => (25 : Int))

/-- (3, 4, 0) 在球面上；证明 3² + 4² + 0² = 25 只需计算（rfl）。 -/
def aPoint : sphere := ⟨((3, 4, 0), ()), rfl⟩
```

不过拉回还有更一般的应用，在编程中也有。例如，把 C++ 的类看作一个范畴，其中态射是把子类连到超类的箭头。我们把继承看作可传递的：如果 `C` 继承自 `B`，`B` 继承自 `A`，我们就说 `C` 继承自 `A`（毕竟，在需要指向 `A` 的指针的地方，你可以传一个指向 `C` 的指针）。另外，我们还假定 `C` 继承自 `C`，这样每个类都有恒等箭头。这样一来，子类关系就和子类型关系对齐了。C++ 还支持多重继承，所以你可以构造一个菱形继承图：两个类 `B` 和 `C` 继承自 `A`，第四个类 `D` 同时继承 `B` 和 `C`。通常 `D` 会得到两份 `A` 的拷贝，这很少是你想要的；但你可以用虚继承，让 `D` 里只有一份 `A`。

让 `D` 成为这个图中的拉回意味着什么？意味着任何同时继承 `B` 和 `C` 的类 `E` 也是 `D` 的子类。这在 C++ 里没法直接表达，因为 C++ 的子类型是名义的（nominal）：C++ 编译器不会推断出这种类关系——那需要“鸭子类型”。但我们可以跳出子类型关系，转而问：从 `E` 到 `D` 的强制转换（cast）是否安全？如果 `D` 只是 `B` 和 `C` 最朴素的组合，没有额外数据，也没有重写任何方法，那么这个转换就是安全的。当然，如果 `B` 和 `C` 的某些方法有命名冲突，那就根本不存在拉回。

![类的菱形继承](/img/2.2/classes.jpg "菱形继承：B 和 C 都继承自 A，D 同时继承 B 和 C。")

::: tip Rust 视角：用 supertrait 和 blanket impl 造出拉回
Rust 没有类继承，但 trait 之间有“子 trait → 父 trait”的关系（`trait B: A` 表示实现 `B` 的类型必须也实现 `A`）。把 trait 看作对象、“是子 trait”看作箭头，也得到一个（瘦）范畴。

C++ 做不到的事，Rust 恰好可以做：用一个 **blanket impl**，让“任何同时实现 `B` 和 `C` 的类型”自动实现 `D`。这正是“任何同时继承 `B` 和 `C` 的 `E` 都是 `D` 的子类”——`D` 成了 `B → A ← C` 的拉回：

```rust
trait A { fn a(&self) -> i32; }
trait B: A { fn b(&self) -> i32; }
trait C: A { fn c(&self) -> i32; }

// D 是 B 和 C 最朴素的组合：没有新方法……
trait D: B + C {}
// ……而且任何同时实现了 B 和 C 的类型都自动是 D（泛性质中的“唯一分解”）
impl<T: B + C> D for T {}

struct E;
impl A for E { fn a(&self) -> i32 { 1 } }
impl B for E { fn b(&self) -> i32 { 2 } }
impl C for E { fn c(&self) -> i32 { 3 } }

fn use_d(d: &dyn D) -> i32 { d.a() + d.b() + d.c() }

pub fn demo() -> i32 {
    use_d(&E) // E 从未声明自己实现 D，但可以当 D 用
}
```

而且 `D` 里只有一份 `A`（Rust 的 trait 没有“两份拷贝”的问题）。
:::

拉回在类型推断中还有一个更高级的用途。我们经常需要**合一**（unify）两个表达式的类型。比如说，假设编译器要推断这个函数的类型：

```lean no-check
def twice f x := f (f x)
```

它会给所有变量和子表达式分配初步的类型。特别地，它会分配：

```lean no-check
f       : t0
x       : t1
f x     : t2
f (f x) : t3
```

由此推出：

```lean no-check
twice : t0 → t1 → t3
```

它还会根据函数应用的规则，得出一组约束：

```lean no-check
t0 = t1 → t2  -- 因为 f 被应用到 x 上
t0 = t2 → t3  -- 因为 f 被应用到 (f x) 上
```

这些约束必须被合一：找到一组类型（或类型变量），代入两个表达式中的未知类型后，能得到同一个类型。一种代换是：

```lean no-check
t1 = t2 = t3 = Int
twice : (Int → Int) → Int → Int
```

但显然它不是最一般的那个。最一般的代换是用拉回得到的。细节我就不展开了，那超出了本书的范围，但你可以说服自己，结果应该是：

```lean
def twice (f : t → t) (x : t) : t := f (f x)
```

其中 `t` 是一个自由类型变量。

::: warning 易错点：Lean 不会替你“泛化”顶层定义
在 Haskell 里，`twice f x = f (f x)` 不写类型也能通过，编译器自己推出最一般的类型。**Lean 4 不这样做**：上面那行 `def twice f x := f (f x)` 会报错 “Function expected”，因为 Lean 在检查函数体之前就要求先确定每个参数的类型。

但 Lean 内部确实在做合一：在表达式内部，只要给出足够信息，它就能把剩下的推出来。例如

```lean
example := fun (f : Nat → Nat) x => f (f x)   -- x 的类型由合一推出：Nat
```

而上面的 `def twice (f : t → t) (x : t) : t` 中，`t` 甚至都没有声明——Lean 的**自动绑定隐式参数**（auto-bound implicit）功能看到一个未定义的单字母名字，会自动把它当作 `{t : Sort u}` 加到参数列表里。所以它的完整类型是 `{t : Sort u} → (t → t) → t → t`，正是“最一般的代换”。
:::

::: info 数学小课堂：为什么“最一般的合一子”是一个拉回
（这是补充直觉，不影响后文。）把“类型表达式”看成对象，把“代换”（把类型变量替换成别的类型表达式）看成箭头。两个约束 $t_0 = t_1 \to t_2$ 和 $t_0 = t_2 \to t_3$ 各自描述了一种“把 $t_0$ 展开”的方式。一个**合一子**是一个代换 $\sigma$，使两边经 $\sigma$ 后变得相同——这就像一个锥的方块交换。**最一般的合一子**则是“所有合一子都能唯一地经由它再做一次代换得到”的那个——这正是泛锥的定义。$t_1 = t_2 = t_3 = \mathrm{Int}$ 是一个锥，而 $t_1 = t_2 = t_3 = t$ 是极限：前者经由代换 $t \mapsto \mathrm{Int}$ 唯一地分解到后者。（严格说，在通常的方向约定下这是一个余等化子/推出；方向取决于你如何定义“代换”箭头。原书在这里只给直觉，我们也点到为止。）
:::

## 余极限

就像范畴论里的所有构造一样，极限在对偶范畴里也有它的镜像。把锥中所有箭头的方向都反过来，就得到**余锥**（co-cone），其中泛的那一个叫作**余极限**（colimit）。注意，这种反转也影响到了分解态射：它现在从泛余锥流向任何别的余锥。

![余锥与分解态射](/img/2.2/colimit.jpg "余锥，以及连接两个顶点的分解态射 h。")

```diagram
Di: (0, 0) "D\,i"
Dj: (2, 0) "D\,j"
L: (1, 1.2) "\mathrm{Colim}\,D"
c: (1, 2.4) "c"
Df: Di -> Dj "D f"
li: Di -> L "\iota_i" side=right
lj: Dj -> L "\iota_j"
ci: Di -> c "\beta_i" bend=30 side=right
cj: Dj -> c "\beta_j" bend=-30
h: L -> c "h" dashed
path "β_i": ci
path "h ∘ ι_i": li h color=green
caption: 余锥：箭头都从图指向顶点；余极限经由唯一的 h 映到任何别的余锥。
```

余极限的一个典型例子是余积，它对应于由 $\mathbf{2}$（我们在定义积时用过的那个范畴）生成的图。

![余积的排名](/img/2.2/coproductranking.jpg "余积：最好的余锥，经由唯一的 m 映到任何别的候选者。")

积和余积都体现了“一对对象”的本质，只是方式各不相同。

就像终对象是一个极限一样，始对象是对应于空范畴上的图的余极限。

拉回的对偶叫作**推出**（pushout）。它基于一种叫作**跨**（span）的图，由范畴 $1 \leftarrow 2 \rightarrow 3$ 生成。

```diagram
b: (0, 0) "b"
c: (1.6, 0) "c"
a: (0, 1.4) "a"
P: (1.6, 1.4) "P"
e: (3, 2.6) "e"
g: b -> c "g"
f: b -> a "f" side=right
i2: c -> P "\iota_2"
i1: a -> P "\iota_1" side=right
j2: c -> e "j" bend=-14
j1: a -> e "i" bend=14 side=right
h: P -> e "h" dashed
path "ι₁ ∘ f": f i1
path "ι₂ ∘ g": g i2 color=green
path "i": j1 color=orange
path "h ∘ ι₁": i1 h color=purple
caption: 推出：跨 a ← b → c 上的泛余锥。ι₁ ∘ f = ι₂ ∘ g，任何别的余锥都唯一地经由 h 分解。
```

### 补充：Type 中的余极限

和极限一样，我们可以在 Lean 里把这些余极限一个个造出来，并证明它们的泛性质。注意方向全部反过来了：唯一的态射现在是**从**余极限**出发**的。

**余积**就是 `Sum`（`a ⊕ b`）。从 `a ⊕ b` 出发的函数，被它在两个内射上的取值唯一确定：

```lean
theorem sum_uniq {a b d : Type} (i : a → d) (j : b → d) (h : a ⊕ b → d)
    (h₁ : h ∘ Sum.inl = i) (h₂ : h ∘ Sum.inr = j) :
    h = fun s => match s with | .inl x => i x | .inr y => j y := by
  funext s
  cases s with
  | inl x => exact congrFun h₁ x
  | inr y => exact congrFun h₂ y
```

**始对象**是空图的余极限，在 Lean 中就是 `Empty`：从 `Empty` 出发的函数都相等（没有元素可以让它们不同）。

```lean
theorem empty_uniq {d : Type} (h k : Empty → d) : h = k := by
  funext x; exact nomatch x
```

**推出**稍微复杂一点。直觉是：先把 `a` 和 `c` 并排放在一起（`a ⊕ c`），再把每对 `inl (f x)` 和 `inr (g x)` **粘起来**（看成同一个点）。“把某些元素看成相同”在数学上叫**商**（quotient），在 Lean 中由内置的 `Quot` 提供。

::: tip Lean 深入：商类型 `Quot`
给定类型 `α` 和一个关系 `r : α → α → Prop`，`Quot r` 是“把 `r` 相关的元素粘在一起”之后得到的类型：

- `Quot.mk r x : Quot r` —— 把 `x` 放进商里；
- `Quot.sound : r x y → Quot.mk r x = Quot.mk r y` —— 相关的元素在商里相等；
- `Quot.lift f hf : Quot r → β` —— 定义从商出发的函数，前提是 `f` 尊重 `r`（`hf : ∀ x y, r x y → f x = f y`）；
- `Quot.ind` —— 证明关于商的命题时，只需对 `Quot.mk r x` 形式的元素证明。

你会发现 `Quot.lift` 的类型签名本身就是一条泛性质：“尊重关系的函数唯一地经由商分解”。`r` 甚至不必是等价关系，Lean 会自动取它生成的等价关系。Rust 里没有对应物——这是依值类型语言的特权之一。
:::

```lean
/-- 粘合关系：inl (f x) 与 inr (g x) 粘在一起。 -/
def PushoutRel {a b c : Type} (f : b → a) (g : b → c) : a ⊕ c → a ⊕ c → Prop :=
  fun s t => ∃ x, s = .inl (f x) ∧ t = .inr (g x)

/-- Type 中跨 a ←f— b —g→ c 的推出。 -/
def Pushout {a b c : Type} (f : b → a) (g : b → c) : Type := Quot (PushoutRel f g)

namespace Pushout
variable {a b c d : Type} {f : b → a} {g : b → c}

def ι₁ : a → Pushout f g := fun x => Quot.mk _ (.inl x)
def ι₂ : c → Pushout f g := fun y => Quot.mk _ (.inr y)

/-- 方块交换：ι₁ ∘ f = ι₂ ∘ g —— 这正是粘合的效果。 -/
theorem condition : (ι₁ : a → Pushout f g) ∘ f = ι₂ ∘ g := by
  funext x
  exact Quot.sound ⟨x, rfl, rfl⟩

/-- 存在性：任何满足 i ∘ f = j ∘ g 的余锥 (d, i, j) 都有一个从推出出发的 desc。 -/
def desc (i : a → d) (j : c → d) (h : i ∘ f = j ∘ g) : Pushout f g → d :=
  Quot.lift (fun | .inl x => i x | .inr y => j y) (by
    rintro _ _ ⟨x, rfl, rfl⟩   -- 被粘起来的两个点……
    exact congrFun h x)          -- ……在 d 中的像相同

theorem desc_ι₁ (i : a → d) (j : c → d) (h : i ∘ f = j ∘ g) : desc i j h ∘ ι₁ = i := rfl
theorem desc_ι₂ (i : a → d) (j : c → d) (h : i ∘ f = j ∘ g) : desc i j h ∘ ι₂ = j := rfl

/-- 唯一性：只要在 ι₁、ι₂ 上与 i、j 一致，就等于 desc。 -/
theorem desc_uniq (i : a → d) (j : c → d) (h : i ∘ f = j ∘ g)
    (k : Pushout f g → d) (h₁ : k ∘ ι₁ = i) (h₂ : k ∘ ι₂ = j) : k = desc i j h := by
  funext z
  induction z using Quot.ind with
  | mk s =>
    cases s with
    | inl x => exact congrFun h₁ x
    | inr y => exact congrFun h₂ y

end Pushout
```

::: tip Lean 深入：`rintro` 与模式
`rintro _ _ ⟨x, rfl, rfl⟩` 一口气做了三件事：引入两个变量（用 `_` 表示不起名），再把第三个假设 `∃ x, s = … ∧ t = …` 拆开：取出 `x`，并用 `rfl` 模式直接把两个等式“代入”消掉。它相当于 `intro s t h; obtain ⟨x, hs, ht⟩ := h; subst hs; subst ht`。
:::

## 连续性

我之前说过，函子很接近“范畴之间的连续映射”这个概念，因为它们从不破坏已有的连接（态射）。从范畴 $\mathcal{C}$ 到 $\mathcal{C}'$ 的**连续函子** $F$ 的真正定义，包含了一条要求：函子要保持极限。$\mathcal{C}$ 中的每个图 $D$，只要把两个函子复合一下，就能映成 $\mathcal{C}'$ 中的图 $F \circ D$。$F$ 的连续性条件说：如果图 $D$ 有极限 $\mathrm{Lim}\,D$，那么图 $F \circ D$ 也有极限，而且它等于 $F(\mathrm{Lim}\,D)$。

![连续性：把图 D 用 F 推到 C'](/img/2.2/continuity.jpg "图 D : I → C 经 F 变成 C' 中的图 F ∘ D。F 连续，意味着 F 把 D 的极限送到 F ∘ D 的极限。")

注意，因为函子把态射映到态射、把复合映到复合，所以锥的像总是一个锥。交换三角形总是被映到交换三角形（函子保持复合）。分解态射也一样：分解态射的像也是分解态射。所以每个函子都**几乎**是连续的。可能出问题的是唯一性条件：$\mathcal{C}'$ 中的分解态射可能不唯一。$\mathcal{C}'$ 中也可能存在 $\mathcal{C}$ 里没有的“更好的锥”。

::: details 补充：函子把锥映成锥（Lean 证明）
“锥的像总是一个锥”这句话，可以写成一个 Lean 定义。证明只用到函子保持复合与恒等：

```lean
section MapCone
variable {I : Type u₁} [Category.{u₁, v₁} I] {C : Type u₂} [Category.{u₂, v₂} C]
  {C' : Type u₃} [Category.{u₃, v₃} C']

/-- 函子的复合 F ∘ D。 -/
def CTFP.CFunctor.comp (F : CFunctor C C') (D : CFunctor I C) : CFunctor I C' where
  obj i := F.obj (D.obj i)
  map f := F.map (D.map f)
  map_id i := by simp only [D.map_id, F.map_id]
  map_comp f g := by simp only [D.map_comp, F.map_comp]

/-- 锥 α : Δ c ⟹ D 在 F 下的像，是以 F c 为顶点、以 F ∘ D 为底的锥。 -/
def mapCone (F : CFunctor C C') {c : C} {D : CFunctor I C} (α : Cone c D) :
    Cone (F.obj c) (F.comp D) where
  app i := F.map (α.app i)
  naturality {i j} f := by
    show F.map (D.map f) ⊚ F.map (α.app i) = F.map (α.app j) ⊚ 𝟙 (F.obj c)
    rw [← F.map_comp, Cone.comm, Category.comp_id]

end MapCone
```
:::

hom 函子是连续函子的一个例子。回想一下，hom 函子 $\mathcal{C}(a, b)$ 在第一个变量上是逆变的，在第二个变量上是协变的。换句话说，它是一个函子：

$$\mathcal{C}^{op} \times \mathcal{C} \to \mathbf{Set}$$

当它的第二个参数固定时，hom-集函子（这时它成了可表预层）把 $\mathcal{C}$ 中的余极限映为 $\mathbf{Set}$ 中的极限；当它的第一个参数固定时，它把极限映为极限。

在 Lean 中，hom 函子就是把任意两个类型映到函数类型的映射，所以它不过是一个带参数的函数类型。当我们固定第二个参数，比如说固定为 `String`，就得到一个逆变函子。Lean 核心库没有 `Contravariant` 类型类，我们自己定义一个；另外，核心库里已经有一个叫 `ToString` 的类型类（相当于 Rust 的 `Display`），所以我们把这个函子叫作 `ToStr`：

```lean
class Contravariant (f : Type → Type) where
  contramap : (b → a) → f a → f b

/-- 固定第二个参数为 String 的 hom 函子：a ↦ (a → String)。 -/
structure ToStr (a : Type) where
  run : a → String

instance : Contravariant ToStr where
  contramap f g := ⟨g.run ∘ f⟩
```

连续性意味着：当 `ToStr` 作用于一个余极限，例如余积 `b ⊕ c` 时，它会产生一个极限；在这里，就是两个函数类型的积：

$$\mathtt{ToStr}\,(b \oplus c) \cong (b \to \mathtt{String}) \times (c \to \mathtt{String})$$

确实如此：任何以 `b ⊕ c` 为参数的函数，都是用一个分两种情形的 `match` 实现的，而这两种情形分别由一对函数来处理。Lean 让我们把这个“确实如此”写成一个双向都证明过的同构（这里结果类型取任意 `r`，`String` 只是特例）：

```lean
/-- hom 函子把余积（余极限）变成积（极限）。 -/
def homOutOfSum (b c r : Type) : (b ⊕ c → r) ≅ (b → r) × (c → r) where
  to h := (h ∘ Sum.inl, h ∘ Sum.inr)
  inv p := fun | .inl x => p.1 x | .inr y => p.2 y
  inv_to h := by funext s; cases s <;> rfl
  to_inv _ := rfl
```

类似地，当我们固定 hom-集的第一个参数时，就得到了熟悉的 Reader 函子。它的连续性意味着，比如说，任何返回积的函数都等价于一个函数的积；具体来说：

```lean
/-- hom 函子把积（极限）变成积（极限）：r → a × b ≅ (r → a) × (r → b)。 -/
def homIntoProd (r a b : Type) : (r → a × b) ≅ (r → a) × (r → b) where
  to h := (Prod.fst ∘ h, Prod.snd ∘ h)
  inv p := fun x => (p.1 x, p.2 x)
  inv_to _ := rfl
  to_inv _ := rfl
```

保持极限的不只是积。作为补充，我们看看 Reader 函子如何保持**等化子**：指向等化子的函数，恰好就是“让 $f$ 和 $g$ 相等”的那些指向 $a$ 的函数——而后者正是函数集合之间的等化子。

```lean
/-- hom 函子 (r → -) 保持等化子。 -/
def homIntoEqualizer {a b : Type} (f g : a → b) (r : Type) :
    (r → Equalizer f g) ≅ {h : r → a // f ∘ h = g ∘ h} where
  to k := ⟨Equalizer.ι ∘ k, by funext x; exact (k x).property⟩
  inv h := Equalizer.lift h.val h.property
  inv_to _ := rfl
  to_inv _ := rfl
```

::: tip Rust 视角
这几条同构在 Rust 里都是日常重构：

- 一个 `fn(Either<B, C>) -> String`（Rust 里通常写成一个 `enum` 加 `match`）总可以拆成两个函数 `fn(B) -> String` 和 `fn(C) -> String`，反之亦然；
- 一个返回元组的 `fn(R) -> (A, B)` 总可以拆成 `fn(R) -> A` 和 `fn(R) -> B`。

范畴论告诉你：这不是两个巧合，而是同一条定理（hom 函子的连续性）的两个实例。
:::

我知道你在想什么：搞清楚这些事情根本不需要范畴论。你说得对！不过，我仍然觉得很神奇：这样的结论可以从第一性原理推导出来，完全不需要诉诸比特和字节、处理器架构、编译器技术，甚至不需要 lambda 演算。

如果你好奇“极限”和“连续性”这两个名字是从哪儿来的：它们是微积分中相应概念的推广。在微积分里，极限和连续性是用开邻域来定义的。开集定义了拓扑，而开集构成一个范畴（一个偏序集）。

::: info 数学小课堂：微积分里的极限与这里的极限
微积分里，“$x_n$ 的极限是 $L$”的意思是：$L$ 的任何一个小邻域，最终都会把整个数列装进去。把“开集包含于开集”看作箭头，开集就构成一个偏序集范畴；“越来越小的邻域”是这个范畴里的一个图，而它的极限（交集）就是那个被逼近的点所在的“最小”开集（严格说是交集，未必开）。范畴论的极限正是把“被一族东西逼近的最好对象”这个想法，从数字推广到了任意范畴。连续函数则是“保持这种逼近”的函数——正对应于保持极限的函子。
:::

## 挑战

1. 你会如何描述 C++ 类范畴中的推出？
2. 证明恒等函子 $\mathbf{Id} : \mathcal{C} \to \mathcal{C}$ 的极限是始对象。
3. 一个给定集合的所有子集构成一个范畴。在这个范畴里，如果第一个集合是第二个集合的子集，就有一个箭头把它们连起来。在这样的范畴里，两个集合的拉回是什么？推出是什么？始对象和终对象是什么？
4. 你能猜出余等化子是什么吗？
5. 证明：在有终对象的范畴里，指向终对象的拉回就是积。
6. 类似地，证明：从始对象出发的推出（如果始对象存在）就是余积。

::: details 参考答案 1：C++ 类范畴中的推出
箭头从子类指向超类。推出基于跨 $B \leftarrow A \rightarrow C$，也就是 $A$ **同时继承** $B$ 和 $C$。推出 $P$ 是一个类，配上箭头 $B \to P$、$C \to P$（$B$ 和 $C$ 都继承 $P$），并且两条路径 $A \to B \to P$ 与 $A \to C \to P$ 相同（在瘦范畴里这自动成立）。“泛”意味着：$B$ 和 $C$ 的任何公共超类 $E$ 都是 $P$ 的超类。

所以 $P$ 是 $B$ 和 $C$ 的“**最具体的公共超类**”：它恰好包含 $B$ 和 $C$ 共有的东西（共同的接口），不多也不少。在 C++ 里这通常需要你手工抽出一个基类；在 Rust 里，对应的是“两个 trait 的公共 supertrait”中最小的那个——可惜 Rust 也无法自动推出它。
:::

::: details 参考答案 2：恒等函子的极限是始对象（Lean 证明）
设 $(L, \lambda)$ 是 $\mathbf{Id}$ 的极限锥，于是对每个对象 $x$ 有 $\lambda_x : L \to x$——这给出了**存在性**。

唯一性分两步：

1. 锥的每个侧面交换：对任意 $f : x \to y$，$f \circ \lambda_x = \lambda_y$。取 $f = \lambda_y$、$x = L$，得 $\lambda_y \circ \lambda_L = \lambda_y$。这说明 $\lambda_L : L \to L$ 是从极限锥到它自己的**锥态射**。而 $\mathrm{id}_L$ 也是。由极限的唯一性，$\lambda_L = \mathrm{id}_L$。
2. 对任意 $f : L \to x$，侧面交换给出 $f \circ \lambda_L = \lambda_x$，即 $f = \lambda_x$。

```lean
def idFunctor (C : Type u₂) [Category.{u₂, v₂} C] : CFunctor C C where
  obj a := a
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 从恒等函子的极限出发的任何态射，都等于锥的那条腿 —— 所以 L 是始对象。 -/
theorem limit_id_initial {C : Type u₂} [Category.{u₂, v₂} C]
    {L : ConeOver (idFunctor C)} (hL : IsLimit L) {x : C} (f : L.apex ⟶ x) :
    f = L.leg.app x := by
  -- 第一步：λ_L 是从极限锥到它自己的锥态射，所以等于恒等态射
  have hself : L.leg.app L.apex = 𝟙 L.apex := by
    let m : ConeHom L L := ⟨L.leg.app L.apex, fun i => Cone.comm L.leg (L.leg.app i)⟩
    have h1 := hL.uniq L m
    have h2 := hL.uniq L (𝟙 L)
    exact congrArg ConeHom.hom (h1.trans h2.symm)
  -- 第二步：侧面交换 f ⊚ λ_L = λ_x，再代入 λ_L = 𝟙
  have := Cone.comm L.leg f
  rw [hself] at this
  exact (Category.comp_id f).symm.trans this
```
:::

::: details 参考答案 3：子集范畴
这是一个偏序（瘦）范畴：两个对象之间最多一个箭头。在瘦范畴里，所有图都自动交换，泛性质只剩下“排名”。

- **拉回**（$A \to C \leftarrow B$，即 $A, B \subseteq C$）：要找最大的 $S$ 使 $S \subseteq A$ 且 $S \subseteq B$。答案是**交集** $A \cap B$。
- **推出**（$A \leftarrow C \rightarrow B$，即 $C \subseteq A, B$）：要找最小的 $S$ 使 $A \subseteq S$ 且 $B \subseteq S$。答案是**并集** $A \cup B$。
- **始对象**：空集 $\varnothing$（它是任何集合的子集）。
- **终对象**：整个给定集合（任何子集都包含于它）。

用谓词 `α → Prop` 表示子集，交集的泛性质就是一个“当且仅当”：

```lean
def SubsetOf {α : Type} (s t : α → Prop) : Prop := ∀ x, s x → t x

/-- S ⊆ A 且 S ⊆ B，当且仅当 S ⊆ A ∩ B —— 交集是拉回。 -/
theorem inter_is_pullback {α : Type} (A B S : α → Prop) :
    (SubsetOf S A ∧ SubsetOf S B) ↔ SubsetOf S (fun x => A x ∧ B x) :=
  ⟨fun ⟨ha, hb⟩ x hs => ⟨ha x hs, hb x hs⟩,
   fun h => ⟨fun x hs => (h x hs).1, fun x hs => (h x hs).2⟩⟩

/-- A ⊆ S 且 B ⊆ S，当且仅当 A ∪ B ⊆ S —— 并集是推出。 -/
theorem union_is_pushout {α : Type} (A B S : α → Prop) :
    (SubsetOf A S ∧ SubsetOf B S) ↔ SubsetOf (fun x => A x ∨ B x) S :=
  ⟨fun ⟨ha, hb⟩ x hx => hx.elim (ha x) (hb x),
   fun h => ⟨fun x ha => h x (Or.inl ha), fun x hb => h x (Or.inr hb)⟩⟩
```
:::

::: details 参考答案 4：余等化子（含 Lean 构造与泛性质证明）
余等化子是等化子的对偶：图仍然是两条平行箭头 $f, g : a \to b$，但余锥的箭头从图**指向**顶点。余锥是 $q : b \to d$，满足 $q \circ f = q \circ g$；余等化子是其中泛的那个。

在集合中，它是把 $b$ **商掉**“$f(z)$ 与 $g(z)$ 视为相同”（及其生成的等价关系）得到的集合。如果说等化子是“解方程”，余等化子就是“强行规定方程成立”——把所有 $f(z)$ 和 $g(z)$ 粘在一起。

```lean
def Coequalizer {a b : Type} (f g : a → b) : Type :=
  Quot (fun x y : b => ∃ z, f z = x ∧ g z = y)

namespace Coequalizer
variable {a b d : Type} {f g : a → b}

def π : b → Coequalizer f g := Quot.mk _

theorem condition : (π : b → Coequalizer f g) ∘ f = π ∘ g := by
  funext z; exact Quot.sound ⟨z, rfl, rfl⟩

/-- 存在性：任何满足 q ∘ f = q ∘ g 的 q 都经由余等化子分解。 -/
def desc (q : b → d) (hq : q ∘ f = q ∘ g) : Coequalizer f g → d :=
  Quot.lift q (by rintro _ _ ⟨z, rfl, rfl⟩; exact congrFun hq z)

theorem desc_fac (q : b → d) (hq : q ∘ f = q ∘ g) : desc q hq ∘ π = q := rfl

/-- 唯一性。 -/
theorem desc_uniq (q : b → d) (hq : q ∘ f = q ∘ g) (k : Coequalizer f g → d)
    (hk : k ∘ π = q) : k = desc q hq := by
  funext z
  induction z using Quot.ind with
  | mk y => exact congrFun hk y

end Coequalizer
```
:::

::: details 参考答案 5：指向终对象的拉回是积
设 $t$ 是终对象，$f : a \to t$、$g : b \to t$ 是（唯一的）态射。以 $d$ 为顶点的锥是一对 $p : d \to a$、$q : d \to b$，外加条件 $f \circ p = g \circ q$。但这两边都是 $d \to t$ 的态射，而终对象意味着这样的态射只有一个——所以条件**自动成立**。于是，这个余跨上的锥恰好就是一对 $(p, q)$，和积的候选者完全一样；泛锥也就是积。

在 Type 中（终对象是 `Unit`），这个同构连证明都是 `rfl`：

```lean
def pullbackTerminal (a b : Type) :
    Pullback (fun (_ : a) => ()) (fun (_ : b) => ()) ≅ a × b where
  to p := p.val
  inv p := ⟨p, rfl⟩     -- 条件 () = () 自动成立
  inv_to _ := rfl
  to_inv _ := rfl
```
:::

::: details 参考答案 6：从始对象出发的推出是余积
对偶地，设 $i$ 是始对象，$f : i \to a$、$g : i \to c$。余锥是一对 $j_1 : a \to d$、$j_2 : c \to d$，条件 $j_1 \circ f = j_2 \circ g$ 两边都是 $i \to d$ 的态射，而从始对象出发的态射只有一个，所以条件自动成立。余锥就是余积的候选者，泛余锥就是余积。

在 Type 中（始对象是 `Empty`），粘合关系永远不会被触发（没有 `x : Empty`），所以商什么也没粘：

```lean
def pushoutInitial (a c : Type) :
    Pushout (Empty.elim : Empty → a) (Empty.elim : Empty → c) ≅ a ⊕ c where
  to := Quot.lift (fun s => s) (by rintro _ _ ⟨x, _, _⟩; exact nomatch x)
  inv s := Quot.mk _ s
  inv_to z := by induction z using Quot.ind; rfl
  to_inv _ := rfl
```
:::

## 本章小结

- **图**是一个函子 $D : \mathcal{I} \to \mathcal{C}$：索引范畴 $\mathcal{I}$ 提供形状，$D$ 把形状画进 $\mathcal{C}$。“选两个对象”就是从离散范畴 $\mathbf{2}$ 出发的函子。
- **锥**是从常函子 $\Delta_c$ 到 $D$ 的自然变换。自然性方块在常函子下塌缩成交换三角形——锥的各个侧面。
- 锥与锥态射（使三角形交换的顶点间态射）构成**锥范畴**；**极限**是锥范畴的终对象，即“所有锥都唯一地经由它分解”的泛锥。
- 等价的说法：$D$ 有极限当且仅当 $\mathcal{C}(c, \mathrm{Lim}\,D) \cong \mathit{Nat}(\Delta_c, D)$ 自然地成立——“指向极限的态射 = 锥”。这个同构的自然性，恰好就是锥态射的交换条件（我们在 Lean 中两个方向都证明了）。
- 例子：积（形状 $\mathbf{2}$）、终对象（空形状）、**等化子**（两条平行箭头，Type 中是子类型 `{x // f x = g x}`）、**拉回**（余跨 $\bullet \to \bullet \leftarrow \bullet$，Type 中是 `{p : a × b // f p.1 = g p.2}`，相当于数据库的内连接）。
- 把所有箭头反过来得到**余锥**和**余极限**：余积、始对象、**推出**（跨 $\bullet \leftarrow \bullet \to \bullet$）、**余等化子**。在 Type 中，它们用 `Sum`、`Empty` 和商类型 `Quot` 构造。
- 每个泛性质都包含两部分：**存在性**（`lift`/`desc`）和**唯一性**（`lift_uniq`/`desc_uniq`）。在 Lean 中，唯一性证明几乎总是 `funext` + `Subtype.ext`/`Quot.ind` + 分量比较。
- 函子总是把锥映成锥，但未必保持极限；保持极限的函子叫**连续**函子。hom 函子是连续的：`(b ⊕ c → r) ≅ (b → r) × (c → r)`，`(r → a × b) ≅ (r → a) × (r → b)`。
