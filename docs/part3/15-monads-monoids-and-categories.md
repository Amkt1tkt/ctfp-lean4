# 3.15 单子、幺半群与范畴

一本讲范畴论的书，没有哪里是结束的好地方。要学的东西永远还有。范畴论是一门浩瀚的学科。
与此同时，有一点也显而易见：同样的主题、概念和模式一次又一次地出现。有句话说“所有概念都是 Kan 扩张”。确实，
你可以用 Kan 扩张推导出极限、余极限、伴随、单子、米田引理，以及更多的东西。范畴的概念本身出现在每一个抽象层次上，
幺半群和单子的概念也是如此。哪一个才是最基本的？事实证明，它们全都相互关联，一个引出另一个，构成一个永不终结的抽象循环。
我决定，展示这些相互联系，也许是结束这本书的好方式。

```lean hidden
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

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

structure CFunctor (C : Type u₁) [Category.{u₁, v₁} C] (D : Type u₂) [Category.{u₂, v₂} D] where
  obj : C → D
  map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id : ∀ (a : C), map (𝟙 a) = 𝟙 (obj a)
  map_comp : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c), map (g ⊚ f) = map g ⊚ map f

end CTFP

open CTFP
```

## 双范畴

范畴论最难的地方之一，是视角的不断切换。以集合范畴为例。我们习惯于用元素来定义集合：空集没有元素，单元素集有一个元素，
两个集合的笛卡尔积是序对的集合，等等。但是在谈论范畴 $\mathbf{Set}$ 时，我请你忘掉集合的内容，转而专注于集合之间的态射（箭头）。
时不时地，你可以掀开盖子偷看一眼，看看 $\mathbf{Set}$ 中的某个泛构造用元素来描述是什么样子。终对象原来是只有一个元素的集合，等等。
但这些只是“合理性检查”。

函子被定义为范畴之间的映射。把映射看作某个范畴中的态射，是很自然的。函子原来就是范畴的范畴中的态射（如果我们想避开“大小”的问题，就说是小范畴的范畴）。
把函子当作箭头，我们就放弃了关于它如何作用于范畴内部（对象和态射）的信息——就像把函数当作 $\mathbf{Set}$ 中的箭头时，我们放弃了它如何作用于集合元素的信息一样。
但任意两个范畴之间的函子也构成一个范畴。这一次，你被要求把在一个范畴中是箭头的东西，看作另一个范畴中的对象。
在函子范畴中，函子是对象，自然变换是态射。我们发现，同一个东西可以在一个范畴里是箭头，在另一个范畴里是对象。
“对象是名词、箭头是动词”这种朴素的看法站不住了。

与其在两种视角之间来回切换，不如试着把它们融为一体。这样就得到了 **2-范畴**（2-category）的概念：其中对象称为 **0-胞腔**（0-cell），
态射称为 **1-胞腔**（1-cell），而态射之间的态射称为 **2-胞腔**（2-cell）。

![2-范畴](/img/3.15/twocat.png "0-胞腔 a、b；1-胞腔 f、g；以及一个 2-胞腔 α。")

```diagram
a: (0, 0) "a"
b: (2.6, 0) "b"
top: (1.3, -0.95) ""
bot: (1.3, 0.95) ""
u: (1.3, -0.48) ""
d: (1.3, 0.48) ""
f: a -> b "f" bend=58
g: a -> b "g" bend=-58 side=right
alpha: u => d "\alpha"
caption: 两个 0-胞腔 a、b，两个 1-胞腔 f, g : a → b，以及 2-胞腔 α : f ⇒ g——“箭头之间的箭头”，从上面那条弧指向下面那条弧。
```

范畴的范畴 $\mathbf{Cat}$ 就是一个现成的例子：范畴是 0-胞腔，函子是 1-胞腔，自然变换是 2-胞腔。
2-范畴的定律告诉我们，任意两个 0-胞腔之间的 1-胞腔构成一个范畴（换句话说，$\mathcal{C}(a, b)$ 是一个 **hom-范畴**，而不仅仅是 hom-集）。
这与我们早先的论断完美吻合：任意两个范畴之间的函子构成一个函子范畴。

特别地，从任意 0-胞腔回到它自身的 1-胞腔也构成一个范畴，即 hom-范畴 $\mathcal{C}(a, a)$；但这个范畴还有更多的结构。
$\mathcal{C}(a, a)$ 的成员既可以看作 $\mathcal{C}$ 中的箭头，也可以看作 $\mathcal{C}(a, a)$ 中的对象。作为箭头，它们可以彼此复合。
但当我们把它们看作对象时，复合就变成了一个从“一对对象”到“一个对象”的映射。实际上，它看起来非常像一个积——确切地说，像一个张量积。
这个张量积有单位：恒等 1-胞腔。事实证明，在任何 2-范畴中，hom-范畴 $\mathcal{C}(a, a)$ 都自动是一个幺半范畴，其张量积就是 1-胞腔的复合。
结合律和单位律直接从相应的范畴定律中得出。

来看看这在我们的标准 2-范畴例子 $\mathbf{Cat}$ 中意味着什么。hom-范畴 $\mathbf{Cat}(a, a)$ 是 $a$ 上的自函子范畴。自函子的复合在其中扮演张量积的角色，
恒等函子是这个积的单位。我们以前见过自函子构成幺半范畴（我们在单子的定义中用到了这一点），但现在我们看到，这是一个更普遍的现象：
任何 2-范畴中的自 1-胞腔都构成幺半范畴。稍后推广单子的时候，我们还会回到这一点。

::: info 数学小课堂：胞腔（cell）的“维数”
可以这样记：0-胞腔是**点**，1-胞腔是连接两个点的**线**（箭头），2-胞腔是夹在两条平行箭头之间的**面**。
在 $\mathbf{Cat}$ 中：点 = 范畴，线 = 函子，面 = 自然变换。
1-胞腔可以首尾相接地复合（函子复合）；2-胞腔有两种复合：上下拼接（垂直复合）和左右拼接（水平复合）——这正是 1.10 章讲过的自然变换的两种复合。
:::

::: tip Lean 深入：在 $\mathbf{Cat}$ 里，1-胞腔的复合是“严格的”
来验证一下。定义函子的复合与恒等函子，然后看看结合律和单位律：

```lean
def CTFP.CFunctor.comp {C D E : Type u} [Category.{u, v} C] [Category.{u, v} D] [Category.{u, v} E]
    (G : CFunctor D E) (F : CFunctor C D) : CFunctor C E where
  obj a := G.obj (F.obj a)
  map f := G.map (F.map f)
  map_id a := by rw [F.map_id, G.map_id]
  map_comp f g := by rw [F.map_comp, G.map_comp]

def CTFP.CFunctor.ident (C : Type u) [Category.{u, v} C] : CFunctor C C where
  obj a := a
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

variable {B C D E : Type u} [Category.{u, v} B] [Category.{u, v} C] [Category.{u, v} D] [Category.{u, v} E]

/-- 张量积（= 函子复合）的结合律：严格成立，`rfl` 即可。 -/
theorem CFunctor.comp_assoc' (H : CFunctor D E) (G : CFunctor C D) (F : CFunctor B C) :
    (H.comp G).comp F = H.comp (G.comp F) := rfl

/-- 单位律：同样严格成立。 -/
theorem CFunctor.ident_comp' (F : CFunctor C D) : (CFunctor.ident D).comp F = F := rfl
theorem CFunctor.comp_ident' (F : CFunctor C D) : F.comp (CFunctor.ident C) = F := rfl
```

为什么 `rfl` 就够了？因为两边的 `obj` 和 `map` 展开后是同一个 λ 表达式，而结构体里的证明字段 `map_id`、`map_comp` 是命题——
Lean 的**证明无关性**（proof irrelevance）保证同一命题的任意两个证明在定义上相等。所以 $\mathbf{Cat}(a, a)$ 是一个**严格**幺半范畴。
:::

你也许还记得，在一般的幺半范畴中，我们并不坚持幺半群定律“严格地”（on the nose）成立。单位律和结合律在同构意义下成立，往往就足够了。
在 2-范畴中，$\mathcal{C}(a, a)$ 中的幺半定律来自 1-胞腔的复合定律。这些定律是严格的，所以我们得到的总是严格幺半范畴。
不过，这些定律也可以放松。例如，我们可以说，恒等 1-胞腔 $\mathrm{id}_a$ 与另一个 1-胞腔 $f \colon a \to b$ 的复合，**同构**于（而非等于）$f$。
1-胞腔的同构是用 2-胞腔来定义的。换句话说，存在一个 2-胞腔：

$$\rho \colon f \circ \mathrm{id}_a \to f$$

并且它有逆。

![双范畴中的单位律](/img/3.15/bicat.png "双范畴中的单位律只在同构意义下成立（由一个可逆的 2-胞腔 ρ 给出）。")

对左单位律和结合律，我们也可以这样做。这种放松了的 2-范畴称为**双范畴**（bicategory）（还有一些额外的相干性定律，这里我略去不谈）。

不出所料，双范畴中的自 1-胞腔构成一个一般的、定律非严格的幺半范畴。

一个有趣的双范畴例子是 **span** 的范畴。两个对象 $a$ 和 $b$ 之间的一个 **span**（有时译作“跨”）是一个对象 $x$ 加上一对态射：

$$f \colon x \to a$$

$$g \colon x \to b$$

![一个 span](/img/3.15/span.png "从 a 到 b 的一个 span：顶点 x，以及两条腿 f : x → a、g : x → b。")

```diagram
x: (1, 0) "x"
a: (0, 1.2) "a"
b: (2, 1.2) "b"
f: x -> a "f" side=right
g: x -> b "g"
caption: span a ← x → b。它“从 a 指向 b”，尽管两条腿都从 x 出发。
```

你也许还记得，我们在定义范畴积的时候用过 span。在这里，我们想把 span 看作一个双范畴中的 1-胞腔。第一步是定义 span 的复合。
假设我们有一个与之相邻的 span：

$$f' \colon y \to b$$

$$g' \colon y \to c$$

![两个相邻的 span](/img/3.15/compspan.png "两个首尾相接的 span：a ← x → b 和 b ← y → c，共享中间的对象 b。")

复合将是第三个 span，顶点是某个 $z$。最自然的选择是 $g$ 沿 $f'$ 的**拉回**。记得拉回是对象 $z$ 加上两个态射：

$$h \colon z \to x$$

$$h' \colon z \to y$$

使得：

$$g \circ h = f' \circ h'$$

并且它在所有这样的对象中是泛的。

![span 的复合：拉回](/img/3.15/pullspan.png "复合的顶点 z 是 g 沿 f' 的拉回；新 span 的两条腿是 f ∘ h 和 g' ∘ h'。")

```diagram
z: (2, 0) "z"
x: (1, 1) "x"
y: (3, 1) "y"
a: (0, 2) "a"
b: (2, 2) "b"
c: (4, 2) "c"
h: z -> x "h" side=right
h2: z -> y "h'"
f: x -> a "f" side=right
g: x -> b "g"
f2: y -> b "f'" side=right
g2: y -> c "g'"
path "g ∘ h": h g
path "f' ∘ h'": h2 f2 color=green
caption: 拉回方块交换：从 z 到 b 的两条路相同。复合后的 span 是 a ← z → c，腿为 f ∘ h 与 g' ∘ h'。
```

现在，我们先专注于集合范畴上的 span。在这种情况下，拉回就是笛卡尔积 $x \times y$ 中满足下式的序对 $(p, q)$ 的集合：

$$g\ p = f'\ q$$

两个端点相同的 span 之间的态射，定义为它们顶点之间的一个态射 $h$，使得相应的三角形交换。

![span 之间的态射](/img/3.15/morphspan.png "Span 中的一个 2-胞腔：顶点之间的映射 h，使两边的三角形都交换。")

```diagram
x: (1.2, 0) "x"
x2: (1.2, 1.1) "x'"
a: (0, 2.3) "a"
b: (2.4, 2.3) "b"
h: x -> x2 "h"
f: x -> a "f" bend=-45 side=right
g: x -> b "g" bend=45
f2: x2 -> a "f'"
g2: x2 -> b "g'" side=right
path "f' ∘ h": h f2
path "f": f color=green
path "g' ∘ h": h g2 color=purple
path "g": g color=orange
caption: 2-胞腔 h : x → x'：f' ∘ h = f，g' ∘ h = g——两个三角形都交换。
```

总结一下，在双范畴 $\mathbf{Span}$ 中：0-胞腔是集合，1-胞腔是 span，2-胞腔是 span 的态射。恒等 1-胞腔是一个退化的 span：三个对象都相同，两个态射都是恒等态射。

我们以前还见过一个双范畴的例子：[剖函子](/part3/10-ends-and-coends)的双范畴 $\mathbf{Prof}$。其中 0-胞腔是范畴，1-胞腔是剖函子，2-胞腔是自然变换。剖函子的复合由一个余端给出。

### 补充：在 Lean 里搭出 $\mathbf{Span}$

我们把集合上的 span（用 Lean 的类型代替集合）写出来。一个从 `A` 到 `B` 的 span 就是一个顶点类型加两条腿：

```lean
structure Span (A B : Type) where
  apex : Type
  src  : apex → A    -- 左腿 f
  tgt  : apex → B    -- 右腿 g
```

恒等 span 和复合。复合的顶点是拉回：满足 `s.tgt x = t.src y` 的序对 `(x, y)` 组成的**子类型**（subtype）。

```lean
namespace Span

/-- 恒等 1-胞腔：A ← A → A，两条腿都是恒等函数。 -/
def id (A : Type) : Span A A := ⟨A, fun a => a, fun a => a⟩

/-- 复合 t ⊙ s：先 s : A ⇸ B，再 t : B ⇸ C（与 g ∘ f 的书写顺序一致）。顶点是拉回。 -/
def comp {A B C : Type} (t : Span B C) (s : Span A B) : Span A C where
  apex := { p : s.apex × t.apex // s.tgt p.1 = t.src p.2 }
  src p := s.src p.val.1
  tgt p := t.tgt p.val.2

scoped infixr:80 " ⊙ " => comp

/-- 2-胞腔：顶点之间的函数，使两个三角形交换。 -/
structure Hom {A B : Type} (s t : Span A B) where
  map      : s.apex → t.apex
  src_comm : ∀ x, t.src (map x) = s.src x
  tgt_comm : ∀ x, t.tgt (map x) = s.tgt x

def Hom.id {A B : Type} (s : Span A B) : Hom s s := ⟨fun x => x, fun _ => rfl, fun _ => rfl⟩

/-- 2-胞腔的垂直复合。 -/
def Hom.vcomp {A B : Type} {s t u : Span A B} (β : Hom t u) (α : Hom s t) : Hom s u where
  map x := β.map (α.map x)
  src_comm x := by rw [β.src_comm, α.src_comm]
  tgt_comm x := by rw [β.tgt_comm, α.tgt_comm]

/-- 两个 2-胞腔相等，只要它们的 `map` 相等（交换性证明是命题，自动相等）。 -/
theorem Hom.ext {A B : Type} {s t : Span A B} {α β : Hom s t} (h : α.map = β.map) : α = β := by
  cases α; cases β; cases h; rfl

end Span
```

::: tip Lean 深入：子类型 `{ p : X // P p }`
`{ p : s.apex × t.apex // s.tgt p.1 = t.src p.2 }` 是**子类型**：它的元素是一个值 `p.val` 加上一个证明 `p.property : P p.val`。
这正是集合论里的 $\{(p, q) \in x \times y \mid g\,p = f'\,q\}$。构造元素时写 `⟨(x, y), 证明⟩`。
Rust 里没有直接对应物；最接近的是“只能通过检查过的构造函数创建”的 newtype（比如 `NonZeroU32`），只不过 Lean 把检查变成了编译期证明。
:::

现在来看看为什么 $\mathbf{Span}$ 只是**双**范畴，而不是 2-范畴。`s ⊙ Span.id A` 的顶点是 `{ p : A × s.apex // p.1 = s.src p.2 }`——
一个**序对**的子类型，而 `s` 的顶点是 `s.apex`。这是两个不同的类型，`s ⊙ Span.id A = s` 根本无从谈起。
但它们之间有一对互逆的 2-胞腔，这正是上图中的 $\rho$：

```lean
open Span

/-- 右单位子 ρ : s ⊙ id ⇒ s：丢掉序对中多余的那一半。 -/
def Span.rho {A B : Type} (s : Span A B) : Hom (s ⊙ Span.id A) s where
  map p := p.val.2
  src_comm p := p.property.symm
  tgt_comm _ := rfl

/-- ρ 的逆：x ↦ (s.src x, x)。 -/
def Span.rhoInv {A B : Type} (s : Span A B) : Hom s (s ⊙ Span.id A) where
  map x := ⟨(s.src x, x), rfl⟩
  src_comm _ := rfl
  tgt_comm _ := rfl

theorem Span.rho_rhoInv {A B : Type} (s : Span A B) : (rho s).vcomp (rhoInv s) = Hom.id s := rfl

theorem Span.rhoInv_rho {A B : Type} (s : Span A B) : (rhoInv s).vcomp (rho s) = Hom.id _ := by
  apply Hom.ext
  funext p
  -- p = ⟨(a, x), h⟩，其中 h : a = s.src x。要证 (s.src x, x) = (a, x)。
  exact Subtype.ext (Prod.ext p.property.symm rfl)

/-- 左单位子 λ : id ⊙ s ⇒ s 与它的逆。 -/
def Span.lam {A B : Type} (s : Span A B) : Hom (Span.id B ⊙ s) s where
  map p := p.val.1
  src_comm _ := rfl
  tgt_comm p := p.property

def Span.lamInv {A B : Type} (s : Span A B) : Hom s (Span.id B ⊙ s) where
  map x := ⟨(x, s.tgt x), rfl⟩
  src_comm _ := rfl
  tgt_comm _ := rfl

/-- 结合子：((u ⊙ t) ⊙ s) ⇒ (u ⊙ (t ⊙ s))，只是把嵌套的序对重新加括号。 -/
def Span.assoc {A B C D : Type} (u : Span C D) (t : Span B C) (s : Span A B) :
    Hom ((u ⊙ t) ⊙ s) (u ⊙ (t ⊙ s)) where
  map p := ⟨(⟨(p.val.1, p.val.2.val.1), p.property⟩, p.val.2.val.2), p.val.2.property⟩
  src_comm _ := rfl
  tgt_comm _ := rfl
```

把这一段和上面 $\mathbf{Cat}$ 的 `rfl` 对比一下：在 $\mathbf{Cat}$ 中单位律是**等式**，在 $\mathbf{Span}$ 中只是**同构**。这就是“双范畴”这个词的全部意义所在。

为了稍后定义单子，我们还需要 2-胞腔与 1-胞腔的“水平”复合，称为**须化**（whiskering）：把一个 2-胞腔放在一个 1-胞腔旁边。

```lean
/-- 左须化 t ◁ α：在 t ⊙ s 中，α 作用在 s 那一侧。 -/
def Span.whiskerL {A B C : Type} (t : Span B C) {s s' : Span A B} (α : Hom s s') :
    Hom (t ⊙ s) (t ⊙ s') where
  map p := ⟨(α.map p.val.1, p.val.2), by rw [α.tgt_comm]; exact p.property⟩
  src_comm p := by simp only [comp]; rw [α.src_comm]
  tgt_comm _ := rfl

/-- 右须化 α ▷ s：在 t ⊙ s 中，α 作用在 t 那一侧。 -/
def Span.whiskerR {A B C : Type} {t t' : Span B C} (α : Hom t t') (s : Span A B) :
    Hom (t ⊙ s) (t' ⊙ s) where
  map p := ⟨(p.val.1, α.map p.val.2), by rw [α.src_comm]; exact p.property⟩
  src_comm _ := rfl
  tgt_comm p := by simp only [comp]; rw [α.tgt_comm]
```

## 单子

到现在，你应该已经相当熟悉“单子是自函子范畴中的幺半群”这个定义了。让我们带着新的理解重温它：自函子范畴只是双范畴 $\mathbf{Cat}$ 中自 1-胞腔的一个小小的 hom-范畴。
我们知道它是一个幺半范畴：张量积来自自函子的复合。幺半群被定义为幺半范畴中的一个对象——这里是一个自函子 $T$——加上两个态射。
自函子之间的态射是自然变换。一个态射把幺半单位——恒等自函子——映到 $T$：

$$\eta \colon I \to T$$

第二个态射把张量积 $T \otimes T$ 映到 $T$。张量积由自函子的复合给出，所以我们得到：

$$\mu \colon T \circ T \to T$$

![单子作为幺半群](/img/3.15/monad.png "单子：自函子 T 加上两个自然变换 η : I → T 与 μ : T ∘ T → T。")

我们认出，这正是定义单子的两个运算（在 Lean 中是 `pure` 和 `join`；Haskell 叫 `return` 和 `join`），而且我们知道，幺半群定律变成了单子定律。

::: tip Lean 深入：把 `List` 写成“幺半群”的样子
Lean 的 `Monad` 类用 `pure` 和 `bind` 定义；`join` 可以由 `bind` 得到。对 `List`，`join` 就是 `List.flatten`。
三条单子定律写成“幺半群”形式，就是 $\mu \circ \eta T = \mathrm{id}$、$\mu \circ T\eta = \mathrm{id}$（两条单位律）和 $\mu \circ \mu T = \mu \circ T\mu$（结合律）：

```lean
def joinL {α : Type} (xss : List (List α)) : List α := xss.flatten

/-- 左单位律：μ ∘ ηT = id（把整个列表包成单元素列表，再拍平） -/
theorem joinL_pure {α : Type} (xs : List α) : joinL [xs] = xs := by
  simp [joinL]

/-- 右单位律：μ ∘ Tη = id（把每个元素包成单元素列表，再拍平） -/
theorem joinL_map_pure {α : Type} (xs : List α) : joinL (xs.map fun x => [x]) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [joinL]

/-- 结合律：μ ∘ μT = μ ∘ Tμ（三层列表，先拍外面两层还是先拍里面两层，结果一样） -/
theorem joinL_joinL {α : Type} (xsss : List (List (List α))) :
    joinL (joinL xsss) = joinL (xsss.map joinL) := by
  show List.flatten (List.flatten xsss) = List.flatten (xsss.map List.flatten)
  exact List.flatten_flatten
```
:::

::: tip Rust 视角
`Option::flatten`、`Iterator::flatten` 都是 $\mu$；`Some`、`std::iter::once` 是 $\eta$。“先拍平外层还是先拍平内层都一样”，
就是你在 Rust 里写 `vvv.into_iter().flatten().flatten()` 时从不担心括号的原因。
:::

现在，让我们从这个定义中去掉所有关于自函子的字眼。我们从一个双范畴 $\mathcal{C}$ 出发，在其中选一个 0-胞腔 $a$。
正如我们之前看到的，hom-范畴 $\mathcal{C}(a, a)$ 是一个幺半范畴。因此我们可以在 $\mathcal{C}(a, a)$ 中定义一个幺半群：选一个 1-胞腔 $T$ 和两个 2-胞腔

$$\eta \colon I \to T$$

$$\mu \colon T \circ T \to T$$

并要求它们满足幺半群定律。我们把**这个**叫作单子。

![双范畴中的单子](/img/3.15/bimonad.png "双范畴中的单子：0-胞腔 a 上的自 1-胞腔 T，以及 2-胞腔 η : id ⇒ T 和 μ : T ∘ T ⇒ T。")

这是一个只用到 0-胞腔、1-胞腔和 2-胞腔的、普遍得多的单子定义。把它用到双范畴 $\mathbf{Cat}$ 上，就退化为通常的单子。但让我们看看在别的双范畴中会发生什么。

我们在 $\mathbf{Span}$ 中构造一个单子。先选一个 0-胞腔，它是一个集合；出于马上就会清楚的原因，我把它叫作 $\mathit{Ob}$。
接着选一个自 1-胞腔：一个从 $\mathit{Ob}$ 回到 $\mathit{Ob}$ 的 span。它的顶点是一个集合，我叫它 $\mathit{Arr}$，配有两个函数：

$$\mathit{dom} \colon \mathit{Arr} \to \mathit{Ob}$$

$$\mathit{cod} \colon \mathit{Arr} \to \mathit{Ob}$$

![Span 中的自 1-胞腔](/img/3.15/spanmonad.png "Span 中从 Ob 到 Ob 的一个自 1-胞腔：顶点 Arr，两条腿 dom 与 cod。")

```diagram
Arr: (1, 0) "\mathit{Arr}"
Ob1: (0, 1.2) "\mathit{Ob}"
Ob2: (2, 1.2) "\mathit{Ob}"
dom: Arr -> Ob1 "\mathit{dom}" side=right
cod: Arr -> Ob2 "\mathit{cod}"
caption: 自 1-胞腔 T：Ob ← Arr → Ob。
```

我们把集合 $\mathit{Arr}$ 的元素叫作“箭头”。如果我再让你把 $\mathit{Ob}$ 的元素叫作“对象”，你大概就能猜到这是要往哪里去了。
两个函数 $\mathit{dom}$ 和 $\mathit{cod}$ 给每个“箭头”指定定义域和陪域。

要把我们的 span 变成单子，需要两个 2-胞腔 $\eta$ 和 $\mu$。在这里，幺半单位是从 $\mathit{Ob}$ 到 $\mathit{Ob}$ 的平凡 span：顶点是 $\mathit{Ob}$，两条腿是恒等函数。
2-胞腔 $\eta$ 是两个顶点 $\mathit{Ob}$ 与 $\mathit{Arr}$ 之间的一个函数。换句话说，$\eta$ 给每个“对象”指定一个“箭头”。
$\mathbf{Span}$ 中的 2-胞腔必须满足交换条件——在这里是：

$$\mathit{dom} \circ \eta = \mathrm{id}$$

$$\mathit{cod} \circ \eta = \mathrm{id}$$

![单位 η](/img/3.15/spanunit.png "2-胞腔 η：从恒等 span（顶点 Ob）到 T（顶点 Arr）的映射，两个三角形都交换。")

```diagram
Ob: (1.2, 0) "\mathit{Ob}"
Arr: (1.2, 1.1) "\mathit{Arr}"
L: (0, 2.3) "\mathit{Ob}"
R: (2.4, 2.3) "\mathit{Ob}"
eta: Ob -> Arr "\eta"
idL: Ob -> L "\mathrm{id}" bend=-45 side=right
idR: Ob -> R "\mathrm{id}" bend=45
dom: Arr -> L "\mathit{dom}"
cod: Arr -> R "\mathit{cod}" side=right
path "dom ∘ η": eta dom
path "id": idL color=green
path "cod ∘ η": eta cod color=purple
path "id ": idR color=orange
caption: η 的两个交换三角形：恒等箭头的定义域和陪域都是它所属的那个对象。
```

写成分量形式就是：

$$\mathit{dom}\ (\eta\ \mathit{ob}) = \mathit{ob} = \mathit{cod}\ (\eta\ \mathit{ob})$$

其中 $\mathit{ob}$ 是 $\mathit{Ob}$ 中的一个“对象”。换句话说，$\eta$ 给每个“对象”指定一个“箭头”，其定义域和陪域都是这个“对象”。我们把这个特殊的“箭头”称为“恒等箭头”。

第二个 2-胞腔 $\mu$ 作用在 span $\mathit{Arr}$ 与它自身的复合上。复合被定义为拉回，所以它的元素是 $\mathit{Arr}$ 中元素的序对——“箭头”对 $(a_1, a_2)$。拉回条件是：

$$\mathit{cod}\ a_1 = \mathit{dom}\ a_2$$

我们说 $a_1$ 和 $a_2$ 是“可复合的”，因为一个的陪域是另一个的定义域。

![T ∘ T 的顶点](/img/3.15/spanmul.png "T ∘ T 的顶点 Arr ⊗ Arr 是拉回：所有满足 cod a₁ = dom a₂ 的箭头对，也就是可复合的箭头对。")

```diagram
P: (2, 0) "\mathit{Arr} \otimes \mathit{Arr}"
A1: (1, 1) "\mathit{Arr}"
A2: (3, 1) "\mathit{Arr}"
O0: (0, 2) "\mathit{Ob}"
O1: (2, 2) "\mathit{Ob}"
O2: (4, 2) "\mathit{Ob}"
p1: P -> A1 "\pi_1" side=right
p2: P -> A2 "\pi_2"
d1: A1 -> O0 "\mathit{dom}" side=right
c1: A1 -> O1 "\mathit{cod}"
d2: A2 -> O1 "\mathit{dom}" side=right
c2: A2 -> O2 "\mathit{cod}"
path "cod ∘ π₁": p1 c1
path "dom ∘ π₂": p2 d2 color=green
caption: 拉回条件 cod a₁ = dom a₂：中间那个 Ob 被两条路走到同一个点。
```

2-胞腔 $\mu$ 是一个函数，把一对可复合的“箭头” $(a_1, a_2)$ 映到 $\mathit{Arr}$ 中的单个“箭头” $a_3$。换句话说，$\mu$ 定义了“箭头”的复合。

很容易验证，单子定律对应于箭头的恒等律和结合律。我们刚刚定义了一个范畴（请注意，是一个小范畴，其对象和箭头构成集合）。

所以，总而言之，**一个范畴就是 span 双范畴中的一个单子**。

这个结果的惊人之处在于，它把范畴与单子、幺半群这些其他代数结构放在了同等的地位上。作为一个范畴，并没有什么特别之处。它只不过是两个集合和四个函数。
事实上，我们甚至不需要单独的对象集合，因为对象可以与恒等箭头认同（它们一一对应）。所以它实际上只是一个集合和几个函数。
考虑到范畴论在整个数学中所扮演的关键角色，这是一个令人谦卑的认识。

### 补充：在 Lean 里验证“范畴 = Span 中的单子”

“很容易验证”——那我们就真的验证一下。先把 $\mathbf{Span}$ 中的单子写成一个结构体。三条定律用前面定义的单位子、结合子和须化来表达，
和幺半群定律 $\mu \circ (\eta \otimes \mathrm{id}) = \lambda$、$\mu \circ (\mathrm{id} \otimes \eta) = \rho$、$\mu \circ (\mu \otimes \mathrm{id}) = \mu \circ (\mathrm{id} \otimes \mu) \circ \alpha$ 一一对应：

```lean
structure SpanMonad (Ob : Type) where
  T : Span Ob Ob
  η : Hom (Span.id Ob) T
  μ : Hom (T ⊙ T) T
  /-- (a, η (cod a)) ↦ a -/
  left_unit  : μ.vcomp ((Span.whiskerR η T).vcomp (Span.lamInv T)) = Hom.id T
  /-- (η (dom a), a) ↦ a -/
  right_unit : μ.vcomp ((Span.whiskerL T η).vcomp (Span.rhoInv T)) = Hom.id T
  /-- 先把后两个复合，还是先把前两个复合，结果一样 -/
  assoc : μ.vcomp (Span.whiskerR μ T) = μ.vcomp ((Span.whiskerL T μ).vcomp (Span.assoc T T T))
```

再把“小范畴”直接写成“两个集合和四个函数”外加定律。注意复合 `comp a₁ a₂ h` 需要一个证明 `h : cod a₁ = dom a₂`——只有可复合的箭头才能复合：

```lean
/-- 小范畴：两个集合（Ob, Arr）和四个函数（dom, cod, idArr, comp）。 -/
structure SmallCat where
  Ob    : Type
  Arr   : Type
  dom   : Arr → Ob
  cod   : Arr → Ob
  idArr : Ob → Arr
  /-- `comp a₁ a₂ h`：先 `a₁` 再 `a₂`。 -/
  comp  : (a₁ a₂ : Arr) → cod a₁ = dom a₂ → Arr
  dom_id   : ∀ o, dom (idArr o) = o
  cod_id   : ∀ o, cod (idArr o) = o
  dom_comp : ∀ a₁ a₂ h, dom (comp a₁ a₂ h) = dom a₁
  cod_comp : ∀ a₁ a₂ h, cod (comp a₁ a₂ h) = cod a₂
  id_comp  : ∀ a h, comp (idArr (dom a)) a h = a
  comp_id  : ∀ a h, comp a (idArr (cod a)) h = a
  assoc    : ∀ a₁ a₂ a₃ h₁₂ h₂₃ h h',
    comp (comp a₁ a₂ h₁₂) a₃ h = comp a₁ (comp a₂ a₃ h₂₃) h'
```

现在是两个方向的翻译。从单子到范畴：`Arr` 是 `T` 的顶点，`dom`/`cod` 是两条腿，`idArr` 是 `η`，`comp` 是 `μ`。
`dom_id` 等四条“定义域/陪域”定律，正是 `η`、`μ` 作为 2-胞腔的交换条件；而单位律与结合律，则是把单子定律在具体元素上取值：

```lean
def SpanMonad.toCat {Ob : Type} (M : SpanMonad Ob) : SmallCat where
  Ob    := Ob
  Arr   := M.T.apex
  dom   := M.T.src
  cod   := M.T.tgt
  idArr := M.η.map
  comp a₁ a₂ h := M.μ.map ⟨(a₁, a₂), h⟩
  dom_id := M.η.src_comm
  cod_id := M.η.tgt_comm
  dom_comp a₁ a₂ h := M.μ.src_comm ⟨(a₁, a₂), h⟩
  cod_comp a₁ a₂ h := M.μ.tgt_comm ⟨(a₁, a₂), h⟩
  -- 单子的右单位律，在元素 a 上取值
  id_comp a _ := congrArg (fun α => α.map a) M.right_unit
  -- 单子的左单位律，在元素 a 上取值
  comp_id a _ := congrArg (fun α => α.map a) M.left_unit
  -- 单子的结合律，在三元组 (a₁, (a₂, a₃)) 上取值
  assoc a₁ a₂ a₃ h₁₂ h₂₃ _ _ :=
    (congrArg (fun α => α.map ⟨(a₁, ⟨(a₂, a₃), h₂₃⟩), h₁₂⟩) M.assoc).symm
```

反过来，从范畴到单子：

```lean
def SmallCat.toSpanMonad (C : SmallCat) : SpanMonad C.Ob where
  T := ⟨C.Arr, C.dom, C.cod⟩
  η := ⟨C.idArr, C.dom_id, C.cod_id⟩
  μ := ⟨fun p => C.comp p.val.1 p.val.2 p.property,
        fun _ => C.dom_comp _ _ _, fun _ => C.cod_comp _ _ _⟩
  left_unit := by
    apply Hom.ext; funext a
    exact C.comp_id a _
  right_unit := by
    apply Hom.ext; funext a
    exact C.id_comp a _
  assoc := by
    apply Hom.ext; funext ⟨⟨a₁, ⟨⟨a₂, a₃⟩, h₂₃⟩⟩, h⟩
    exact (C.assoc a₁ a₂ a₃ h h₂₃ _ _).symm
```

::: tip Lean 深入：`congrArg`
`congrArg f h : f x = f y`，其中 `h : x = y`——“相等的东西代入同一个函数，结果仍相等”。
这里 `M.left_unit` 是两个 2-胞腔相等，我们用 `congrArg (fun α => α.map a)` 把它“求值”在元素 `a` 上，就得到关于箭头的等式。
Lean 会自动展开 `vcomp`、`whiskerR`、`lamInv` 的定义，看出左边恰好是 `comp a (idArr (cod a)) _`。
:::

最后来两个例子。第一个是预序 $0 \le 1 \le 2$（1.3 章说过，预序是“每两个对象间至多一个箭头”的范畴）：

```lean
/-- 预序 Fin 3 上的 ≤：箭头 (i, j) 存在当且仅当 i ≤ j。 -/
def leCat : SmallCat where
  Ob    := Fin 3
  Arr   := { p : Fin 3 × Fin 3 // p.1 ≤ p.2 }
  dom a := a.val.1
  cod a := a.val.2
  idArr o := ⟨(o, o), Fin.le_refl o⟩
  comp a₁ a₂ h := ⟨(a₁.val.1, a₂.val.2), Fin.le_trans a₁.property (h ▸ a₂.property)⟩
  dom_id _ := rfl
  cod_id _ := rfl
  dom_comp _ _ _ := rfl
  cod_comp _ _ _ := rfl
  id_comp _ _ := rfl
  comp_id _ _ := rfl
  assoc _ _ _ _ _ _ _ := rfl

/-- 复合 (0 ≤ 1) 与 (1 ≤ 2)，得到 (0 ≤ 2)。 -/
example : (leCat.comp ⟨(0, 1), by decide⟩ ⟨(1, 2), by decide⟩ rfl).val = (0, 2) := rfl
```

第二个回到本章标题里的“幺半群”：**幺半群就是只有一个对象的范畴**（1.3 章）。所以它也是 $\mathbf{Span}$ 中、建在单元素集 `Unit` 上的单子：

```lean
/-- (ℕ, +, 0) 作为单对象范畴：唯一的对象是 ()，箭头是自然数，复合是加法。 -/
def natAddCat : SmallCat where
  Ob    := Unit
  Arr   := Nat
  dom _ := ()
  cod _ := ()
  idArr _ := 0
  comp a b _ := a + b
  dom_id _ := rfl
  cod_id _ := rfl
  dom_comp _ _ _ := rfl
  cod_comp _ _ _ := rfl
  id_comp a _ := Nat.zero_add a
  comp_id a _ := Nat.add_zero a
  assoc a b c _ _ _ _ := Nat.add_assoc a b c

/-- 同一个幺半群，作为 Span 中 Unit 上的单子；μ 就是加法。 -/
def natAddMonad : SpanMonad Unit := natAddCat.toSpanMonad

example : natAddMonad.μ.map ⟨((2 : Nat), (3 : Nat)), rfl⟩ = (5 : Nat) := rfl
```

于是一个完整的圆圈闭合了：**单子**是（自函子范畴中的）**幺半群**；**范畴**是（span 双范畴中的）**单子**；而**幺半群**又是（只有一个对象的）**范畴**。

下面的组件把“span 中的单子”摊开来给你看：左右两列是 $\mathit{Ob}$，中间一列是 $\mathit{Arr}$，连线就是 $\mathit{dom}$ 和 $\mathit{cod}$。
下面列出拉回 $T \circ T$ 的所有元素——它们恰好是所有可复合的箭头对；点一对，看 $\mu$ 把它送到哪里。

<div class="ctfp-widget-host"><Ch3_15SpanMonad /></div>

## 挑战

1. 推导双范畴中“定义为自 1-胞腔复合的张量积”的单位律和结合律。
2. 验证：$\mathbf{Span}$ 中单子的单子定律，对应于所得范畴中的恒等律与结合律。
3. 证明：$\mathbf{Prof}$ 中的单子是一个对象上恒等的函子。
4. $\mathbf{Span}$ 中单子的单子代数是什么？

::: details 参考答案
**1.** 在双范畴 $\mathcal{C}$ 中固定 0-胞腔 $a$，在 hom-范畴 $\mathcal{C}(a, a)$ 上定义 $f \otimes g = f \circ g$，单位对象 $I = \mathrm{id}_a$。
双范畴的数据直接给出幺半范畴所需的三个自然同构：

- 左单位子 $\lambda_f \colon \mathrm{id}_a \circ f \Rightarrow f$；
- 右单位子 $\rho_f \colon f \circ \mathrm{id}_a \Rightarrow f$；
- 结合子 $\alpha_{h,g,f} \colon (h \circ g) \circ f \Rightarrow h \circ (g \circ f)$。

它们都是可逆的 2-胞腔，并且对 2-胞腔自然（自然性来自 2-胞腔的水平复合与垂直复合之间的交换律）。
双范畴的相干性公理（五边形与三角形等式）恰好就是幺半范畴的五边形与三角形等式，所以 $\mathcal{C}(a, a)$ 是一个（一般非严格的）幺半范畴。
在严格的 2-范畴中，这三个同构都是恒等，就得到严格幺半范畴——正如我们在 Lean 中看到的，$\mathbf{Cat}$ 的单位律与结合律都是 `rfl`。
而在 $\mathbf{Span}$ 中，我们给出了 `Span.rho`/`Span.rhoInv`、`Span.lam`/`Span.lamInv` 和 `Span.assoc`，并证明了 `rho` 与 `rhoInv` 互逆
（`lam` 的情形完全类似）。

**2.** 这正是上面 `SpanMonad.toCat` 与 `SmallCat.toSpanMonad` 两个函数所做的事，它们都通过了编译：

- $\eta$、$\mu$ 作为 2-胞腔的交换条件 ⟺ `dom_id`、`cod_id`、`dom_comp`、`cod_comp`（恒等箭头从对象到它自身；复合的定义域/陪域正确）；
- 单子的右单位律 $\mu \circ (T \triangleleft \eta) \circ \rho^{-1} = \mathrm{id}$ 在元素 $a$ 上取值 ⟺ $\mathrm{id}_{\mathit{dom}\,a}$ 后接 $a$ 等于 $a$；
- 单子的左单位律 ⟺ $a$ 后接 $\mathrm{id}_{\mathit{cod}\,a}$ 等于 $a$；
- 单子的结合律在可复合三元组 $(a_1, (a_2, a_3))$ 上取值 ⟺ 箭头复合的结合律。

**3.** $\mathbf{Prof}$ 中，范畴 $\mathcal{C}$ 上的一个单子是一个剖函子 $P \colon \mathcal{C}^{op} \times \mathcal{C} \to \mathbf{Set}$，以及两个自然变换
$\eta \colon \mathcal{C}(-, =) \Rightarrow P$（恒等剖函子是 hom-函子）和 $\mu \colon P \diamond P \Rightarrow P$，其中复合是余端
$(P \diamond P)(a, c) = \int^b P(a, b) \times P(b, c)$。

构造一个新范畴 $\mathcal{D}$：对象与 $\mathcal{C}$ 相同，$\mathcal{D}(a, b) = P(a, b)$。复合由 $\mu$ 给出：一对 $(p, q) \in P(a, b) \times P(b, c)$ 先进入余端（余楔），再被 $\mu$ 送到 $P(a, c)$；
恒等箭头是 $\eta(\mathrm{id}_a)$。单子的单位律与结合律就是 $\mathcal{D}$ 的单位律与结合律。函子 $J \colon \mathcal{C} \to \mathcal{D}$ 在对象上是恒等，在态射上由 $\eta$ 给出：$f \mapsto \eta(f)$。
$\eta$ 的自然性保证 $J$ 保持复合。反过来，给定一个对象上恒等的函子 $J \colon \mathcal{C} \to \mathcal{D}$，令 $P(a, b) = \mathcal{D}(J a, J b)$，$\mathcal{C}$ 通过 $J$ 在两边作用，
$\eta = J$，$\mu$ 就是 $\mathcal{D}$ 中的复合（余端的认同关系恰好被 $\mathcal{D}$ 的结合律尊重）。两个构造互逆。

**4.** 双范畴中，单子 $(T, \eta, \mu)$（在 0-胞腔 $\mathit{Ob}$ 上）的一个代数，是一个 1-胞腔 $s \colon c \to \mathit{Ob}$ 加上一个 2-胞腔 $\alpha \colon T \circ s \Rightarrow s$，满足通常的两条代数定律。
取 $c$ 为单元素集，span $1 \leftarrow X \to \mathit{Ob}$ 就是一个集合 $X$ 加一个函数 $p \colon X \to \mathit{Ob}$（把 $X$ 的元素“放在”各个对象上方）。
$T \circ s$ 的顶点是 $\{(x, a) \mid p\,x = \mathit{dom}\,a\}$，$\alpha$ 则把这样的一对送到 $X$ 中的一个元素，使其位于 $\mathit{cod}\,a$ 上方：箭头 $a$ “把 $a$ 定义域上方的元素推到陪域上方”。
两条代数定律说的是：恒等箭头什么都不推，复合箭头的推送等于依次推送。这正是一个函子 $\mathcal{C} \to \mathbf{Set}$（对象 $o$ 被送到纤维 $p^{-1}(o)$）！
对一般的 $c$，就得到一族以 $c$ 为下标的这种结构。用 Lean 写出 $c = 1$ 的情形，并给出一个例子——从固定对象 $o$ 出发的所有箭头，靠“后复合”被推送（这就是可表函子 $\mathcal{C}(o, -)$）：

```lean
/-- Span 中单子（即范畴 C）的代数：一个“放在对象上方”的集合，箭头可以推送它的元素。 -/
structure SpanAlg (C : SmallCat) where
  X   : Type
  p   : X → C.Ob
  act : (x : X) → (a : C.Arr) → p x = C.dom a → X
  p_act    : ∀ x a h, p (act x a h) = C.cod a
  act_id   : ∀ x h, act x (C.idArr (p x)) h = x
  act_comp : ∀ x a₁ a₂ h₁ h₁₂ h h',
    act x (C.comp a₁ a₂ h₁₂) h = act (act x a₁ h₁) a₂ h'

/-- 可表的代数 C(o, -)：从 o 出发的箭头，被“后复合”推送。 -/
def SmallCat.repAlg (C : SmallCat) (o : C.Ob) : SpanAlg C where
  X := { a : C.Arr // C.dom a = o }
  p x := C.cod x.val
  act x a h := ⟨C.comp x.val a h, by rw [C.dom_comp]; exact x.property⟩
  p_act _ _ _ := C.cod_comp _ _ _
  act_id x h := Subtype.ext (C.comp_id x.val h)
  act_comp x a₁ a₂ h₁ h₁₂ _ _ := Subtype.ext (C.assoc x.val a₁ a₂ h₁ h₁₂ _ _).symm
```
:::

## 参考文献

1. [Paweł Sobociński 的博客](https://graphicallinearalgebra.net/2017/04/16/a-monoid-is-a-category-a-category-is-a-monad-a-monad-is-a-monoid/)：A monoid is a category, a category is a monad, a monad is a monoid。

## 本章小结

- **2-范畴**有三层：0-胞腔（对象）、1-胞腔（态射）、2-胞腔（态射之间的态射）。$\mathbf{Cat}$ 是标准例子：范畴、函子、自然变换。
- 在 2-范畴中，任意 hom-范畴 $\mathcal{C}(a, a)$ 都是幺半范畴：张量积 = 1-胞腔的复合，单位 = 恒等 1-胞腔。$\mathbf{Cat}(a, a)$ 就是自函子范畴，Lean 中它的定律都是 `rfl`（严格）。
- **双范畴**放宽了 2-范畴：单位律与结合律只在可逆 2-胞腔（单位子、结合子）意义下成立，外加相干性定律。
- **$\mathbf{Span}$** 是双范畴：0-胞腔是集合，1-胞腔是 span $a \leftarrow x \to b$，复合用**拉回**，2-胞腔是使三角形交换的顶点映射。在 Lean 中，`s ⊙ Span.id A` 与 `s` 的顶点是不同的类型，只能同构——这就是“非严格”。
- 推广的**单子**定义：双范畴中某个 0-胞腔上的自 1-胞腔 $T$，配上 2-胞腔 $\eta \colon I \Rightarrow T$、$\mu \colon T \circ T \Rightarrow T$，满足幺半群定律。在 $\mathbf{Cat}$ 中就是通常的单子。
- **$\mathbf{Span}$ 中的单子就是小范畴**：顶点 $\mathit{Arr}$ 是箭头，两条腿是 $\mathit{dom}$/$\mathit{cod}$，$\eta$ 给出恒等箭头，拉回 $T \circ T$ 是可复合的箭头对，$\mu$ 是复合；单子定律 = 范畴定律。我们在 Lean 中给出了双向翻译。
- 循环闭合：单子是幺半群，范畴是单子，幺半群是单对象范畴。范畴并不神秘——不过是“两个集合和四个函数”。

## 补充：全书回顾与接下来学什么（译者补充）

::: info 说明
本节是中文 Lean 版译者新增的内容，不属于原书。
:::

### 我们走过的路

回头看，这本书其实只讲了一件事：**复合**。

- **第一部分**从“范畴就是复合”出发：类型与函数构成范畴，Kleisli 范畴把带副作用的函数也变成可以复合的东西；积与余积用泛性质刻画，代数数据类型就是它们的组合；
  函子是保持复合的映射，自然变换是函子之间保持结构的映射。
- **第二部分**把泛构造推向一般：极限与余极限，自由幺半群，可表函子，以及全书的中心——米田引理：一个对象由它与其他对象的关系完全决定。
- **第三部分**用这些工具重建了函数式编程的核心概念：伴随（以及由它产生的单子与余单子）、F-代数（递归的本质）、端与余端、Kan 扩张、富集范畴、拓扑斯，
  以及最后的 Lawvere 理论与本章的“单子、幺半群与范畴”的循环。

贯穿始终的几个主题：**复合**、**泛性质**（“最好的那一个”）、**对偶**（把箭头反过来，免费得到另一半理论）、**米田**（用关系代替内部结构）、**伴随**（最普遍的“互逆”）、以及**幺半群**（复合的最小抽象）。
而 Lean 让我们多做了一件原书做不到的事：把“读者可以验证”变成了“编译器已经验证”。

### 从本书的 `CTFP.Category` 到 Mathlib

本书刻意只用 Lean 核心库，自己定义了一套小小的范畴论（`CTFP.Category`、`CFunctor`、`NatTrans`、`Op`），好让每一行都看得见。
真正做形式化数学时，你会用 [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) 的 `CategoryTheory` 库——它是目前规模最大的形式化范畴论库之一。
两者的概念一一对应，但有几处记号和约定**方向相反**，第一次读 Mathlib 时很容易被绊倒：

| 概念 | 本书（`CTFP`） | Mathlib（`CategoryTheory`） |
|---|---|---|
| 范畴 | `class Category (Obj : Type u)`，宇宙写作 `Category.{u, v}`（对象在前） | `class Category (obj : Type u)`，宇宙写作 `Category.{v, u}`（**态射的宇宙在前**） |
| 态射 | `a ⟶ b` | `X ⟶ Y`（相同） |
| 恒等 | `𝟙 a` | `𝟙 X`（相同） |
| 复合 | `g ⊚ f`：先 `f` 后 `g`（与数学的 $g \circ f$ 同序） | `f ≫ g`：先 `f` 后 `g`（**图示顺序**，从左往右读） |
| 结合律 | `h ⊚ (g ⊚ f) = (h ⊚ g) ⊚ f` | `(f ≫ g) ≫ h = f ≫ g ≫ h`（`Category.assoc`） |
| 函子 | `CFunctor C D`，`F.obj`、`F.map` | `C ⥤ D`，`F.obj`、`F.map`；`F.map_comp : F.map (f ≫ g) = F.map f ≫ F.map g` |
| 自然变换 | `F ⟹ G`，`α.app a`；自然性 `G.map f ⊚ α.app a = α.app b ⊚ F.map f` | `F ⟶ G`（就是函子范畴里的态射），`α.app X`；自然性 `F.map f ≫ α.app Y = α.app X ≫ G.map f` |
| 对偶范畴 | `Op C` | `Cᵒᵖ`，用 `op`/`unop` 在两边搬运 |
| 类型范畴 | `typeCategory`（`Type u` 上的实例） | `Type u` 上的实例（`CategoryTheory.types`） |

几点说明：

- **复合方向**是最大的差别。Mathlib 选图示顺序，是因为在长长的交换图证明里，`f ≫ g ≫ h` 和箭头在纸上的走向一致，`simp` 重写也更顺手。
  把本书的等式搬到 Mathlib 时，记住 `g ⊚ f` ↦ `f ≫ g`，所有复合链都要倒过来读。
- **宇宙参数的顺序**也相反：本书的 `Category.{u, v}` 先写对象的宇宙 `u`；Mathlib 的 `Category.{v, u}` 先写态射的宇宙 `v`。在 Mathlib 里经常看到 `[Category.{v} C]`，指定的就是 hom 的宇宙。
- 本书中用到的其他概念，在 Mathlib 里大多有对应：同构 `X ≅ Y`、范畴等价 `C ≌ D`、伴随 `F ⊣ G`、米田嵌入 `yoneda`、极限（`CategoryTheory.Limits` 下的 `HasLimit`、`IsLimit` 等）、
  范畴论意义下的单子 `CategoryTheory.Monad`（注意与编程用的 `Monad` 类型类区分）、幺半范畴 `MonoidalCategory`（`⊗`、`𝟙_ C`）、双范畴 `Bicategory`、富集范畴、Kan 扩张、Grothendieck 拓扑与层等。
  具体名字随版本演化，以 Mathlib 文档为准。

为了体会“方向相反”，可以在本书的定义上局部定义一个 Mathlib 风格的 `≫`，看看同一条结合律换个写法的样子：

```lean
section MathlibStyle
open Category

/-- Mathlib 风格的图示顺序复合：f ≫ g 表示“先 f 后 g”。 -/
local notation:80 f:81 " ≫ " g:80 => Category.comp g f

variable {C : Type u} [Category.{u, v} C] {a b c d : C}

example (f : a ⟶ b) (g : b ⟶ c) : f ≫ g = g ⊚ f := rfl

/-- 结合律的“Mathlib 写法”：括号挪动，箭头顺序与纸上的图一致。 -/
theorem assoc_diagrammatic (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  Category.assoc f g h

example (f : a ⟶ b) : 𝟙 a ≫ f = f := Category.comp_id f

end MathlibStyle
```

以下是 Mathlib 中同一组定律的样子（仅供对照，本书不依赖 Mathlib，所以不编译）：

```lean no-check
import Mathlib.CategoryTheory.Functor.Basic
open CategoryTheory

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y Z : C}

example (f : X ⟶ Y) (g : Y ⟶ Z) : F.map (f ≫ g) = F.map f ≫ F.map g := F.map_comp f g
example : F.map (𝟙 X) = 𝟙 (F.obj X) := F.map_id X
```

### 接下来学什么

一份建议的路线（按需挑选，不必全读）：

1. **把 Lean 练扎实。**
   - [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)：依值类型论与证明的系统讲解。
   - [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)：David Thrane Christiansen 写的 Lean 编程入门，对 Rust 程序员很友好。
   - [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)：学会在 Mathlib 里做数学。
   - 有问题就去 [Lean Zulip](https://leanprover.zulipchat.com/) 提问，社区非常活跃。
2. **读一本“正经的”范畴论教材，并用 Mathlib 形式化其中的习题。**
   - Emily Riehl，*Category Theory in Context*（作者主页提供免费 PDF）：例子丰富、论证干净，特别是米田引理、极限、伴随和 Kan 扩张几章；读完本书后正好接得上。
   - Tom Leinster，*Basic Category Theory*（arXiv 免费）：篇幅短小，非常适合打基础。
   - Saunders Mac Lane，*Categories for the Working Mathematician*：经典参考书，需要更多数学背景。
   - Brendan Fong 与 David Spivak，*Seven Sketches in Compositionality*（arXiv 免费）：应用范畴论，从数据库、电路到资源理论。
3. **继续跟着 Milewski 学。**
   - *The Dao of Functional Programming*（GitHub 上有免费 PDF）：Milewski 的新书，用更现代、更统一的视角重讲函数式编程背后的范畴论，可以看作本书的续篇。
   - 他在 YouTube 上的 *Category Theory* 系列讲座（共三部分），内容与本书大体对应，适合换个方式再过一遍。
   - 他的博客 *Bartosz Milewski's Programming Cafe*：本书最初就连载于此，还有许多后续文章（透镜、剖函子光学、Kan 扩张等）。
4. **顺着最后两章往深处走。**
   - 代数效应：Plotkin 与 Pretnar 的 *Handlers of Algebraic Effects*；Hyland 与 Power 的 *The Category Theoretic Understanding of Universal Algebra: Lawvere Theories and Monads*。
   - 双范畴与高维范畴：Niles Johnson 与 Donald Yau 的 *2-Dimensional Categories*（arXiv 免费）；Tom Leinster 的 *Higher Operads, Higher Categories*。
   - 类型论与范畴论的交汇：同伦类型论（*Homotopy Type Theory* 一书，免费）、范畴语义学。

最后，借原书的精神说一句：范畴论没有“学完”的时候。但你已经掌握了它的语言——复合、泛性质、函子、自然变换、伴随、米田——
今后读任何一篇用范畴论写成的文章、任何一个 Mathlib 文件，你都不再是门外汉。去复合点什么吧。
