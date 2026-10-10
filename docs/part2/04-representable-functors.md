# 2.4 可表函子

```lean hidden
universe u v w u₁ v₁ u₂ v₂

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

def Op (C : Type u) : Type u := C

instance opCategory (C : Type u) [Category.{u, v} C] : Category.{u, v} (Op C) where
  Hom a b := @Category.Hom C _ b a
  id a := @Category.id C _ a
  comp g f := @Category.comp C _ _ _ _ f g
  id_comp f := @Category.comp_id C _ _ _ f
  comp_id f := @Category.id_comp C _ _ _ f
  assoc f g h := (@Category.assoc C _ _ _ _ _ h g f).symm

end CTFP

open CTFP Category
```

是时候认真聊一聊集合了。数学家和集合论的关系可以说是又爱又恨：集合论曾经是数学的“汇编语言”——至少过去是这样。范畴论在某种程度上想离集合论远一点。比如，大家都知道“所有集合构成的集合”并不存在（否则会撞上罗素悖论），但“所有集合构成的范畴” $\mathbf{Set}$ 却是存在的。这很好。可另一方面，我们又默认任意两个对象之间的态射构成一个集合——我们甚至给它起名叫 **hom-集**（hom-set，即“态射集合”）。公平地说，范畴论里确实有一个分支，那里态射并不构成集合，而是另一个范畴里的对象。这种用“hom-对象”代替 hom-集的范畴叫做**富集范畴**（enriched category）。不过接下来我们还是老老实实地使用传统的 hom-集。

在范畴论的对象之外，集合差不多是你能找到的最“没有特征”的一团东西了。集合有元素，可是关于这些元素你几乎说不出什么。对有限集，你可以数一数有几个元素；对无限集，也可以借助**基数**（cardinal number）勉强“数一数”。例如，自然数集比实数集“小”，尽管两者都是无限的。但也许出人意料的是，有理数集和自然数集却一样大。

::: info 数学小课堂：无限集合怎么“比大小”
比较两个集合的大小，最朴素的办法不是“数数”，而是**配对**：如果能把两个集合的元素一一配成对，谁也不剩下，它们就一样大。这种一一配对叫做**双射**（bijection）。

- 自然数 $\{0, 1, 2, \dots\}$ 和偶数 $\{0, 2, 4, \dots\}$ 一样大：配对 $n \leftrightarrow 2n$。（是的，“部分”可以和“整体”一样大，这正是无限集的怪异之处。）
- 有理数和自然数一样大：把所有分数 $p/q$ 排进一张二维表，沿对角线 $1/1, 1/2, 2/1, 1/3, 2/2, 3/1, \dots$ 一条条扫过去，就能给每个分数编上一个自然数号码（重复的跳过即可）。
- 实数比自然数多：康托尔的“对角线论证”说明，不管你怎样给实数编号，总能构造出一个没被编到的实数。

记住这个直觉：**对集合来说，“一样”就是“能一一配对”**。本章和接下来两章会反复用到它。
:::

除了大小之外，关于集合的一切信息都可以编码在集合之间的函数里——尤其是那些可逆的函数，即**同构**（isomorphism）。从任何实际用途来看，同构的集合就是相同的。在招来数学基础学家的怒火之前，我得先解释一句：相等与同构之间的区别其实极为重要。事实上，它正是最新的数学分支之一——**同伦类型论**（Homotopy Type Theory，HoTT）——关心的核心问题之一。我之所以提到 HoTT，是因为它是一门从计算中汲取灵感的纯数学理论，而它的主要倡导者之一 Vladimir Voevodsky 正是在研究定理证明器 Rocq（以前叫 Coq）时获得了重大的顿悟。数学和编程之间的影响是双向的。

::: tip Lean 深入：Lean 里的“相等”与“同构”
你手上的 Lean 4 和 Rocq 是近亲，都基于依值类型论。在 Lean 里，`a = b` 是一个命题（`Prop`），而“两个类型同构”则需要你**给出**一对互逆的函数——它是数据，不是命题。Lean 的标准设定与 HoTT 并不兼容（Lean 有“证明无关性”，HoTT 要求等式本身可以携带信息），但这种“相等 vs. 同构”的张力你在 Lean 里天天都能感受到：`Nat × Bool` 和 `Bool × Nat` 显然“一样”，可它们并不是同一个类型，你必须写函数在两者之间来回转换。
:::

关于集合，最重要的一课是：拿元素种类完全不同的集合来比较，是完全可以的。比如我们可以说，某个由自然变换构成的集合与某个由态射构成的集合同构——因为集合就只是集合。这里的同构只意味着：一边的每个自然变换都恰好对应另一边的一个态射，反之亦然，它们可以两两配对。如果苹果和橘子是不同范畴里的对象，你没法直接比较苹果和橘子；但你可以比较“一筐苹果”和“一筐橘子”。把一个范畴论问题转化为集合论问题，常常能带来关键的洞见，甚至让我们证明出有价值的定理。

## hom 函子

每个范畴都自带一族通往 $\mathbf{Set}$ 的标准映射。这些映射其实都是函子，因此它们保持范畴的结构。我们来构造其中一个。

在 $\mathcal{C}$ 中固定一个对象 $a$，再任取 $\mathcal{C}$ 中的另一个对象 $x$。hom-集 $\mathcal{C}(a, x)$ 是一个集合，也就是 $\mathbf{Set}$ 中的一个对象。当 $a$ 保持不动而 $x$ 变化时，$\mathcal{C}(a, x)$ 也在 $\mathbf{Set}$ 中跟着变化。于是我们得到了一个从 $x$ 到 $\mathbf{Set}$ 的映射。

![hom-集作为 x 的函数](/img/2.4/hom-set.jpg "固定 a，让 x 变化：每个 x 都被映到一个集合——从 a 到 x 的全部箭头。")

如果想强调我们把 hom-集看作关于**第二个参数**的映射，就写成 $\mathcal{C}(a, -)$，其中短横线是参数的占位符。

::: info 数学小课堂：占位符记号 $-$
$\mathcal{C}(a, -)$ 这种写法和编程里的“部分应用”一模一样：$\mathcal{C}(-, -)$ 是个两参数的东西，把第一个参数固定成 $a$，剩下的空位用 $-$ 表示“等着你填”。用 Lean 的话说，它就像 `fun x => (a ⟶ x)`；用 Rust 的话说，像一个闭包 `|x| hom(a, x)`。
:::

这个对象映射很容易扩展成态射映射。在 $\mathcal{C}$ 中任取两个对象 $x$、$y$ 之间的态射 $f$。在刚定义的映射下，$x$ 被映到集合 $\mathcal{C}(a, x)$，$y$ 被映到 $\mathcal{C}(a, y)$。如果这个映射想成为函子，$f$ 就必须被映成两个集合之间的函数：

$$\mathcal{C}(a, x) \to \mathcal{C}(a, y)$$

我们逐点定义这个函数，也就是对每个参数分别说明它被送到哪里。参数应当是 $\mathcal{C}(a, x)$ 中的任意一个元素——叫它 $h$ 吧。态射只要首尾相接就能复合。恰好 $h$ 的终点就是 $f$ 的起点，所以它们的复合

$$f \circ h : a \to y$$

是一个从 $a$ 到 $y$ 的态射，因而是 $\mathcal{C}(a, y)$ 的成员。

![hom 函子作用在态射上](/img/2.4/hom-functor.jpg "f 被映成函数 C(a, f)：它把每个 h : a → x 送到 f ∘ h : a → y。")

```diagram
a: (0, 0.9)
x: (2, 0.9)
y: (4, 0.9)
h: a -> x "h" side=right
f: x -> y "f" side=right
fh: a -> y "f \circ h" bend=50 color=brand
path "先 h 再 f": h f
path "直接走 f∘h": fh color=green
caption: hom 函子的“后接”：C(a, f) 把 h 变成 f ∘ h
```

我们刚刚找到了一个从 $\mathcal{C}(a, x)$ 到 $\mathcal{C}(a, y)$ 的函数，它可以充当 $f$ 的像。在不会混淆的情况下，我们把这个被“提升”的函数记作 $\mathcal{C}(a, f)$，它在态射 $h$ 上的作用是：

$$\mathcal{C}(a, f)\, h = f \circ h$$

### 用 Lean 写出 hom 函子

我们在 [1.7 函子](/part1/07-functors) 里定义过范畴之间的函子 `CFunctor`，在 [1.10 自然变换](/part1/10-natural-transformations) 里定义过 `NatTrans`。本章开头的隐藏代码块已经把这些定义（与全书 `Prelude.lean` 完全相同）引了进来。现在可以把 hom 函子写成一个真正的 Lean 值，并且**证明**它满足函子定律：

```lean
/-- hom 函子 `C(a, -)`：对象 `x` ↦ 集合 `a ⟶ x`；态射 `f` ↦ “后接 f”。 -/
def homFunctor {C : Type u} [Category.{u, v} C] (a : C) : CFunctor C (Type v) where
  obj x := a ⟶ x
  map f := fun h => f ⊚ h
  -- 恒等律：C(a, id_x) h = id_x ∘ h = h
  map_id x := by
    funext h
    exact id_comp h
  -- 复合律：C(a, g ∘ f) h = (g ∘ f) ∘ h = g ∘ (f ∘ h)
  map_comp f g := by
    funext h
    exact (assoc h f g).symm
```

逐行看一下：

- `CFunctor C (Type v)`：这是一个从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的函子。在本书里，$\mathbf{Set}$ 由 Lean 的类型范畴 `Type v` 扮演。为什么是 `Type v` 而不是 `Type`？因为 `Category.{u, v} C` 规定 $\mathcal{C}$ 的 hom-集住在宇宙 `Type v` 里（`a ⟶ x : Type v`），所以 hom 函子的值域自然是 `Type v`。对于我们最常用的情形 $\mathcal{C} = $ `Type`，有 `v = 0`，值域就是 `Type`。
- `obj x := a ⟶ x`：对象 $x$ 被映到 hom-集——它本身是一个类型。
- `map f := fun h => f ⊚ h`：态射 $f$ 被映到“后接 $f$”这个函数。
- 两条函子定律分别由范畴的单位律 `id_comp` 和结合律 `assoc` 推出。`funext h` 的意思是：要证明两个函数相等，只需证明它们对任意参数 `h` 给出相同的结果（**函数外延性**）。

这一构造在任何范畴里都成立，所以它当然也适用于“类型与函数”的范畴。在那里，hom 函子有个更常见的名字：**`Reader` 函子**。

```lean
def Reader (a x : Type) := a → x

instance : Functor (Reader a) where
  map f h := f ∘ h
```

`Reader a` 的 `map` 正是函数的“后接”：`map f h = f ∘ h`。我们还可以顺手证明它是个**守法的**函子——Lean 的 `LawfulFunctor` 类型类要求你把函子定律证出来，这里三条全都是 `rfl`（按定义展开就相等）：

```lean
instance : LawfulFunctor (Reader a) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

-- Reader Nat 里装着“一个读取 Nat 的计算”；map 在它后面再接一个函数
example : (Functor.map (f := Reader Nat) toString (fun n : Nat => n * 2)) 21 = "42" := rfl
```

::: tip Lean 深入：标准库里的 Reader
Lean 标准库也有 Reader，只不过是单子变换器的形式：`ReaderT ρ m α` 本质上就是 `ρ → m α`，而 `ReaderM ρ := ReaderT ρ Id`。去掉那层 `Id` 之后，它就是我们这里的 `Reader ρ`。我们自己定义一个光秃秃的版本，是为了让“hom 函子 = 函数类型 = Reader”这件事一目了然。
:::

::: tip Rust 视角
在 Rust 里，`Reader<A, X>` 就是“一个闭包 `impl Fn(A) -> X`”，而它的 `map` 就是在闭包后面再接一个闭包：

```rust
fn reader_map<A, X, Y>(f: impl Fn(X) -> Y, h: impl Fn(A) -> X) -> impl Fn(A) -> Y {
    move |a| f(h(a))
}

pub fn demo() -> String {
    let h = |n: i32| n * 2;
    let g = reader_map(|x: i32| x.to_string(), h);
    g(21) // "42"
}
```

“固定输入类型 `A`，让输出类型 `X` 变化”——这正是 $\mathcal{C}(a, -)$。
:::

### 逆变的 hom 函子与剖函子

现在换个问法：如果我们固定 hom-集的**终点**而不是起点，会怎样？也就是说，映射 $\mathcal{C}(-, a)$ 是不是函子？它是，只不过不是协变的，而是**逆变**的。原因是：同样的“首尾相接”要求，这一次导致我们对 $f$ 做的是**前接**（先 $f$ 再 $h$），而不是 $\mathcal{C}(a, -)$ 那样的后接。

我们在 Lean 里也见过这个逆变函子（[1.8 函子性](/part1/08-functoriality) 中称为 `Op`）。为了避免和全书前导里表示对偶范畴的 `CTFP.Op` 撞名，这里叫它 `Op'`。Lean 核心库没有 `Contravariant` 类型类，我们自己定义一个：

```lean
def Op' (a x : Type) := x → a

class Contravariant (f : Type → Type) where
  contramap : {α β : Type} → (β → α) → f α → f β

instance : Contravariant (Op' a) where
  contramap f h := h ∘ f    -- 前接：先 f，再 h
```

在一般范畴里，逆变就等价于“从对偶范畴出发的协变函子”，所以 $\mathcal{C}(-, a)$ 可以写成一个 `CFunctor (Op C) (Type v)`。（这里需要把实例参数写明，告诉 Lean 我们是在原范畴 $\mathcal{C}$ 里做复合。）

```lean
/-- 逆变 hom 函子 `C(-, a)`，看作 `Cᵒᵖ ⥤ Set`。 -/
def coHomFunctor {C : Type u} [inst : Category.{u, v} C] (a : C) : CFunctor (Op C) (Type v) where
  obj x := @Category.Hom C inst x a
  map f := fun h => @Category.comp C inst _ _ _ h f   -- h ∘ f：前接
  map_id x := by funext h; exact @comp_id C inst _ _ h
  map_comp f g := by funext h; exact @assoc C inst _ _ _ _ g f h
```

最后，如果让两个对象都变化，就得到一个**剖函子**（profunctor）$\mathcal{C}(-, =)$：它对第一个参数逆变，对第二个参数协变。（为了强调两个参数可以独立变化，我们用双横线 $=$ 作为第二个占位符。）我们在讨论函子性时见过它。Lean 核心库同样没有 `Profunctor`，那就再定义一个：

```lean
class Profunctor (p : Type → Type → Type) where
  dimap : {a b c d : Type} → (a → b) → (c → d) → p b c → p a d
  lmap : {a b c : Type} → (a → b) → p b c → p a c := fun f => dimap f id
  rmap : {a b c : Type} → (b → c) → p a b → p a c := fun g => dimap id g

/-- 函数箭头 `(· → ·)` 是剖函子：左边前接，右边后接。 -/
instance : Profunctor (· → ·) where
  dimap ab cd bc := cd ∘ bc ∘ ab
  lmap ab bc := bc ∘ ab
  rmap bc ab := bc ∘ ab

-- 先 +1，再 *2，最后转成字符串
example : Profunctor.dimap (p := (· → ·)) (fun n : Nat => n + 1) toString (fun n : Nat => n * 2) 3
    = "8" := rfl
```

重要的结论是：这个现象在**任何**范畴里都成立——把一对对象映到它们之间的 hom-集，这个映射是函子性的。既然逆变等价于从对偶范畴出发的映射，我们可以把这件事简洁地写成：

$$\mathcal{C}(-, =) : \mathcal{C}^{op} \times \mathcal{C} \to \mathbf{Set}$$

## 可表函子

我们已经看到，对 $\mathcal{C}$ 中的每个对象 $a$，都能得到一个从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的函子。这种通往 $\mathbf{Set}$ 的保结构映射，常常被称为一个**表示**（representation）：我们把 $\mathcal{C}$ 的对象和态射“表示”成了 $\mathbf{Set}$ 中的集合和函数。

函子 $\mathcal{C}(a, -)$ 本身有时就被称作“可表的”。更一般地，只要一个函子 $F$ 对**某个** $a$ 与 hom 函子自然同构，它就称为**可表函子**（representable functor）。这样的函子必然是取值于 $\mathbf{Set}$ 的，因为 $\mathcal{C}(a, -)$ 是。

前面说过，我们常把同构的集合看作相同的。更一般地，我们把范畴里同构的**对象**也看作相同的。这是因为对象除了通过态射与其他对象（以及自己）发生关系之外，没有任何别的结构。

举个例子：我们以前讨论过幺半群范畴 $\mathbf{Mon}$，它最初是用集合来建模的。但我们很小心，只挑选那些保持幺半群结构的函数作为态射。所以，如果 $\mathbf{Mon}$ 中两个对象同构——也就是说它们之间有一个可逆态射——那它们的结构就完全一样。要是偷看一下它们背后的集合和函数，就会发现：一个幺半群的单位元被映到另一个幺半群的单位元，两个元素的乘积被映到它们像的乘积。

同样的推理也适用于函子。两个范畴之间的函子构成一个范畴，其中自然变换扮演态射的角色。所以，如果两个函子之间存在一个可逆的自然变换，它们就是同构的，并且可以看作相同的。

::: info 数学小课堂：自然同构
回忆一下：**自然变换** $\alpha : F \Rightarrow G$ 是一族态射 $\alpha_x : F x \to G x$（每个对象 $x$ 一个“分量”），并且满足自然性方块。**自然同构**就是“可逆的自然变换”：存在反方向的自然变换 $\beta : G \Rightarrow F$，使得每个分量都互逆：

$$\beta_x \circ \alpha_x = \mathrm{id}_{F x}, \qquad \alpha_x \circ \beta_x = \mathrm{id}_{G x}$$

在 $\mathbf{Set}$ 里，“分量互逆”就是“每个 $F x$ 和 $G x$ 之间都有一个一一配对，而且这些配对彼此协调（自然）”。
:::

让我们从这个角度分析可表函子的定义。$F$ 可表，要求的是：

1. $\mathcal{C}$ 中存在一个对象 $a$；
2. 有一个从 $\mathcal{C}(a, -)$ 到 $F$ 的自然变换 $\alpha$；
3. 有另一个反方向的自然变换 $\beta$；
4. 它们的复合是恒等自然变换。

看看 $\alpha$ 在某个对象 $x$ 上的分量。它是 $\mathbf{Set}$ 中的一个函数：

$$\alpha_x : \mathcal{C}(a, x) \to F x$$

这个变换的自然性条件告诉我们：对任意从 $x$ 到 $y$ 的态射 $f$，下面的图交换：

$$F f \circ \alpha_x = \alpha_y \circ \mathcal{C}(a, f)$$

```diagram
Cax: (0, 0) "\mathcal{C}(a, x)\hspace{1.6em}"
Fx: (3, 0) "F x"
Cay: (0, 1.8) "\mathcal{C}(a, y)\hspace{1.6em}"
Fy: (3, 1.8) "F y"
ax: Cax -> Fx "\alpha_x"
ay: Cay -> Fy "\alpha_y" side=right
Caf: Cax -> Cay "\mathcal{C}(a, f)" side=right
Ff: Fx -> Fy "F f"
path "先 α_x 再 F f": ax Ff
path "先 C(a, f) 再 α_y": Caf ay color=green
caption: 自然性方块：两条路径给出同一个函数
```

在 Lean 的类型范畴里，自然变换就是**多态函数**：

```lean no-check
-- 对固定的 a 和函子 F：
alpha : {x : Type} → (a → x) → F x
```

花括号 `{x : Type}` 表示 `x` 是**隐式参数**：调用时 Lean 会根据上下文自己推断出 `x`。这相当于 Haskell 中可写可不写的 `forall x.`，也相当于 Rust 中的泛型参数 `fn alpha<X>(h: impl Fn(A) -> X) -> F<X>`。

它的自然性条件是

```lean no-check
-- 对任意 f : x → y
Functor.map f ∘ alpha = alpha ∘ Functor.map f
```

请注意，左边的 `map` 是函子 `F` 的 `map`，而右边的 `map` 是 Reader 函子的 `map`。既然 Reader 的 `map` 就是函数的后接，我们可以把它写得更直白：作用在 $\mathcal{C}(a, x)$ 的某个元素 `h` 上时，自然性条件化简为

```lean no-check
f <$> alpha h = alpha (f ∘ h)
```

（`f <$> v` 是 `Functor.map f v` 的中缀写法，相当于 Rust 里的 `v.map(f)`。）

在 Haskell 里，这个条件由**参数性**（parametricity）自动保证——它就是我之前提到过的“免费定理”之一。

::: warning 易错点：Lean 里的“免费定理”不是免费的
在 Haskell（以及不用 `unsafe` 的 Rust）里，一个对所有 `x` 一视同仁的多态函数无法偷看 `x` 是什么类型，因此自动满足自然性。Lean 的可计算部分同样无法对类型做模式匹配，所以你写出来的普通多态函数在“元理论”层面也是自然的。

但是，**Lean 无法在自身内部证明这一点**——“对所有多态函数，自然性成立”不是 Lean 里的一个定理。更糟的是，借助经典逻辑（`Classical.choice`），你甚至能写出一个 `noncomputable` 的、会偷看类型的“多态函数”，它根本不自然（下一章会给出一个具体例子）。

所以在 Lean 里，**每当我们需要自然性，就把它作为一个显式的条件写出来并证明**。这是 Lean 比 Haskell 更诚实的地方：原书说“自动满足”的东西，我们要么证明它，要么把它写进假设。
:::

另一个变换 `beta` 方向相反：

```lean no-check
beta : {x : Type} → F x → (a → x)
```

它也必须满足自然性条件，并且必须是 `alpha` 的逆：

```lean no-check
alpha ∘ beta = id      beta ∘ alpha = id
```

稍后我们会看到，只要 $F a$ 非空，从 $\mathcal{C}(a, -)$ 到任意 $\mathbf{Set}$ 值函子的自然变换就一定存在（这就是**米田引理**），但它不一定可逆。

### 一个反例：List 不可表

我用列表函子、取 `a` 为 `Nat`，来举个例子。下面这个自然变换就能完成任务：

```lean
def alpha12 {x : Type} (h : Nat → x) : List x := List.map h [12]
```

我随手挑了数字 12，做了一个只含它的单元素列表，然后把函数 `h` `map` 到这个列表上，得到一个元素类型为 `h` 返回类型的列表。（实际上，这样的变换有多少个，就有多少个整数列表：把 `[12]` 换成任意 `List Nat` 都行。）

自然性条件等价于 `List.map` 的“可复合性”——先 `map h` 再 `map f`，等于一次 `map (f ∘ h)`。这在 Lean 里可以直接证明：

```lean
theorem alpha12_natural {x y : Type} (f : x → y) (h : Nat → x) :
    List.map f (alpha12 h) = alpha12 (f ∘ h) := by
  simp [alpha12]   -- simp 展开定义，并用标准库的 List.map_map 化简
```

`simp` 是 Lean 最常用的自动化 tactic：它会用一大批标记为 `@[simp]` 的等式（比如 `List.map_map : map g (map f l) = map (g ∘ f) l`）反复改写目标，直到化简成平凡的东西。

但是，如果我们想找逆变换，就得从任意类型 `x` 的列表出发，得到一个返回 `x` 的函数：

```lean no-check
beta : {x : Type} → List x → (Nat → x)
```

你也许会想到从列表里取一个 `x` 出来，比如用 `head`——可惜这对空列表行不通。（在 Lean 里，`List.head` 甚至要求你提供一个“列表非空”的证明才能调用，类型系统直接把这条路堵死了。）还要注意，把 `Nat` 换成任何别的类型 `a` 都无济于事。所以，列表函子不是可表的。

“换成任何类型都无济于事”这句话，在 Lean 里可以被**证明**。思路非常漂亮：

- 看 `x := Unit`（只有一个值 `()` 的类型）。不管 `R` 是什么，从 `R` 到 `Unit` 的函数**只有一个**（每个输入都只能送到 `()`）。
- 可是 `List Unit` 有很多不同的值：`[]`、`[()]`、`[(), ()]`……
- 如果 `tabulate ∘ index = id`，那么 `index` 必须是单射；但它要把无穷多个列表塞进只有一个元素的 `R → Unit`，必然有两个不同的列表被送到同一个函数。矛盾。

```lean
theorem list_not_representable :
    ¬ ∃ (R : Type) (tab : {x : Type} → (R → x) → List x) (idx : {x : Type} → List x → R → x),
      ∀ {x : Type} (l : List x), tab (idx l) = l := by
  intro ⟨R, tab, idx, h⟩
  -- R → Unit 只有一个元素：idx [()] 和 idx [] 必然是同一个函数
  have e : idx [()] = idx ([] : List Unit) := by
    funext r
    rfl          -- 两边都是 Unit 的值，而 Unit 只有一个值
  -- 于是 [()] = tab (idx [()]) = tab (idx []) = []
  have : [()] = ([] : List Unit) := calc
    [()] = tab (idx [()]) := (h _).symm
    _ = tab (idx []) := by rw [e]
    _ = [] := h _
  exact List.cons_ne_nil _ _ this
```

注意我们甚至没有用到自然性——仅凭“`tab` 是 `idx` 的左逆”就足以推出矛盾。这里出现了几个新 tactic：`intro ⟨...⟩` 把存在量词的证据拆开；`calc` 写出一条等式链，每一步都附上理由；`rw [e]` 用等式 `e` 改写目标。

### 表示即“备忘录”

还记得我们说过，Lean（以及 Haskell）中的自函子有点像容器吗？同样地，我们可以把可表函子看成**存放函数调用的备忘结果的容器**（在类型范畴里，hom-集的成员就是函数）。表示对象——$\mathcal{C}(a, -)$ 里的那个类型 $a$——可以看作**键的类型**，我们用它来访问一个函数被“制成表”的那些值。我们称为 `alpha` 的变换叫做 `tabulate`（制表），它的逆 `beta` 叫做 `index`（查表）。下面是一个（稍作简化的）`Representable` 类定义：

```lean
class Representable (f : Type → Type) where
  /-- 表示对象：键的类型 -/
  Rep : Type
  /-- 把函数制成表（α） -/
  tabulate : {x : Type} → (Rep → x) → f x
  /-- 按键查表（β） -/
  index : {x : Type} → f x → Rep → x
```

注意，表示类型——也就是我们的 $a$，在这里叫做 `Rep f`——是 `Representable` 定义的一部分。字段声明 `Rep : Type` 说的是：`Rep f` 是一个**类型**（而不是 `Type → Type` 那样的类型构造器，或者别的更奇特的东西）。Haskell 原文写作 `type Rep f :: *`，其中星号 `*` 就是 Haskell 对 `Type` 的老式记法。在 Haskell 里，这需要一个叫“关联类型族”的扩展；而在 Lean 里，它只是一个类型为 `Type` 的普通字段，因为 Lean 是依值类型语言，**类型本身就是值**，可以像别的数据一样放进结构体。

::: tip Rust 视角：关联类型
`Rep` 就是 Rust trait 中的**关联类型**：

```rust
trait Representable {
    type Rep;
    type F<X>;
    fn tabulate<X>(h: impl Fn(Self::Rep) -> X) -> Self::F<X>;
    fn index<X>(fx: &Self::F<X>, key: Self::Rep) -> X where X: Clone;
}
```

（为了让 `F<X>` 成为“类型构造器”，这里用到了 Rust 的泛型关联类型 GAT。Lean 不需要这种绕弯子的写法：`f : Type → Type` 直接就是一个类型构造器。）
:::

上面的类只给出了两个函数，并没有要求它们互逆。在 Lean 里我们可以把这个要求也写进去，做成一个“守法版本”，就像 `LawfulFunctor` 之于 `Functor`：

```lean
class LawfulRepresentable (f : Type → Type) [Representable f] : Prop where
  index_tabulate : ∀ {x : Type} (h : Representable.Rep f → x),
    Representable.index (Representable.tabulate h) = h
  tabulate_index : ∀ {x : Type} (fx : f x),
    Representable.tabulate (Representable.index fx) = fx
```

（严格说来，完整的定义还应要求 `tabulate`、`index` 是自然的；对下面的例子它们都显然成立，为了不让定义过于臃肿，我们略去这一条。）

### 例子：Stream 由 Nat 表示

无限列表，也叫**流**（stream），永远不可能为空，它们是可表的。在 Haskell 里，流的定义是

```lean no-check
-- Haskell 的写法，直译成 Lean：
inductive BadStream (α : Type) where
  | cons : α → BadStream α → BadStream α
```

**但这在 Lean 里行不通**——准确地说，Lean 会接受这个定义，可它定义出来的是一个**空类型**！`inductive` 定义的是“用有限步构造器搭起来的值”。这里只有一个构造器 `cons`，而它需要一个现成的 `BadStream` 作为参数——你永远无法迈出第一步。我们甚至可以证明这一点：

```lean
inductive BadStream (α : Type) where
  | cons : α → BadStream α → BadStream α

/-- 归纳地看，BadStream 里根本没有值。 -/
theorem BadStream.empty {α : Type} (s : BadStream α) : False := by
  induction s with
  | cons _ _ ih => exact ih
```

Haskell 之所以能用这个定义，是因为它是**惰性的**：值按需求值，“无限的数据”只要你不全部展开就没问题。Lean 是**严格求值**的语言，类型也只包含“有限的”数据。（Lean 核心库目前没有余归纳类型 coinductive type，那才是“无限数据”的正确家园。）

那 Lean 里怎么表示一个流呢？答案恰恰是本章的主题：**流由 `Nat` 表示**。一个流就是“第 0 个元素、第 1 个元素、第 2 个元素……”，也就是一个函数 `Nat → α`。我们干脆就这样定义它，再配上 `head`、`tail`、`cons` 这些熟悉的接口：

```lean
namespace Rep

/-- 流：用“下标 ↦ 元素”的函数来表示。 -/
structure Stream (α : Type) where
  get : Nat → α

def Stream.head (s : Stream α) : α := s.get 0
def Stream.tail (s : Stream α) : Stream α := ⟨fun n => s.get (n + 1)⟩
def Stream.cons (x : α) (s : Stream α) : Stream α :=
  ⟨fun n => match n with
    | 0 => x
    | n + 1 => s.get n⟩

end Rep
```

（Lean 核心库里已经有一个叫 `Stream` 的类型类，含义不同，所以我们把自己的 `Stream` 放进命名空间 `Rep`。）

你可以把流看作“一个以自然数为参数的函数”的备忘值。（原书用的是 Haskell 的 `Integer`，作者特意注明“严格说应该用非负整数，只是不想让代码变复杂”；在 Lean 里用 `Nat` 反而更简单。）

在 Haskell 版本里，要对这样的函数**制表**，就要创建一个无限的值的流——当然，这只有在惰性语言里才可能：值按需求值。而在我们的 Lean 版本里，`tabulate` 简单到近乎作弊：函数本身就是表！为了让 `index` 保持原书“沿着流一步步往前走”的风味，我们用 `head`/`tail` 递归地定义它：

```lean
namespace Rep

def Stream.tabulate (f : Nat → α) : Stream α := ⟨f⟩

/-- 查表：第 0 个就是 head，第 n+1 个就是 tail 的第 n 个。 -/
def Stream.index : Stream α → Nat → α
  | s, 0 => s.head
  | s, n + 1 => Stream.index s.tail n

instance : Representable Stream where
  Rep := Nat
  tabulate := Stream.tabulate
  index := Stream.index

end Rep
```

有意思的是，你可以实现**一种**备忘方案，覆盖**一整族**返回类型任意的函数——`tabulate` 对所有 `x` 都适用。

::: tip Lean 深入：Lean 里的“备忘”
坦白说：我们的 `Stream` 只是把函数包了一层，读取第 1000 个元素时仍要现场调用一次函数，**并没有缓存**。Haskell 的惰性流会把算过的值留在内存里，这才有真正的备忘效果。

在严格的 Lean 中，真正的备忘要靠一个实打实的数据结构，比如定长数组。`Vector α n`（长度恰为 `n` 的数组）就是由 `Fin n`（小于 `n` 的自然数）表示的可表函子：`tabulate` 把函数的 `n` 个值一次性算好存进数组，`index` 是 O(1) 的数组下标访问。

```lean
instance : Representable (Vector · 3) where
  Rep := Fin 3
  tabulate h := Vector.ofFn h
  index v i := v[i]

instance : LawfulRepresentable (Vector · 3) where
  index_tabulate h := by funext i; simp [Representable.index, Representable.tabulate]
  tabulate_index v := by ext i hi; simp [Representable.index, Representable.tabulate]
```

`Vector · 3` 里的 `·` 是“匿名参数”的简写，等价于 `fun α => Vector α 3`。在 Rust 里，这正对应 `std::array::from_fn`：

```rust
fn tabulate<const N: usize, T>(f: impl Fn(usize) -> T) -> [T; N] {
    std::array::from_fn(f) // 一次性把 f(0..N) 全部算好
}

fn index<const N: usize, T: Copy>(table: &[T; N], i: usize) -> T {
    table[i] // 之后每次查表都是 O(1)，不再调用 f
}

pub fn demo() -> u64 {
    let squares: [u64; 10] = tabulate(|n| (n * n) as u64);
    index(&squares, 7) // 49
}
```
:::

下面的组件让你亲手体会“同一份内容的两种实现”：左边是函数（每次查询都要调用一次），右边是备忘表（每个格子只在第一次被访问时计算一次）。

<div class="ctfp-ch-widget"><Ch2_4Tabulate /></div>

### 逆变函子的可表性

逆变函子的可表性定义与此类似，只不过我们固定的是 $\mathcal{C}(-, a)$ 的第二个参数。或者等价地，我们可以考虑从 $\mathcal{C}^{op}$ 到 $\mathbf{Set}$ 的函子，因为 $\mathcal{C}^{op}(a, -)$ 与 $\mathcal{C}(-, a)$ 是同一个东西。上面的 `coHomFunctor` 正是这样定义的：它的类型是 `CFunctor (Op C) (Type v)`。

### 可表性的一个有趣转折：对数

可表性还有一个有趣的转折。还记得吗，在笛卡尔闭范畴里，hom-集可以在内部被看作指数对象。hom-集 $\mathcal{C}(a, x)$ 等价于 $x^a$，于是对一个可表函子 $F$，我们可以写

$$(-)^a = F$$

纯粹为了好玩，对两边取个对数：

$$a = \log F$$

当然，这只是一个纯形式上的变换。但如果你熟悉对数的性质，它会相当有帮助。特别地，基于**积类型**的函子可以用**和类型**来表示，而基于和类型的函子一般不可表（例如列表函子）。

::: info 数学小课堂：为什么“取对数”说得通
把类型看成它的元素个数（[1.6 简单代数数据类型](/part1/06-simple-algebraic-data-types) 讲过这种“类型代数”）：`Bool` 是 2，`Unit` 是 1，`α × β` 是乘法，`α ⊕ β` 是加法，函数类型 `a → x` 是 $x^a$。

- `Pair x := x × x` 有 $x^2$ 个值。$\log_x(x^2) = 2$，所以表示对象有 2 个元素——就是 `Bool`。
- `x × x × x` 是 $x^3$，表示对象是三元素类型 `Fin 3`。
- 流满足 $\mathrm{Stream}\,x \cong x \times \mathrm{Stream}\,x$，取对数：$\log \mathrm{Stream} = 1 + \log \mathrm{Stream}$。满足 $R \cong 1 + R$ 的最小类型就是自然数 `Nat`（`Nat` 要么是 `0`，要么是某个 `Nat` 的后继）。
- `Option x = 1 + x`，`List x = 1 + x + x^2 + \cdots`：都有“加上一个常数 1”这一项。可 $x^R$ 在 $x = 1$ 时总等于 $1$，而 `Option Unit`、`List Unit` 都不止一个值——所以它们不可能写成 $x^R$ 的形式。这正是我们上面 Lean 证明的思路！

对数把乘法变成加法：积类型（$x \cdot x \cdot x$）的“对数”是和类型（$1 + 1 + 1$）。
:::

### 两种实现，同一份内容

最后请注意，一个可表函子给了我们同一个东西的两种不同实现——一种是函数，一种是数据结构。它们的内容完全相同：用相同的键取出相同的值。这就是我一直在说的那种“相同”。就内容而言，两个自然同构的函子是一模一样的。另一方面，这两种表示的实现方式往往不同，性能特征也可能不同。备忘是一种性能优化手段，可能大幅缩短运行时间。能为同一个底层计算生成不同的表示，在实践中非常有价值。所以，虽然范畴论完全不关心性能，它却意外地为我们提供了大量探索具有实用价值的替代实现的机会。

## 补充：用 `CFunctor` 写出“可表”的完整定义

上面的 `Representable` 类是程序员的简化版。范畴论里的原始定义是“与某个 hom 函子**自然同构**”。有了 `homFunctor` 和 `NatTrans`，我们可以把它一字不差地写成 Lean：

```lean
/-- 自然同构：一对互逆的自然变换。 -/
structure NatIso {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    (F G : CFunctor C D) where
  hom : F ⟹ G
  inv : G ⟹ F
  hom_inv : ∀ a, inv.app a ⊚ hom.app a = 𝟙 (F.obj a)
  inv_hom : ∀ a, hom.app a ⊚ inv.app a = 𝟙 (G.obj a)

/-- F 的一个表示：一个对象 `rep`，以及 C(rep, -) ≅ F。 -/
structure Representation {C : Type u} [Category.{u, v} C] (F : CFunctor C (Type v)) where
  rep : C
  iso : NatIso (homFunctor rep) F
```

现在，流函子的可表性就是一个具体的值：表示对象是 `Nat`，`α` 是 `tabulate`，`β` 是 `get`，所有的自然性和互逆性都按定义成立（`rfl`）：

```lean
def streamFunctor : CFunctor Type Type where
  obj := Rep.Stream
  map f s := ⟨fun n => f (s.get n)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def streamRep : Representation streamFunctor where
  rep := Nat
  iso := {
    hom := { app := fun _ h => Rep.Stream.tabulate h, naturality := fun _ => rfl }
    inv := { app := fun _ s => s.get, naturality := fun _ => rfl }
    hom_inv := fun _ => rfl
    inv_hom := fun _ => rfl }
```

这就是“流由 `Nat` 表示”的字面意思：`streamFunctor` 与 `homFunctor Nat`（也就是 `Nat → -`）自然同构。

## 挑战

1. 证明 hom 函子把 $\mathcal{C}$ 中的恒等态射映到 $\mathbf{Set}$ 中相应的恒等函数。
2. 证明 `Option`（Haskell 的 `Maybe`）不可表。
3. `Reader` 函子可表吗？
4. 用 `Stream` 表示，对一个求平方的函数做备忘。
5. 证明 `Stream` 的 `tabulate` 和 `index` 确实互为逆。（提示：用归纳法。）
6. 函子

   ```lean no-check
   structure Pair (α : Type) where
     fst : α
     snd : α
   ```

   是可表的。你能猜出表示它的类型吗？实现 `tabulate` 和 `index`。

::: details 参考答案

**1.** 这正是 `homFunctor` 的 `map_id` 字段。逐点地看：$\mathcal{C}(a, \mathrm{id}_x)$ 作用在 $h : a \to x$ 上得到 $\mathrm{id}_x \circ h$，由单位律它等于 $h$；所以 $\mathcal{C}(a, \mathrm{id}_x)$ 把每个 $h$ 送回它自己，即恒等函数。用 Lean 单独陈述一遍：

```lean
theorem homFunctor_map_id {C : Type u} [Category.{u, v} C] (a x : C) (h : a ⟶ x) :
    (homFunctor a).map (𝟙 x) h = h :=
  id_comp h
```

**2.** 与 `List` 的证明一模一样：`R → Unit` 只有一个元素，而 `Option Unit` 有两个（`none` 和 `some ()`），所以 `index` 不可能是单射。用“对数”的语言说：`Option x = 1 + x`，在 $x = 1$ 时等于 2，而 $1^R = 1$。

```lean
theorem option_not_representable :
    ¬ ∃ (R : Type) (tab : {x : Type} → (R → x) → Option x) (idx : {x : Type} → Option x → R → x),
      ∀ {x : Type} (o : Option x), tab (idx o) = o := by
  intro ⟨R, tab, idx, h⟩
  have e : idx (some ()) = idx (none : Option Unit) := by funext r; rfl
  have : some () = (none : Option Unit) := calc
    some () = tab (idx (some ())) := (h _).symm
    _ = tab (idx none) := by rw [e]
    _ = none := h _
  cases this   -- some () = none 是不可能的：不同构造器
```

**3.** 可表，而且是最“原汁原味”的可表函子：`Reader a` 就是 hom 函子 `a → -` 本身。表示对象是 `a`，`tabulate` 和 `index` 都是恒等函数。

```lean
instance : Representable (Reader a) where
  Rep := a
  tabulate h := h
  index h := h

instance : LawfulRepresentable (Reader a) where
  index_tabulate _ := rfl
  tabulate_index _ := rfl
```

**4.** 制表一次，然后按下标查询：

```lean
namespace Rep

def squares : Stream Nat := Stream.tabulate (fun n => n * n)

#guard squares.index 7 == 49
#guard (List.range 6).map squares.index == [0, 1, 4, 9, 16, 25]

end Rep
```

如前所述，在严格的 Lean 里这个 `Stream` 并不真的缓存。若想要真正的备忘，可以借用流的表示把前若干项“截下来”制成数组：先把平方函数制成流，再用 `index` 读出前 10 项，交给 `Vector.ofFn` 一次性算好。之后的查询只是数组下标访问：

```lean
def memoSquares : Vector Nat 10 :=
  Vector.ofFn (fun (i : Fin 10) => Rep.squares.index i.val)

#guard memoSquares[7] == 49
```

**5.** 关键引理：`index` 沿着 `tail` 走 `n` 步，结果就是 `get n`。对 `n` 做归纳，并且让归纳假设对**所有**流成立（`generalizing s`），因为每走一步，流都换成了它的 `tail`：

```lean
namespace Rep

theorem Stream.index_eq_get (s : Stream α) (n : Nat) : s.index n = s.get n := by
  induction n generalizing s with
  | zero => rfl                                   -- index s 0 = head s = get 0
  | succ n ih => simp [Stream.index, ih, Stream.tail]  -- index s (n+1) = index (tail s) n = get (n+1)

instance : LawfulRepresentable Stream where
  index_tabulate h := by
    funext n
    exact Stream.index_eq_get _ n
  tabulate_index s := by
    show Stream.tabulate (Stream.index s) = s
    cases s with
    | mk g =>
      simp only [Stream.tabulate]
      congr
      funext n
      exact Stream.index_eq_get _ n

end Rep
```

`induction n generalizing s with` 是带“推广”的归纳：普通归纳的假设只对固定的 `s` 成立，而我们在归纳步骤中需要把它用在 `s.tail` 上，所以要先把 `s` 推广出去。`congr` 把“两个结构体相等”化归为“对应字段相等”。

**6.** `Pair x = x × x = x^2`，所以表示类型有两个元素：`Bool`。

```lean
structure Pair (α : Type) where
  fst : α
  snd : α

instance : Representable Pair where
  Rep := Bool
  tabulate h := ⟨h false, h true⟩
  index p b := if b then p.snd else p.fst

instance : LawfulRepresentable Pair where
  index_tabulate h := by funext b; cases b <;> rfl   -- 对 Bool 的两种情况分别验证
  tabulate_index p := rfl
```

`cases b <;> rfl` 的意思是：对 `b` 分成 `false`、`true` 两种情况，然后对**每一个**生成的目标都执行 `rfl`。
:::

## 参考资料

1. The Catsters 关于[可表函子](https://www.youtube.com/watch?v=4QgjKUzyrhM)的视频。

## 本章小结

- 集合是“没有特征的一团”，它的一切信息都编码在函数里；同构的集合（能一一配对）可以看作相同。我们可以放心地比较“元素种类不同”的集合。
- 固定对象 $a$，**hom 函子** $\mathcal{C}(a, -)$ 把 $x$ 映到 hom-集 $\mathcal{C}(a, x)$，把 $f$ 映到“后接 $f$”。在类型范畴里，它就是 `Reader a`，即 `a → -`。我们在 Lean 中证明了它满足函子定律。
- 固定终点得到逆变的 $\mathcal{C}(-, a)$（前接）；两个都放开得到剖函子 $\mathcal{C}(-, =) : \mathcal{C}^{op} \times \mathcal{C} \to \mathbf{Set}$。
- 与某个 hom 函子**自然同构**的函子叫**可表函子**；那个对象 $a$ 叫表示对象。程序员版本：`Representable` 类，关联类型 `Rep`，一对互逆函数 `tabulate`、`index`。
- 可表函子 = 函数的备忘表：`Stream` 由 `Nat` 表示，`Pair` 由 `Bool` 表示，`Vector · n` 由 `Fin n` 表示，`Reader a` 由 `a` 表示。
- `List`、`Option` 不可表：`R → Unit` 只有一个元素，而 `List Unit`、`Option Unit` 有不止一个。Lean 把这个直觉变成了几行证明。
- “$a = \log F$”：积类型函子由和类型表示；含“$1 +$”项的和类型函子一般不可表。
- Lean 是严格的、只含有限数据的语言：Haskell 式的 `data Stream` 在 Lean 中是空类型，“流 = `Nat → α`”反而让可表性一目了然；真正的备忘需要数组之类的数据结构。
- 在 Lean 中，多态函数的自然性不是免费的：需要时就写成显式条件并证明——下一章的米田引理会让我们看到这有多重要。
