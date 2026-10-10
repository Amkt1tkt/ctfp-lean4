# 3.6 范畴论视角下的单子

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

end CTFP

open CTFP Category
```

跟程序员提起单子，话题多半会转到“副作用”上去；跟数学家提起单子，他想到的却是“代数”。代数后面会专门讲（它们在编程里同样分量十足），不过在那之前，我想先给你一点直觉：代数和单子到底是怎么扯上关系的。下面这段论证有点“挥挥手”的味道，请先耐着性子听我说完。

代数研究的是怎样构造、变形、求值**表达式**。表达式由运算符搭起来。看这个简单的例子：

$$x^2 + 2x + 1$$

它由变量（比如 $x$）和常量（比如 $1$、$2$）组成，中间用加号、乘号之类的运算符粘在一起。程序员看到表达式，脑子里浮现的往往是一棵树：

![表达式树](/img/3.6/exptree.png "表达式 x² + 2x + 1 画成一棵树：内部结点是运算符，叶子是变量和常量。")

树是一种容器。所以更一般地说，表达式就是“装变量的容器”。在范畴论里，容器用自函子来刻画。如果变量 $x$ 的类型是 $a$，那么整个表达式的类型就是 $m\ a$，其中 $m$ 是一个“搭建表达式树”的自函子。（真正有分支的表达式，一般要用递归定义的自函子来造。）

在 Lean 里，这样的自函子写起来非常自然：

```lean
/-- 以 `α` 为变量类型的表达式树。 -/
inductive Expr (α : Type) where
  | var : α → Expr α                  -- 变量
  | lit : Int → Expr α                -- 整数常量
  | add : Expr α → Expr α → Expr α    -- 加法结点
  | mul : Expr α → Expr α → Expr α    -- 乘法结点
  deriving Repr

open Expr in
/-- x² + 2x + 1，这里只有一个变量，所以变量类型取 `Unit`。 -/
def poly : Expr Unit := add (mul (var ()) (var ())) (add (mul (lit 2) (var ())) (lit 1))
```

对表达式最常做的事情是什么？是**代入**（substitution）：把变量换成别的表达式。比如在上面的例子里，把 $x$ 换成 $y - 1$，就得到

$$(y - 1)^2 + 2 (y - 1) + 1$$

仔细看看发生了什么：我们拿到一个类型为 $m\ a$ 的表达式，再拿一个类型为 $a \to m\ b$ 的变换（$b$ 是 $y$ 的类型），得到一个类型为 $m\ b$ 的新表达式。把签名完整写出来就是：

$$m\ a \to (a \to m\ b) \to m\ b$$

没错，这正是单子 bind 的签名。

```lean
namespace Expr

/-- 代入：把每个变量 `x` 换成表达式 `σ x`。签名正是 bind 的签名。 -/
def subst : Expr α → (α → Expr β) → Expr β
  | var x,     σ => σ x
  | lit n,     _ => lit n
  | add e₁ e₂, σ => add (e₁.subst σ) (e₂.subst σ)
  | mul e₁ e₂, σ => mul (e₁.subst σ) (e₂.subst σ)

/-- 给变量赋值后求值。 -/
def eval (env : α → Int) : Expr α → Int
  | var x   => env x
  | lit n   => n
  | add a b => eval env a + eval env b
  | mul a b => eval env a * eval env b

end Expr

open Expr in
/-- 把 x 换成 y + (-1)，也就是 y - 1。 -/
def poly' : Expr Unit := poly.subst fun () => add (var ()) (lit (-1))

-- 代入之前，x = 4 时值为 25；代入之后，y = 5（于是 y - 1 = 4）时值也是 25。
#guard poly.eval (fun () => 4) == 25
#guard poly'.eval (fun () => 5) == 25
```

::: tip Rust 视角
`subst` 的形状就是 `Option::and_then` / `Iterator::flat_map` 的形状：`fn and_then<U>(self, f: impl FnOnce(T) -> Option<U>) -> Option<U>`。
“容器里每个元素都换成一个新容器，再把结果拼回一层”——代入表达式和 `flat_map` 是同一个动作。
:::

热身到此为止，下面进入单子的数学。数学家用的记号跟程序员不太一样：他们习惯用字母 $T$ 表示自函子，用希腊字母 $\mu$ 表示 `join`，用 $\eta$ 表示 `return`（Lean 里叫 `pure`）。`join` 和 `pure` 都是多态函数，所以不难猜到：它们对应的是自然变换。

于是，在范畴论里，**单子**（monad）被定义为一个自函子 $T$，外加一对自然变换 $\mu$ 和 $\eta$。

$\mu$ 是从函子的“平方” $T^2$ 回到 $T$ 的自然变换。所谓平方，就是函子和自己复合：$T \circ T$（只有自函子才能这么自乘，因为只有它的终点范畴和起点范畴是同一个）。

$$\mu :: T^2 \to T$$

这个自然变换在对象 $a$ 处的分量是态射

$$\mu_a :: T (T a) \to T a$$

翻译到类型与函数的范畴里，它恰好就是我们熟悉的 `join`。

$\eta$ 是从恒等函子 $I$ 到 $T$ 的自然变换：

$$\eta :: I \to T$$

恒等函子把对象 $a$ 映到 $a$ 自己，所以 $\eta$ 的分量是态射

$$\eta_a :: a \to T a$$

它恰好就是 `pure`。

::: info 数学小课堂：自函子的“平方”与自然变换的“分量”
- **自函子** $T : \mathcal{C} \to \mathcal{C}$ 的起点和终点是同一个范畴，所以可以接着再用一次：$T \circ T$ 把 $a$ 送到 $T(T a)$。我们把它简写成 $T^2$，同理 $T^3 = T \circ T \circ T$。对 `List` 来说，$T^2 a$ 就是 `List (List a)`。
- **自然变换** $\mu : T^2 \to T$ 是“一族函数”，每个对象 $a$ 一个：$\mu_a : T(T a) \to T a$。这一族函数叫做它的**分量**。
  对 `List`，$\mu_{\mathrm{Nat}}$ 是 `List (List Nat) → List Nat` 的 `List.flatten`，$\mu_{\mathrm{String}}$ 是 `List (List String) → List String` 的 `List.flatten`……
  在 Lean 里，这就是一个带隐式类型参数的多态函数 `List.flatten : {α : Type} → List (List α) → List α`。
- “自然”的意思是：这族函数与函子的 `map` 协调——先 `map f` 再压平，等于先压平再 `map f`。详见 [1.10 自然变换](/part1/10-natural-transformations)。
:::

::: tip Lean 深入：把 μ/η 形式的单子写成 Lean 结构体
为了让后面的论证都能在 Lean 里检查，我们先把“以 `join`/`pure` 为原语”的单子写成一个结构体。Lean 自带的 `Monad` 类以 `bind` 为原语（和 Haskell 一样），这里我们故意换一套原语，以便和数学定义一一对应。下面列出的定律，本节接下来会逐条解释：

```lean
/-- 以 `join`（μ）和 `pure`（η）为原语的单子结构。 -/
structure MonadJ (T : Type → Type) [Functor T] where
  /-- η 的分量：a → T a -/
  pure : α → T α
  /-- μ 的分量：T (T a) → T a -/
  join : T (T α) → T α
  /-- η 是自然变换：pure (f a) = map f (pure a) -/
  pure_natural : ∀ {α β} (f : α → β) (a : α), pure (f a) = f <$> pure a
  /-- μ 是自然变换：先对内层 map f 再压平 = 先压平再 map f -/
  join_natural : ∀ {α β} (f : α → β) (x : T (T α)), join ((f <$> ·) <$> x) = f <$> join x
  /-- 结合律：T³ 压成 T 的两种方式相同 -/
  join_assoc : ∀ {α} (x : T (T (T α))), join (join x) = join (join <$> x)
  /-- 左单位律：μ ∘ ηT = id -/
  join_pure : ∀ {α} (x : T α), join (pure x) = x
  /-- 右单位律：μ ∘ Tη = id -/
  join_map_pure : ∀ {α} (x : T α), join (pure <$> x) = x
```

- `pure : α → T α` 中的 `α` 没有声明。Lean 的 **auto-bound implicit** 会把它自动变成该字段的隐式参数，相当于 `pure : {α : Type} → α → T α`。所以一个 `MonadJ T` 值里装的是**多态**函数——正对应“自然变换是一族分量”。
- `(f <$> ·)` 是 `fun y => f <$> y` 的简写，`·` 是匿名参数的占位符。`(f <$> ·) <$> x` 就是“对两层容器的内层做 `map f`”。
- 为什么要把“自然性”也写成字段？在 Haskell（以及 Lean）中，任何一个用多态方式写出来的 `join` 都**自动**是自然的，这是参数性（parametricity）给的“免费定理”。但是参数性是一个元定理，Lean 的逻辑里没法直接引用它，所以我们老老实实把它列成需要证明的条款。好在对具体实例来说，这些证明几乎都是 `rfl`。
:::

这些自然变换还得满足一些额外的定律。理解这些定律的一个途径是：它们恰好保证了我们能为自函子 $T$ 定义一个 Kleisli 范畴。回忆一下，从 $a$ 到 $b$ 的 **Kleisli 箭头**是一个态射 $a \to T b$。两支这样的箭头的复合（我把它写成右下角带 $T$ 的小圆圈）可以借助 $\mu$ 来实现：

$$g \circ_T f = \mu_c \circ (T g) \circ f$$

其中

$$f :: a \to T b, \qquad g :: b \to T c$$

这里 $T$ 是函子，所以可以作用在态射 $g$ 上，得到 $T g : T b \to T(T c)$。把三段路连起来看最清楚（图是我们补画的）：

```diagram
A: (0, 0) "a"
TB: (1.7, 0) "T\,b"
TTC: (3.6, 0) "T(T\,c)"
TC: (5.4, 0) "T\,c"
f: A -> TB "f"
Tg: TB -> TTC "T\,g"
mu: TTC -> TC "\mu_c"
k: A -> TC "g \circ_T f" bend=-55 side=right color=brand
path "f，再 T g，再 μ": f Tg mu
path "Kleisli 复合 g ∘_T f": k color=green
caption: Kleisli 复合：先用 f 得到 T b，用 T g 把里面每个 b 换成 T c，最后用 μ 压平两层。
```

用 Lean 的记号写出来，也许更容易认出这个公式。下面的 `fish`（“鱼”运算符 `>=>` 的别名）就是 Kleisli 复合，它的无点（point-free）形式恰好是 $\mu \circ (T g) \circ f$：

```lean
namespace MonadJ
variable {T : Type → Type} [Functor T] (M : MonadJ T)

/-- Kleisli 复合（“鱼”运算符）：先 f，再在里面 map g，最后 join。 -/
def fish (f : α → T β) (g : β → T γ) : α → T γ :=
  fun a => M.join (g <$> f a)

/-- 无点写法：f >=> g = join ∘ map g ∘ f -/
theorem fish_eq_comp (f : α → T β) (g : β → T γ) :
    M.fish f g = M.join ∘ Functor.map g ∘ f := rfl

end MonadJ
```

或者写成分量（逐点）形式：

```lean
example {T : Type → Type} [Functor T] (M : MonadJ T) (f : α → T β) (g : β → T γ) (a : α) :
    M.fish f g a = M.join (g <$> f a) := rfl
```

从代数的角度解读，我们不过是把两次相继的代入复合起来：先用 `f` 把 `a` 代成一棵树，再用 `g` 把树上每个 `b` 代成一棵树，最后把“树套树”压平成一棵树。

::: tip Lean 深入
Lean 核心库其实已经有 Kleisli 复合运算符 `>=>`（`Bind.kleisliRight`），只不过它是用 `bind` 实现的。例如
`((fun n => some (n+1)) >=> (fun n => some (n*2))) 3 = some 8`。我们的 `fish` 是同一个东西的 `join` 版本。
:::

要让 Kleisli 箭头构成范畴，我们需要复合满足结合律，并且 $\eta_a$ 充当 $a$ 上的恒等 Kleisli 箭头。这两条要求可以翻译成关于 $\mu$ 和 $\eta$ 的单子定律。不过还有另一种推导方式，推出来的定律看上去更像幺半群定律。事实上，$\mu$ 常常被叫作**乘法**（multiplication），$\eta$ 被叫作**单位**（unit）。

粗略地说，结合律说的是：把 $T$ 的立方 $T^3$ 压成 $T$ 有两种办法，结果必须一样。两条单位律（左和右）说的是：先用 $\eta$ 给 $T$ 多包一层、再用 $\mu$ 压回去，就回到了原来的 $T$。

事情之所以有点绕，是因为我们同时在复合自然变换和函子。所以需要先复习一下**横向复合**（horizontal composition）。比如，$T^3$ 可以看作 $T$ 跟在 $T^2$ 后面的复合。对它可以施加两个自然变换的横向复合：

$$I_T \circ \mu$$

![横向复合 I_T ∘ μ](/img/3.6/assoc1.png "左边的格子里，μ 把 T² 变成 T；右边的格子里，恒等自然变换 I_T 把 T 原样留下。两格横向拼起来，就是作用在 T³ 上的 I_T ∘ μ。")

结果是 $T \circ T$，它可以再用一次 $\mu$ 压成 $T$。这里 $I_T$ 是从 $T$ 到 $T$ 的恒等自然变换。你常会看到这种横向复合 $I_T \circ \mu$ 被简写成 $T \circ \mu$。这个简写不会有歧义：把函子和自然变换复合本来没有意义，所以在这个语境里 $T$ 只能是指 $I_T$。

我们也可以在（自）函子范畴 $[\mathcal{C}, \mathcal{C}]$ 里画出这条路径：

![函子范畴中的 T∘μ 再 μ](/img/3.6/assoc2.png "在函子范畴 [C, C] 里：T³ 经 T∘μ 到 T²，再经 μ 到 T。")

::: info 数学小课堂：$T\circ\mu$ 和 $\mu\circ T$ 的分量到底是什么？
横向复合听起来吓人，落到分量上其实很朴素（这种“自然变换与函子的复合”也常被叫作 *whiskering*，“加胡须”）：

| 记号 | 在 $a$ 处的分量 | 对 `List` 来说 | 直观含义 |
|---|---|---|---|
| $\mu \circ T$（也写 $\mu T$） | $\mu_{T a} : T(T(T a)) \to T(T a)$ | `List.flatten`，作用在 `List (List (List a))` 上 | 把**外面两层**压成一层 |
| $T \circ \mu$（也写 $T\mu$） | $T(\mu_a) : T(T(T a)) \to T(T a)$ | `List.map List.flatten` | 把**里面两层**压成一层 |
| $\eta \circ T$ | $\eta_{T a} : T a \to T(T a)$ | `fun xs => [xs]` | 在**外面**包一层 |
| $T \circ \eta$ | $T(\eta_a) : T a \to T(T a)$ | `List.map (fun x => [x])` | 在**每个元素外面**包一层 |

记忆方法：$T$ 写在左边，就是“用 $T$ 的 `map` 把它送进去，作用在里层”；$T$ 写在右边，就是“在下标处代入 $T a$，作用在外层”。
:::

另一种办法是把 $T^3$ 看成 $T^2 \circ T$，对它施加 $\mu \circ T$。结果同样是 $T \circ T$，再用 $\mu$ 压成 $T$。我们要求这两条路径给出相同的结果：

```diagram
T3: (0, 0) "T^3"
T2a: (2.6, 0) "T^2"
T2b: (0, 1.9) "T^2"
T: (2.6, 1.9) "T"
muT: T3 -> T2a "\mu \circ T"
Tmu: T3 -> T2b "T \circ \mu" side=right
mu1: T2a -> T "\mu"
mu2: T2b -> T "\mu" side=right
path "μ∘T 再 μ（先压外层）": muT mu1
path "T∘μ 再 μ（先压内层）": Tmu mu2 color=green
caption: 单子的结合律：从 T³ 到 T 的两条路径相等，即 μ ∘ (μ∘T) = μ ∘ (T∘μ)。
```

![结合律](/img/3.6/assoc.png "结合律的交换图（原书手绘版）。")

类似地，把横向复合 $\eta \circ T$ 作用在“恒等函子 $I$ 跟在 $T$ 后面”的复合上，得到 $T^2$，再用 $\mu$ 压回去；结果应当和直接对 $T$ 施加恒等自然变换一样。对称地，$T \circ \eta$ 也应如此：

```diagram
IT: (0, 0) "I \circ T"
TT: (2.2, 0) "T^2"
TI: (4.4, 0) "T \circ I"
T: (2.2, 1.7) "T"
etaT: IT -> TT "\eta \circ T"
Teta: TI -> TT "T \circ \eta" side=right
mu: TT -> T "\mu"
idl: IT -> T "\mathrm{id}_T" side=right
idr: TI -> T "\mathrm{id}_T"
path "η∘T 再 μ": etaT mu
path "左边直接走 id": idl color=green
path "T∘η 再 μ": Teta mu color=orange
path "右边直接走 id": idr color=purple
caption: 单子的两条单位律：μ ∘ (η∘T) = id_T = μ ∘ (T∘η)。
```

![单位律](/img/3.6/unitlawcomp-1.png "单位律的交换图（原书手绘版）。")

下面这个小工具把这两张图“落到实处”：选一个 `List (List (List α))` 或 `Option (Option (Option α))`，一步步执行两条路径。每一步先用删除线预告“哪一层括号要被 μ 抹掉”，再真正执行。你会看到：先抹第 2 层还是先抹第 3 层，最后都只剩最外一层，而且内容一模一样——这就是结合律；先在外面包一层还是在每个元素外面包一层，μ 都会把它原样收回——这就是单位律。

<div class="ctfp-widget-host"><Ch3_6JoinLayers /></div>

你可以自己验证：这些定律保证了 Kleisli 箭头的复合确实满足范畴的定律。在 Lean 里，“自己验证”可以变成真正的证明：

```lean
namespace MonadJ
variable {T : Type → Type} [Functor T] (M : MonadJ T)

/-- η 是 Kleisli 复合的左单位元：先 pure 再 f，等于 f。 -/
theorem fish_pure_left (f : α → T β) : M.fish M.pure f = f := by
  funext a
  simp only [fish]
  -- 目标：join (f <$> pure a) = f a
  rw [← M.pure_natural]   -- f <$> pure a 换成 pure (f a)（η 的自然性）
  rw [M.join_pure]        -- join (pure _) = _（左单位律）

/-- η 是 Kleisli 复合的右单位元：先 f 再 pure，等于 f。 -/
theorem fish_pure_right (f : α → T β) : M.fish f M.pure = f := by
  funext a
  simp only [fish, M.join_map_pure]   -- join (pure <$> f a) = f a（右单位律）

/-- Kleisli 复合满足结合律。这里要用到函子定律，所以加上 `LawfulFunctor`。 -/
theorem fish_assoc [LawfulFunctor T] (f : α → T β) (g : β → T γ) (h : γ → T δ) :
    M.fish (M.fish f g) h = M.fish f (M.fish g h) := by
  funext a
  simp only [fish]
  -- 右边里有 join (map (fun b => join (h <$> g b)) …)，
  -- 先用 μ 的自然性把内层的 h 提出来，再用结合律把两个 join 合并
  rw [← M.join_natural, M.join_assoc]
  simp only [Functor.map_map]   -- 函子定律：map g ∘ map f = map (g ∘ f)
  rfl

end MonadJ
```

::: tip Lean 深入：这几个 tactic
- `funext a`：要证两个函数相等，只需证它们在任意参数 `a` 上相等（函数外延性）。
- `simp only [fish]`：只用给定的引理/定义做化简，这里是把 `fish` 展开。
- `rw [h]`：用等式 `h : x = y` 把目标中的 `x` 改写成 `y`；`rw [← h]` 反方向改写。
- `Functor.map_map` 来自 `LawfulFunctor`，内容是 `g <$> (f <$> x) = (g ∘ f) <$> x`。
:::

::: details 补充：三个实例——给 Option、List、State 装上 μ/η，并证明全部定律
本章后面还会用到这三个实例。`Option` 的情况最简单，按情况拆开就全是 `rfl`：

```lean
def optionJ : MonadJ Option where
  pure := some
  join := Option.join          -- some (some a) ↦ some a；其余 ↦ none
  pure_natural _ _ := rfl
  join_natural f x := by cases x <;> rfl
  join_assoc x := by cases x <;> rfl
  join_pure _ := rfl
  join_map_pure x := by cases x <;> rfl

#guard optionJ.join (some (some 3)) == some 3
#guard optionJ.join (some (none : Option Nat)) == none
```

`List` 的 μ 是 `List.flatten`（压平），η 是“做成单元素列表”。定律要对列表做归纳。Lean 核心库给 `List` 提供了 `Functor` 实例，但没有附带 `LawfulFunctor` 实例，我们顺手补上：

```lean
instance : LawfulFunctor List where
  map_const := rfl
  id_map xs := by simp [Functor.map]
  comp_map f g xs := by simp [Functor.map]

def listJ : MonadJ List where
  pure a := [a]
  join := List.flatten
  pure_natural _ _ := rfl
  join_natural f x := by
    induction x with
    | nil => rfl
    | cons xs xss ih => simp_all [Functor.map]
  join_assoc x := by
    induction x with
    | nil => rfl
    | cons xs xss ih => simp_all [Functor.map]
  join_pure x := by simp
  join_map_pure x := by
    induction x with
    | nil => rfl
    | cons x xs ih => simp_all [Functor.map]

#guard listJ.join [[1, 2], [], [3]] == [1, 2, 3]
```

这里的 `induction x with | nil => … | cons xs xss ih => …` 是对列表做结构归纳：`nil` 分支证明空列表的情形；`cons` 分支里，`ih` 是归纳假设（对尾部 `xss` 已经成立）。`simp_all` 会把所有假设和目标一起化简，常常能顺手用上 `ih`。

最后是 State。为了让定义一目了然，我们自己定义一个 `State`（与 Lean 自带的 `StateM` 同构）：

```lean
/-- 状态单子：读入一个状态，返回结果和新状态。 -/
structure State (σ α : Type) where
  run : σ → α × σ

instance : Functor (State σ) where
  map f m := ⟨fun s => let p := m.run s; (f p.1, p.2)⟩

instance : LawfulFunctor (State σ) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

def stateJ : MonadJ (State σ) where
  pure a := ⟨fun s => (a, s)⟩
  -- 先跑外层动作得到 (内层动作, 新状态)，再用新状态跑内层动作
  join m := ⟨fun s => let p := m.run s; p.1.run p.2⟩
  pure_natural _ _ := rfl
  join_natural _ _ := rfl
  join_assoc _ := rfl
  join_pure _ := rfl
  join_map_pure _ := rfl
```

State 的五条定律全部是 `rfl`：Lean 只需把定义展开、对 `Prod` 和结构体做 η-展开，两边就逐字相同了。
:::

单子和幺半群的相似之处太明显了：有乘法 $\mu$、有单位 $\eta$、有结合律、有单位律。可是我们现有的幺半群定义太窄，装不下单子。所以，下面我们把幺半群的概念推广一下。

## 幺半范畴

回到幺半群的传统定义：一个集合，配上一个二元运算和一个叫做单位的特殊元素。在 Lean 里可以写成一个类型类（核心库没有 `Monoid`，我们自己起个名字 `MonoidC`）：

```lean
class MonoidC (m : Type) where
  mappend : m → m → m
  mempty : m
```

二元运算 `mappend` 必须满足结合律和单位律（与单位 `mempty` 相乘什么也不改变）。

注意，在 Lean 中 `mappend` 的类型是柯里化的。可以把它理解成：把 `m` 的每个元素映成一个函数：

```lean no-check
mappend : m → (m → m)
```

正是这种理解，引出了“幺半群是只有一个对象的范畴”这一定义：自态射 `m → m` 代表幺半群的元素（见 [1.3 大大小小的范畴](/part1/03-categories-great-and-small)）。不过，既然柯里化在 Lean 里是内建的，我们也完全可以从另一种乘法定义出发：

```lean no-check
mu : m × m → m
```

这里，笛卡尔积 `m × m` 成了“待相乘的一对元素”的来源。

这个定义指向另一条推广之路：把笛卡尔积换成范畴论的积。我们可以从一个处处有积的范畴出发，在里面选一个对象 `m`，再把乘法定义成一个态射：

$$\mu :: m \times m \to m$$

但还有一个问题：在任意范畴里，我们看不到对象内部，那怎么挑出单位元呢？这里有个小技巧。还记得吗，“挑出一个元素”等价于“一个从单元素集合出发的函数”。在 Lean 里，可以把 `mempty` 换成一个函数：

```lean no-check
eta : Unit → m
```

单元素集合是 $\mathbf{Set}$ 中的终对象，所以很自然地，可以把这个定义推广到任何有终对象 $t$ 的范畴：

$$\eta :: t \to m$$

这样我们就能在不谈论“元素”的前提下，挑出单位“元素”了。

::: info 数学小课堂：用箭头“指”出一个元素
在集合的世界里，从单元素集合 $\{\ast\}$ 到集合 $S$ 的函数，完全由它把 $\ast$ 送到哪里决定。所以“$S$ 的元素”和“函数 $\{\ast\} \to S$”一一对应。
在 Lean 中：`Unit → m` 类型的函数 `fun () => x` 就“是”元素 `x`。这让我们可以在“只看箭头，不看元素”的范畴论里谈论“特定元素”。单元素集合正是 $\mathbf{Set}$ 的终对象（见 [1.5 积与余积](/part1/05-products-and-coproducts)）。
:::

和前面“单对象范畴”的幺半群定义不同，这里的幺半群定律不会自动成立，需要我们另外施加。可是，要写出这些定律，得先弄清楚底层的范畴积本身的幺半结构。我们先回顾一下在类型的世界里这件事是怎么回事。

先看结合律。逐点写出来的等式是：

```lean no-check
mu (x, mu (y, z)) = mu (mu (x, y), z)
```

要把它推广到别的范畴，必须先把它改写成函数（态射）之间的等式。也就是说，要把它从“对单个变量的作用”中抽象出来——换句话说，要用无点（point-free）写法。笛卡尔积是一个双函子（[1.8 函子性](/part1/08-functoriality)），它可以同时作用在一对函数上：Lean 里这就是 `Prod.map f g : α × β → γ × δ`。利用它，左边可以写成

```lean no-check
(mu ∘ Prod.map id mu) (x, (y, z))
```

右边可以写成

```lean no-check
(mu ∘ Prod.map mu id) ((x, y), z)
```

几乎是我们想要的了。可惜笛卡尔积不是严格结合的——`(x, (y, z))` 和 `((x, y), z)` 不是同一个东西——所以我们不能直接写成无点形式：

```lean no-check
mu ∘ Prod.map id mu = mu ∘ Prod.map mu id   -- 类型都对不上！
```

另一方面，这两种嵌套的二元组是同构的。有一个可逆函数在它们之间转换，叫做**结合子**（associator）：

```lean
def alpha : (α × β) × γ → α × (β × γ) := fun ((x, y), z) => (x, (y, z))
```

借助结合子，可以写出 `mu` 的无点结合律：

```lean no-check
mu ∘ Prod.map id mu ∘ alpha = mu ∘ Prod.map mu id
```

单位律可以如法炮制。它们在新记号下的逐点形式是：

```lean no-check
mu (eta (), x) = x
mu (x, eta ()) = x
```

可以改写成：

```lean no-check
(mu ∘ Prod.map eta id) ((), x) = lambda ((), x)
(mu ∘ Prod.map id eta) (x, ()) = rho (x, ())
```

同构 `lambda` 和 `rho` 分别叫做**左单位子**（left unitor）和**右单位子**（right unitor）。它们见证了这样一个事实：在同构意义下，单位 `()` 是笛卡尔积的单位元：

```lean
def lambda : Unit × α → α := fun ((), x) => x
def rho : α × Unit → α := fun (x, ()) => x
```

于是，单位律的无点版本是：

```lean no-check
mu ∘ Prod.map id eta = rho
mu ∘ Prod.map eta id = lambda
```

我们利用“笛卡尔积本身在类型范畴里就像一种幺半乘法”这一事实，给 `mu` 和 `eta` 写出了无点的幺半群定律。不过别忘了：笛卡尔积自己的结合律和单位律只在同构意义下成立。

把这些写成一个 Lean 结构体，并检验字符串拼接确实是一个“无点幺半群”：

```lean
/-- 用 μ : m × m → m 和 η : Unit → m 表述的幺半群，定律全部写成函数等式。 -/
structure PFMonoid (m : Type) where
  mu : m × m → m
  eta : Unit → m
  assoc : mu ∘ Prod.map id mu ∘ alpha = mu ∘ Prod.map mu id
  left_unit : mu ∘ Prod.map eta id = lambda
  right_unit : mu ∘ Prod.map id eta = rho

def stringPF : PFMonoid String where
  mu := fun (x, y) => x ++ y
  eta := fun () => ""
  assoc := by funext ⟨⟨x, y⟩, z⟩; simp [alpha, String.append_assoc]
  left_unit := by funext ⟨(), x⟩; simp [lambda]
  right_unit := by funext ⟨x, ()⟩; simp [rho]
```

传统的（柯里化的）幺半群定义和无点定义是等价的。下面证明其中一个方向：满足定律的 `MonoidC` 总能给出一个 `PFMonoid`。

```lean
/-- 传统幺半群定律（逐点形式）。 -/
class LawfulMonoidC (m : Type) [MonoidC m] : Prop where
  assoc : ∀ x y z : m, MonoidC.mappend x (MonoidC.mappend y z)
                     = MonoidC.mappend (MonoidC.mappend x y) z
  left_id : ∀ x : m, MonoidC.mappend MonoidC.mempty x = x
  right_id : ∀ x : m, MonoidC.mappend x MonoidC.mempty = x

def toPF (m : Type) [MonoidC m] [LawfulMonoidC m] : PFMonoid m where
  mu := fun (x, y) => MonoidC.mappend x y
  eta := fun () => MonoidC.mempty
  -- `funext ⟨⟨x, y⟩, z⟩` 一边引入参数，一边把二元组拆开
  assoc := by funext ⟨⟨x, y⟩, z⟩; exact LawfulMonoidC.assoc x y z
  left_unit := by funext ⟨(), x⟩; exact LawfulMonoidC.left_id x
  right_unit := by funext ⟨x, ()⟩; exact LawfulMonoidC.right_id x
```

事实证明，这些定律可以推广到任何有积和终对象的范畴。范畴积在同构意义下确实满足结合律，终对象在同构意义下确实是单位。结合子和两个单位子都是**自然同构**。这些定律可以画成交换图：

```diagram
A: (0, 0) "(m \times m) \times m"
B: (3.2, 0) "m \times (m \times m)"
C: (0, 1.5) "m \times m"
D: (3.2, 1.5) "m \times m"
M: (1.6, 2.6) "m"
alpha: A -> B "\alpha"
l: A -> C "\mu \times \mathrm{id}" side=right
r: B -> D "\mathrm{id} \times \mu"
ml: C -> M "\mu" side=right
mr: D -> M "\mu"
path "先乘左边两个": l ml
path "先换括号，再乘右边两个": alpha r mr color=green
caption: 积上的幺半群结合律：两条路径相等（结合子 α 负责把括号换过来）。
```

![积上的结合律](/img/3.6/assocmon.png "积上的幺半群结合律（原书手绘版）。")

```diagram
IM: (0, 0) "\mathbf{1} \times m"
MM: (2.2, 0) "m \times m"
MI: (4.4, 0) "m \times \mathbf{1}"
M: (2.2, 1.7) "m"
el: IM -> MM "\eta \times \mathrm{id}"
er: MI -> MM "\mathrm{id} \times \eta" side=right
mu: MM -> M "\mu"
lam: IM -> M "\lambda" side=right
rho: MI -> M "\rho"
path "η×id 再 μ": el mu
path "左单位子 λ": lam color=green
path "id×η 再 μ": er mu color=orange
path "右单位子 ρ": rho color=purple
caption: 积上的幺半群单位律（1 是终对象，在 Lean 中就是 Unit）。
```

注意，因为积是双函子，它能同时提升一对态射——在 Lean 里这件事由 `Prod.map` 完成。

我们本可以就此打住，宣布：在任何有范畴积和终对象的范畴上都能定义幺半群。只要能挑出一个对象 $m$ 和两个满足幺半群定律的态射 $\mu$、$\eta$，就有了一个幺半群。但我们还能做得更好。要写出 $\mu$ 和 $\eta$ 的定律，其实用不着一个货真价实的范畴积。回忆一下，积是用一个借助投影的泛构造来定义的。而在写幺半群定律时，我们一次投影都没用过。

一个行为像积、但又不一定是积的双函子，叫做**张量积**（tensor product），通常记作中缀运算符 $\otimes$。张量积的一般定义有点微妙，但我们不必操心，只要列出它的性质——最重要的是同构意义下的结合律。

同样，对象 $t$ 也不必是终对象。我们从没用过它的“终”性质——也就是“从任何对象到它都有唯一态射”。我们需要的只是它和张量积配合得好：在同构意义下，它是张量积的单位。全部合起来：

**幺半范畴**（monoidal category）是一个范畴 $\mathcal{C}$，配上一个叫做张量积的双函子

$$\otimes :: \mathcal{C} \times \mathcal{C} \to \mathcal{C}$$

和一个叫做**单位对象**的特定对象 $i$，以及三个自然同构，分别叫结合子、左单位子和右单位子：

$$
\begin{aligned}
\alpha_{a b c} &:: (a \otimes b) \otimes c \to a \otimes (b \otimes c) \\
\lambda_a &:: i \otimes a \to a \\
\rho_a &:: a \otimes i \to a
\end{aligned}
$$

（还有一个化简四重张量积的相容性条件。）

::: info 数学小课堂：同构与自然同构
- **同构**（isomorphism）$f : a \to b$ 是有逆的态射：存在 $g : b \to a$ 使 $g \circ f = \mathrm{id}_a$、$f \circ g = \mathrm{id}_b$。同构的两个对象“换个包装而已”，比如 `(x, (y, z))` 和 `((x, y), z)`。
- **自然同构**是每个分量都是同构的自然变换。$\alpha$ 是自然的，意思是：“先换括号再对三个分量分别做 $f, g, h$”等于“先分别做再换括号”。直观上：换括号这件事不偷看里面装的是什么。
:::

重要的是，张量积描述了许多我们熟悉的双函子。特别地，它适用于积、余积，以及——我们马上会看到——自函子的复合（还适用于一些更玄妙的积，比如 Day 卷积）。幺半范畴在[富集范畴](/part3/12-enriched-categories)的表述中会扮演关键角色。

### 补充：五边形与三角形——为什么需要它们

原书只用一句话带过了“相容性条件”（coherence condition），但它们值得多看一眼。具体有两条。

**五边形恒等式**（pentagon identity）。四个对象相乘，有五种加括号的方式。从最左结合的 $((a\otimes b)\otimes c)\otimes d$ 到最右结合的 $a\otimes(b\otimes(c\otimes d))$，用结合子一步步换括号，有两条路：上面那条走三步，下面那条走两步。五边形恒等式要求它们相等：

```diagram
N1: (0, 1.1) "((a \otimes b) \otimes c) \otimes d"
N2: (1.6, 0) "(a \otimes (b \otimes c)) \otimes d"
N3: (3.8, 0) "a \otimes ((b \otimes c) \otimes d)"
N5: (5.4, 1.1) "a \otimes (b \otimes (c \otimes d))"
N4: (2.7, 2.3) "(a \otimes b) \otimes (c \otimes d)"
a1: N1 -> N2 "\alpha_{a,b,c} \otimes \mathrm{id}_d"
a2: N2 -> N3 "\alpha_{a,\,b \otimes c,\,d}"
a3: N3 -> N5 "\mathrm{id}_a \otimes \alpha_{b,c,d}"
b1: N1 -> N4 "\alpha_{a \otimes b,\,c,\,d}" side=right
b2: N4 -> N5 "\alpha_{a,\,b,\,c \otimes d}" side=right
path "上路：三步换括号": a1 a2 a3
path "下路：两步换括号": b1 b2 color=green
caption: 五边形恒等式：两条换括号的路线必须给出同一个同构。
```

**三角形恒等式**（triangle identity）。中间夹一个单位对象时，“先换括号再用左单位子吃掉 $i$”与“直接用右单位子吃掉 $i$”必须一致：

```diagram
T1: (0, 0) "(a \otimes i) \otimes b"
T2: (2.8, 0) "a \otimes (i \otimes b)"
T3: (1.4, 1.5) "a \otimes b"
al: T1 -> T2 "\alpha_{a,i,b}"
rh: T1 -> T3 "\rho_a \otimes \mathrm{id}_b" side=right
la: T2 -> T3 "\mathrm{id}_a \otimes \lambda_b"
path "换括号，再 λ": al la
path "直接 ρ": rh color=green
caption: 三角形恒等式：消去中间的单位对象，两种做法一致。
```

为什么非要这两条不可？想想我们为什么需要结合子：因为 $(a\otimes b)\otimes c$ 和 $a\otimes(b\otimes c)$ 不是同一个对象，只是同构。一旦对象多起来，“同构”就不止一个了：从一种括号方式到另一种括号方式，往往有好几条由 $\alpha$、$\lambda$、$\rho$ 拼成的路线。如果这些路线给出**不同**的同构，那么“$m$ 的四次方”就不是一个明确的东西——你说的 $m\otimes m\otimes m\otimes m$ 到底按哪条路线认同？幺半群“任意加括号都一样”的广义结合律也就无从谈起。

Mac Lane 的**相容性定理**（coherence theorem）说：只要五边形和三角形这两张图交换，那么**所有**由结合子、单位子（及其逆、张量、复合）拼成的、起点终点相同的图都自动交换。换句话说，这两条有限的检查，一劳永逸地保证了“怎么换括号都无所谓”。这和幺半群本身很像：只要三元结合律成立，任意长的乘积怎么加括号都相等——五边形就是“结合子这个层面的结合律”。

::: tip Rust 视角
`((a, b), c)` 和 `(a, (b, c))` 在 Rust 里也是不同的类型，你需要写 `fn assoc<A, B, C>(((a, b), c): ((A, B), C)) -> (A, (B, C))` 来转换。
五边形恒等式保证的是：对一个四层嵌套的元组，不管你用哪种顺序调用这些 `assoc` 辅助函数把它“摊平”成右结合的形式，最后得到的值都一样。对元组来说这显然成立，所以下面 Lean 的证明全是 `rfl`；但对一般的幺半范畴，这是需要检查的公理。
:::

### 补充：用 Lean 定义幺半范畴

先定义范畴中的同构，再把幺半范畴写成一个类型类。每个字段都对应上面数学定义中的一项：

```lean
/-- 范畴中的同构：一对互逆的态射。 -/
structure Iso {C : Type u} [Category.{u, v} C] (a b : C) where
  hom : a ⟶ b
  inv : b ⟶ a
  inv_hom : inv ⊚ hom = 𝟙 a
  hom_inv : hom ⊚ inv = 𝟙 b

class Monoidal (C : Type u) [Category.{u, v} C] where
  /-- 张量积作用在对象上 -/
  tensor : C → C → C
  /-- 张量积作用在态射上（双函子的 bimap） -/
  tensorHom : {a b c d : C} → (a ⟶ b) → (c ⟶ d) → (tensor a c ⟶ tensor b d)
  /-- 单位对象 i -/
  tensorUnit : C
  /-- 双函子定律：保持恒等 -/
  tensor_id : ∀ (a b : C), tensorHom (𝟙 a) (𝟙 b) = 𝟙 (tensor a b)
  /-- 双函子定律：保持复合 -/
  tensor_comp : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : C} (f : a₁ ⟶ a₂) (f' : a₂ ⟶ a₃) (g : b₁ ⟶ b₂) (g' : b₂ ⟶ b₃),
    tensorHom (f' ⊚ f) (g' ⊚ g) = tensorHom f' g' ⊚ tensorHom f g
  /-- 结合子 α -/
  associator : (a b c : C) → Iso (tensor (tensor a b) c) (tensor a (tensor b c))
  /-- 左单位子 λ -/
  leftUnitor : (a : C) → Iso (tensor tensorUnit a) a
  /-- 右单位子 ρ -/
  rightUnitor : (a : C) → Iso (tensor a tensorUnit) a
  /-- α、λ、ρ 的自然性 -/
  associator_natural : ∀ {a a' b b' c c' : C} (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c'),
    tensorHom f (tensorHom g h) ⊚ (associator a b c).hom
      = (associator a' b' c').hom ⊚ tensorHom (tensorHom f g) h
  leftUnitor_natural : ∀ {a b : C} (f : a ⟶ b),
    f ⊚ (leftUnitor a).hom = (leftUnitor b).hom ⊚ tensorHom (𝟙 tensorUnit) f
  rightUnitor_natural : ∀ {a b : C} (f : a ⟶ b),
    f ⊚ (rightUnitor a).hom = (rightUnitor b).hom ⊚ tensorHom f (𝟙 tensorUnit)
  /-- 五边形恒等式 -/
  pentagon : ∀ (a b c d : C),
    (associator a b (tensor c d)).hom ⊚ (associator (tensor a b) c d).hom
      = tensorHom (𝟙 a) (associator b c d).hom ⊚ (associator a (tensor b c) d).hom
          ⊚ tensorHom (associator a b c).hom (𝟙 d)
  /-- 三角形恒等式 -/
  triangle : ∀ (a b : C),
    tensorHom (𝟙 a) (leftUnitor b).hom ⊚ (associator a tensorUnit b).hom
      = tensorHom (rightUnitor a).hom (𝟙 b)

infixr:70 " ⊗ " => Monoidal.tensor
infixr:70 " ⊗ₘ " => Monoidal.tensorHom
notation "𝟭" => Monoidal.tensorUnit
```

类型与函数的范畴，以积 `×` 为张量积、`Unit` 为单位对象，构成一个幺半范畴。所有定律——包括五边形和三角形——都是 `rfl`：

```lean
instance productMonoidal : Monoidal Type where
  tensor a b := a × b
  tensorHom f g := Prod.map f g
  tensorUnit := Unit
  tensor_id _ _ := rfl
  tensor_comp _ _ _ _ := rfl
  associator _ _ _ :=
    { hom := fun ((x, y), z) => (x, (y, z)), inv := fun (x, (y, z)) => ((x, y), z),
      inv_hom := rfl, hom_inv := rfl }
  leftUnitor _ := { hom := fun (_, x) => x, inv := fun x => ((), x), inv_hom := rfl, hom_inv := rfl }
  rightUnitor _ := { hom := fun (x, _) => x, inv := fun x => (x, ()), inv_hom := rfl, hom_inv := rfl }
  associator_natural _ _ _ := rfl
  leftUnitor_natural _ := rfl
  rightUnitor_natural _ := rfl
  pentagon _ _ _ _ := rfl
  triangle _ _ := rfl
```

前面说过，余积也可以充当张量积，这时单位对象换成空类型 `Empty`（始对象）。在 Lean 里同样能把它写出来：

::: details 同一个范畴上的另一个幺半结构：余积 ⊕ 与 Empty
因为一个类型上只能有一个“默认”实例，这里用 `def` 而不是 `instance`。

```lean
@[reducible] def sumMonoidal : Monoidal Type where
  tensor a b := a ⊕ b
  tensorHom f g := Sum.map f g
  tensorUnit := Empty
  tensor_id _ _ := by funext x; cases x <;> rfl
  tensor_comp _ _ _ _ := by funext x; cases x <;> rfl
  associator _ _ _ :=
    { hom := (fun | .inl (.inl x) => .inl x | .inl (.inr y) => .inr (.inl y) | .inr z => .inr (.inr z)),
      inv := (fun | .inl x => .inl (.inl x) | .inr (.inl y) => .inl (.inr y) | .inr (.inr z) => .inr z),
      inv_hom := (by funext x; rcases x with (_ | _) | _ <;> rfl),
      hom_inv := by funext x; rcases x with _ | _ | _ <;> rfl }
  leftUnitor _ :=
    { hom := Sum.elim Empty.elim id
      inv := Sum.inr
      inv_hom := funext (fun | .inl e => e.elim | .inr _ => rfl)
      hom_inv := rfl }
  rightUnitor _ :=
    { hom := Sum.elim id Empty.elim
      inv := Sum.inl
      inv_hom := funext (fun | .inr e => e.elim | .inl _ => rfl)
      hom_inv := rfl }
  associator_natural _ _ _ := by funext x; rcases x with (_ | _) | _ <;> rfl
  leftUnitor_natural _ := funext fun | .inl e => e.elim | .inr _ => rfl
  rightUnitor_natural _ := funext fun | .inr e => e.elim | .inl _ => rfl
  pentagon _ _ _ _ := by funext x; rcases x with ((_ | _) | _) | _ <;> rfl
  triangle _ _ := funext fun | .inl (.inl _) => rfl | .inl (.inr e) => e.elim | .inr _ => rfl
```

`rcases x with (_ | _) | _` 一次把嵌套的 `Sum` 拆成三种情况；`e.elim` 处理 `Empty` 的“不可能情况”（空类型没有值，从它出发可以推出任何东西）。
:::

## 幺半范畴中的幺半群

现在可以在更一般的幺半范畴里定义幺半群了。先挑一个对象 $m$。用张量积可以构造 $m$ 的幂：$m$ 的平方是 $m \otimes m$。构造 $m$ 的立方有两种方式，但它们通过结合子同构。更高次幂也是如此（这就是需要相容性条件的地方）。要构成一个幺半群，需要挑出两个态射：

$$
\begin{aligned}
\mu &:: m \otimes m \to m \\
\eta &:: i \to m
\end{aligned}
$$

其中 $i$ 是张量积的单位对象。

![幺半群的猪](/img/3.6/monoid-1.jpg "幺半范畴中的幺半群：η 从单位对象（那个圆环）里“变出”一个 m，μ 把两个 m 乘成一个 m。")

这两个态射必须满足结合律和单位律，可以用下面两张交换图来表达：

```diagram
A: (0, 0) "(m \otimes m) \otimes m"
B: (3.2, 0) "m \otimes (m \otimes m)"
C: (0, 1.5) "m \otimes m"
D: (3.2, 1.5) "m \otimes m"
M: (1.6, 2.6) "m"
alpha: A -> B "\alpha"
l: A -> C "\mu \otimes \mathrm{id}" side=right
r: B -> D "\mathrm{id} \otimes \mu"
ml: C -> M "\mu" side=right
mr: D -> M "\mu"
path "μ⊗id 再 μ": l ml
path "α，id⊗μ，再 μ": alpha r mr color=green
caption: 幺半范畴中幺半群的结合律。
```

```diagram
IM: (0, 0) "i \otimes m"
MM: (2.2, 0) "m \otimes m"
MI: (4.4, 0) "m \otimes i"
M: (2.2, 1.7) "m"
el: IM -> MM "\eta \otimes \mathrm{id}"
er: MI -> MM "\mathrm{id} \otimes \eta" side=right
mu: MM -> M "\mu"
lam: IM -> M "\lambda" side=right
rho: MI -> M "\rho"
path "η⊗id 再 μ": el mu
path "λ": lam color=green
path "id⊗η 再 μ": er mu color=orange
path "ρ": rho color=purple
caption: 幺半范畴中幺半群的单位律。
```

![张量积上的结合律](/img/3.6/assoctensor.jpg "幺半群结合律（原书手绘版）。")

![张量积上的单位律](/img/3.6/unitmon.jpg "幺半群单位律（原书手绘版）。")

注意，张量积必须是双函子，这一点至关重要：我们需要提升一对态射，才能构造 $\mu \otimes \mathrm{id}$ 或 $\eta \otimes \mathrm{id}$ 这样的东西。这两张图不过是前面范畴积结论的直接推广。

补充一点 Lean：“幺半范畴中的幺半群”就是下面这个结构体，三条定律就是上面的交换图：

```lean
structure MonoidObj (C : Type u) [Category.{u, v} C] [Monoidal C] (m : C) where
  μ : m ⊗ m ⟶ m
  η : 𝟭 ⟶ m
  mul_assoc : μ ⊚ (μ ⊗ₘ 𝟙 m) = μ ⊚ (𝟙 m ⊗ₘ μ) ⊚ (Monoidal.associator m m m).hom
  unit_left : μ ⊚ (η ⊗ₘ 𝟙 m) = (Monoidal.leftUnitor m).hom
  unit_right : μ ⊚ (𝟙 m ⊗ₘ η) = (Monoidal.rightUnitor m).hom

/-- 在 (Type, ×, Unit) 中，自然数加法是一个幺半群。 -/
def natAdd : MonoidObj Type Nat where
  μ := fun (x, y) => x + y
  η := fun () => 0
  mul_assoc := by funext ⟨⟨x, y⟩, z⟩; exact Nat.add_assoc x y z
  unit_left := by funext ⟨(), x⟩; exact Nat.zero_add x
  unit_right := by funext ⟨x, ()⟩; rfl
```

::: details 补充：换一个张量积，幺半群就完全不同了
同一个范畴 **Type**，如果把张量积换成余积 `⊕`、单位对象换成 `Empty`，那么幺半群会变得非常无聊：μ 只能是“把两边合并”的余对角映射。证明只用两条单位律：

因为 `Type` 上已经有了以 `×` 为张量积的默认实例，我们先给 `Type` 起一个别名 `SumType`，把 `⊕` 结构挂在别名上：

```lean
def SumType : Type 1 := Type
instance : Category SumType := typeCategory
instance : Monoidal SumType := sumMonoidal

theorem sum_monoid_is_codiagonal {m : SumType} (M : MonoidObj SumType m) :
    ∀ x : m ⊕ m, M.μ x = Sum.elim id id x
  | .inl x => congrFun M.unit_right (.inl x)   -- μ ∘ (id ⊕ η) = ρ，在 inl x 上取值
  | .inr x => congrFun M.unit_left (.inr x)    -- μ ∘ (η ⊕ id) = λ，在 inr x 上取值
```

所以“幺半群”这个概念的内容，很大程度上取决于你选了哪个张量积。下一章我们会看到它的对偶：在 (**Type**, ×, Unit) 里，**余**幺半群同样无聊。正因如此，我们才要去别的幺半范畴里找有趣的幺半群——比如下一节的自函子范畴。
:::

## 单子即幺半群

幺半结构会在意想不到的地方冒出来，其中一个就是函子范畴。眯起眼睛看，你也许能把函子复合看成一种乘法。问题在于，并非任意两个函子都能复合——一个的终点范畴必须是另一个的起点范畴。这正是态射复合的通常规则——而我们知道，函子确实是范畴 $\mathbf{Cat}$ 中的态射。不过，就像自态射（绕回同一个对象的态射）总能复合一样，自函子也总能复合。对任意给定的范畴 $\mathcal{C}$，从 $\mathcal{C}$ 到 $\mathcal{C}$ 的自函子构成函子范畴 $[\mathcal{C}, \mathcal{C}]$：它的对象是自函子，态射是自函子之间的自然变换。从这个范畴里任取两个对象，比如自函子 $F$ 和 $G$，就能造出第三个对象 $F \circ G$——它们的复合，也是一个自函子。

自函子复合适合当张量积吗？首先要确认它是双函子。它能提升一对态射——在这里是一对自然变换——吗？张量积的 `bimap` 的类似物，签名大概长这样：

$$\mathit{bimap} :: (a \to b) \to (c \to d) \to (a \otimes c \to b \otimes d)$$

把对象换成自函子，箭头换成自然变换，张量积换成复合，就得到：

$$(F \to F') \to (G \to G') \to (F \circ G \to F' \circ G')$$

你也许认出来了，这正是横向复合的一个特例。

![横向复合](/img/3.6/horizcomp.png "横向复合：F ⟹ F′ 和 G ⟹ G′ 并排放，得到 F∘G ⟹ F′∘G′。")

我们手边还有恒等自函子 $I$，它可以充当自函子复合——我们新的张量积——的单位。而且函子复合满足结合律。事实上，结合律和单位律都是**严格**成立的——根本不需要结合子和两个单位子。所以，自函子构成一个以函子复合为张量积的**严格幺半范畴**。

这个范畴里的幺半群是什么？它是一个对象——也就是一个自函子 $T$；以及两个态射——也就是两个自然变换：

$$
\begin{gathered}
\mu :: T \circ T \to T \\
\eta :: I \to T
\end{gathered}
$$

不仅如此，幺半群定律就是：

```diagram
T2b: (0, 0) "T \otimes T"
T3: (3, 0) "T \otimes T \otimes T"
T2a: (6, 0) "T \otimes T"
T: (3, 1.8) "T"
muT: T3 -> T2a "\mu \otimes \mathrm{id}_T = \mu \circ T"
Tmu: T3 -> T2b "\mathrm{id}_T \otimes \mu = T \circ \mu" side=right
mu1: T2a -> T "\mu"
mu2: T2b -> T "\mu" side=right
path "μ⊗id 再 μ": muT mu1
path "id⊗μ 再 μ": Tmu mu2 color=green
caption: 自函子范畴中幺半群的结合律。张量积是复合，所以 T⊗T⊗T 就是 T³，结合子是恒等，原来的五个顶点只剩四个。
```

```diagram
IT: (0, 0) "I \otimes T"
TT: (2.2, 0) "T \otimes T"
TI: (4.4, 0) "T \otimes I"
T: (2.2, 1.7) "T"
etaT: IT -> TT "\eta \otimes \mathrm{id}_T"
Teta: TI -> TT "\mathrm{id}_T \otimes \eta" side=right
mu: TT -> T "\mu"
idl: IT -> T "\lambda = \mathrm{id}" side=right
idr: TI -> T "\rho = \mathrm{id}"
path "η⊗id 再 μ": etaT mu
path "λ": idl color=green
path "id⊗η 再 μ": Teta mu color=orange
path "ρ": idr color=purple
caption: 自函子范畴中幺半群的单位律：单位子也是恒等。
```

![结合律](/img/3.6/assoc.png "自函子范畴中幺半群的结合律（原书手绘版）。")

![单位律](/img/3.6/unitlawcomp.png "自函子范畴中幺半群的单位律（原书手绘版）。")

它们正是我们前面见过的单子定律。现在你明白 Saunders Mac Lane 那句名言了：

> All told, a monad is just a monoid in the category of endofunctors.
>
> 说到底，单子不过是自函子范畴中的一个幺半群。

在函数式编程的会议上，你也许见过印着这句话的 T 恤。

### 补充：把名言逐词拆开

这句话常被当成笑话（“这不是废话吗？”），但现在你已经有了理解它的全部零件。逐词对照一下：

| 名言里的词 | 在 (**Set**, ×, 1) 中的普通幺半群 | 在 ([**C**, **C**], ∘, I) 中的单子 |
|---|---|---|
| “范畴” | 集合与函数 | 自函子与自然变换 |
| “张量积” $\otimes$ | 笛卡尔积 $\times$ | 函子复合 $\circ$ |
| 单位对象 $i$ | 单元素集合 $\mathbf{1}$ | 恒等函子 $I$ |
| 载体对象 $m$ | 一个集合，例如 `Nat` | 一个自函子，例如 `List` |
| 乘法 $\mu : m\otimes m \to m$ | `Nat × Nat → Nat` 的加法 | $\mu : T\circ T \Rightarrow T$，即 `join` |
| 单位 $\eta : i \to m$ | `Unit → Nat`，挑出 `0` | $\eta : I \Rightarrow T$，即 `pure` |
| $m\otimes m\otimes m$ | $m \times m \times m$（三元组） | $T\circ T\circ T$（三层嵌套） |
| 结合律 | $(x+y)+z = x+(y+z)$ | 先压外层还是先压内层，结果一样 |
| 单位律 | $0 + x = x = x + 0$ | 外面包一层或里面包一层再压掉，都回到原样 |

::: warning 易错点
- 这里的“乘法”**不是**把 `T a` 里的元素乘起来！`List a` 在 `++` 下恰好也是幺半群，但那是另一回事（那是 **Set** 中的幺半群）。单子的“乘法”是把**两层函子**乘成一层：`List (List a) → List a`。“两个因子”是外层的 `List` 和内层的 `List`，不是两个列表值。
- 张量积是**复合** $T \circ T$，不是逐点的积 $a \mapsto T a \times T a$。如果你在自函子范畴里换用逐点积当张量积，得到的“幺半群”是完全不同的东西；而换用 Day 卷积当张量积，得到的幺半群恰好是 **Applicative** 函子。单子之所以是单子，正是因为选了“复合”这种乘法。
- 函子复合的结合律和单位律是**严格**的（`T (T (T a))` 只有一种读法），所以在这个幺半范畴里 $\alpha$、$\lambda$、$\rho$ 都是恒等，五边形和三角形自动成立。
:::

### 补充：在 Lean 中让名言通过类型检查

光看表格还不够过瘾。既然我们已经在 Lean 里定义了 `Monoidal` 和 `MonoidObj`，那就真的把自函子范畴做成一个幺半范畴，再证明 `List`、`Option`、`State` 都是其中的幺半群。为了简单，我们只考虑 **Type** 上的自函子。

第一步：自函子、复合、恒等函子。

```lean
/-- Type 上的自函子。 -/
abbrev Endo := CFunctor Type Type

/-- 复合 F ∘ G：先 G 后 F。这将是我们的张量积。 -/
def Endo.comp (F G : Endo) : Endo where
  obj a := F.obj (G.obj a)
  map f := F.map (G.map f)
  map_id a := by rw [G.map_id, F.map_id]
  map_comp f g := by rw [G.map_comp, F.map_comp]

/-- 恒等自函子 I。这将是单位对象。 -/
def Endo.id : Endo where
  obj a := a
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `List` 作为一个 `Endo`。 -/
def listEndo : Endo where
  obj := List
  map f := List.map f
  map_id a := by funext (xs : List a); simp [Category.id]
  map_comp {a _ _} f g := by funext (xs : List a); simp [Category.comp]

@[simp] theorem Endo.map_id' (F : Endo) (a : Type) : F.map (fun x : a => x) = fun x => x := F.map_id a
@[simp] theorem Endo.map_id_apply (F : Endo) (a : Type) (x : F.obj a) : F.map (fun x : a => x) x = x :=
  congrFun (F.map_id a) x
@[simp] theorem Endo.map_comp' (F : Endo) {a b c : Type} (f : a → b) (g : b → c) (x : F.obj a) :
    F.map (fun x => g (f x)) x = F.map g (F.map f x) := congrFun (F.map_comp f g) x
```

第二步：自函子范畴本身——对象是 `Endo`，态射是自然变换，复合是**纵向复合**（逐分量复合）。两个自然变换相等，只需各分量相等（自然性条件是命题，证明无关紧要）：

```lean
theorem NatTrans.ext' {F G : Endo} {α β : F ⟹ G} (h : ∀ a, α.app a = β.app a) : α = β := by
  cases α; cases β
  have : _ = _ := funext h
  subst this; rfl

instance endoCategory : Category Endo where
  Hom F G := F ⟹ G
  id F := { app := fun a => 𝟙 (F.obj a), naturality := fun _ => rfl }
  comp β α :=
    { app := fun a => β.app a ⊚ α.app a,
      -- 纵向复合的自然性：把两个自然性方块上下拼起来
      naturality := fun f => by
        rw [Category.assoc, β.naturality, ← Category.assoc, α.naturality, Category.assoc] }
  id_comp _ := NatTrans.ext' fun _ => rfl
  comp_id _ := NatTrans.ext' fun _ => rfl
  assoc _ _ _ := NatTrans.ext' fun _ => rfl
```

第三步：张量积在态射上的作用——**横向复合** $\alpha \circ \beta : F\circ G \Rightarrow F'\circ G'$，分量为 $\alpha_{G' a} \circ F(\beta_a)$：

```lean
def hcomp {F F' G G' : Endo} (α : F ⟹ F') (β : G ⟹ G') : Endo.comp F G ⟹ Endo.comp F' G' where
  app a := α.app (G'.obj a) ⊚ F.map (β.app a)
  naturality {a b} f := by
    show F'.map (G'.map f) ⊚ (α.app (G'.obj a) ⊚ F.map (β.app a))
       = (α.app (G'.obj b) ⊚ F.map (β.app b)) ⊚ F.map (G.map f)
    rw [Category.assoc, α.naturality, ← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp,
        β.naturality]

@[simp] theorem endo_id_app (F : Endo) (a : Type) : (𝟙 F : F ⟶ F).app a = fun x => x := rfl
@[simp] theorem endo_comp_app {F G H : Endo} (β : G ⟶ H) (α : F ⟶ G) (a : Type) :
    (β ⊚ α).app a = fun x => β.app a (α.app a x) := rfl
@[simp] theorem hcomp_app {F F' G G' : Endo} (α : F ⟹ F') (β : G ⟹ G') (a : Type) :
    (hcomp α β).app a = fun x => α.app (G'.obj a) (F.map (β.app a) x) := rfl
@[simp] theorem Endo.id_map {a b : Type} (f : a ⟶ b) : Endo.id.map f = f := rfl
```

第四步：幺半范畴实例。结合子和单位子的分量都是恒等函数 `fun x => x`——这就是“严格”的含义：`(F ∘ G) ∘ H` 和 `F ∘ (G ∘ H)` 在 Lean 里**定义上相等**。最有意思的一条是 `tensor_comp`：它说横向复合与纵向复合可以交换次序，这就是 [1.10 节](/part1/10-natural-transformations)讲过的**交换律**（interchange law），也正是“复合是双函子”的内容。

```lean
instance endoMonoidal : Monoidal Endo where
  tensor := Endo.comp
  tensorHom := hcomp
  tensorUnit := Endo.id
  tensor_id F G := NatTrans.ext' fun a => by
    show (fun x => x) ∘ F.map (𝟙 (G.obj a)) = _
    rw [F.map_id]; rfl
  -- 交换律：(α' ⋅ α) ∘ (β' ⋅ β) = (α' ∘ β') ⋅ (α ∘ β)
  tensor_comp {F₁ F₂ F₃ G₁ G₂ G₃} α α' β β' := NatTrans.ext' fun a => by
    show (α'.app (G₃.obj a) ⊚ α.app (G₃.obj a)) ⊚ F₁.map (β'.app a ⊚ β.app a)
      = (α'.app (G₃.obj a) ⊚ F₂.map (β'.app a)) ⊚ (α.app (G₂.obj a) ⊚ F₁.map (β.app a))
    rw [F₁.map_comp, Category.assoc, Category.assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (α.naturality (β'.app a)).symm
  associator F G H :=
    { hom := { app := fun _ x => x, naturality := fun _ => rfl },
      inv := { app := fun _ x => x, naturality := fun _ => rfl },
      inv_hom := NatTrans.ext' fun _ => rfl, hom_inv := NatTrans.ext' fun _ => rfl }
  leftUnitor F :=
    { hom := { app := fun _ x => x, naturality := fun _ => rfl },
      inv := { app := fun _ x => x, naturality := fun _ => rfl },
      inv_hom := NatTrans.ext' fun _ => rfl, hom_inv := NatTrans.ext' fun _ => rfl }
  rightUnitor F :=
    { hom := { app := fun _ x => x, naturality := fun _ => rfl },
      inv := { app := fun _ x => x, naturality := fun _ => rfl },
      inv_hom := NatTrans.ext' fun _ => rfl, hom_inv := NatTrans.ext' fun _ => rfl }
  associator_natural f g h := NatTrans.ext' fun a => by
    funext x
    simp [Category.comp, hcomp, Endo.comp]
  leftUnitor_natural f := NatTrans.ext' fun a => rfl
  rightUnitor_natural {F G} f := NatTrans.ext' fun a => by
    show _ = f.app a ⊚ F.map (𝟙 a)
    rw [F.map_id]; rfl
  -- 五边形与三角形：所有分量都是恒等函数，化简后两边逐字相同
  pentagon F G H K := NatTrans.ext' fun a => by
    funext x
    simp [Category.comp, hcomp, Endo.comp] <;> rfl
  triangle F G := NatTrans.ext' fun a => by
    funext x
    simp [Category.comp, hcomp, Endo.comp]
    exact congrFun (F.map_id (G.obj a)) x

@[simp] theorem endo_tensorHom {F F' G G' : Endo} (α : F ⟶ F') (β : G ⟶ G') :
    (α ⊗ₘ β) = hcomp α β := rfl
```

第五步：把第一节的 `MonadJ` 接上来。任何满足函子定律的 `T : Type → Type` 都给出一个 `Endo`；任何 `MonadJ T` 都给出 `Endo` 中以 `T` 为载体的幺半群。μ/η 形式的单子定律，**逐条**变成了幺半群定律：

```lean
/-- 满足函子定律的 Lean 函子，看作 Type 上的自函子。 -/
def toEndo (T : Type → Type) [Functor T] [LawfulFunctor T] : Endo where
  obj := T
  map f := Functor.map f
  map_id a := by funext x; exact id_map x
  map_comp f g := by funext x; exact comp_map f g x

/-- 单子（μ/η 形式） ⟹ 自函子范畴中的幺半群。 -/
def MonadJ.toMonoidObj {T : Type → Type} [Functor T] [LawfulFunctor T] (M : MonadJ T) :
    MonoidObj Endo (toEndo T) where
  μ := { app := fun _ => M.join, naturality := fun f => funext fun x => (M.join_natural f x).symm }
  η := { app := fun _ => M.pure, naturality := fun f => funext fun x => (M.pure_natural f x).symm }
  mul_assoc := NatTrans.ext' fun a => funext fun x => by
    simp [Category.comp, Monoidal.associator, Endo.comp, toEndo]
    exact M.join_assoc x                -- 幺半群结合律 = 单子结合律
  unit_left := NatTrans.ext' fun a => funext fun x => M.join_pure x   -- 左单位律
  unit_right := NatTrans.ext' fun a => funext fun x => by
    simp [Category.comp, Endo.comp, toEndo, Monoidal.rightUnitor]
    exact M.join_map_pure x             -- 右单位律

/-- “单子是自函子范畴中的幺半群”——三个机器检查过的例子。 -/
def listMonoid : MonoidObj Endo (toEndo List) := listJ.toMonoidObj
def optionMonoid : MonoidObj Endo (toEndo Option) := optionJ.toMonoidObj
def stateMonoid (σ : Type) : MonoidObj Endo (toEndo (State σ)) := stateJ.toMonoidObj
```

反过来，自函子范畴里的幺半群定律拆到分量上，恰好就是教科书里的单子结合律 $\mu_a \circ \mu_{Ta} = \mu_a \circ T\mu_a$：

```lean
theorem MonoidObj.assoc_app {T : Endo} (M : MonoidObj Endo T) (a : Type) :
    M.μ.app a ⊚ M.μ.app (T.obj a) = M.μ.app a ⊚ T.map (M.μ.app a) := by
  have h := congrArg (fun α => NatTrans.app α a) M.mul_assoc
  simp [Category.comp, Monoidal.associator, Endo.comp] at h
  funext x
  exact congrFun h x
```

::: tip Lean 深入：`abbrev`、`@[simp]` 与 `show`
- `abbrev Endo := CFunctor Type Type` 是一个**可约**的别名：Lean 在找实例、做合一时会自动展开它。
- 给引理加上 `@[simp]`，`simp` 就会自动用它化简。上面那些 `…_app` 引理告诉 `simp`“纵向复合/横向复合在分量上长什么样”。
- `show t` 把当前目标换成一个**定义上相等**的写法 `t`，便于后面的 `rw` 找到要改写的模式。
:::

## 由伴随得到单子

[伴随](/part3/02-adjunctions) $L \dashv R$ 是在两个范畴 $\mathcal{C}$ 和 $\mathcal{D}$ 之间来回走的一对函子。把它们复合有两种方式，得到两个自函子：$R \circ L$ 和 $L \circ R$。按照伴随的定义，这两个自函子通过两个叫做单位和余单位的自然变换与恒等函子联系起来：

$$
\begin{gathered}
\eta :: I_{\mathcal{D}} \to R \circ L \\
\varepsilon :: L \circ R \to I_{\mathcal{C}}
\end{gathered}
$$

一眼就能看出，伴随的单位长得和单子的单位一模一样。事实证明，自函子 $R \circ L$ 确实是一个单子。我们只需要定义一个与 $\eta$ 搭配的 $\mu$。它是从我们这个自函子的平方到它自身的自然变换，用伴随函子写出来就是：

$$R \circ L \circ R \circ L \to R \circ L$$

而我们确实可以用余单位把中间那个 $L \circ R$ 压掉。$\mu$ 的精确公式由横向复合给出：

$$\mu = R \circ \varepsilon \circ L$$

单子定律可以由伴随的单位与余单位所满足的恒等式（三角恒等式），再加上交换律推出来。

```diagram
RLRL: (0, 0) "R \circ L \circ R \circ L"
RL: (3.2, 0) "R \circ L"
I: (1.6, 1.4) "R \circ I_{\mathcal{C}} \circ L"
mu: RLRL -> RL "\mu = R \circ \varepsilon \circ L"
e: RLRL -> I "R \circ \varepsilon \circ L" side=right dashed color=gray
eq: I -> RL "=" side=right dashed color=gray
caption: 用余单位 ε 压掉中间的 L∘R，就得到单子的乘法 μ。
```

在编程中，我们见到的由伴随导出的单子并不多，因为伴随通常涉及两个范畴。不过，指数对象（函数对象）的定义是个例外。构成这个伴随的两个自函子是：

$$
\begin{gathered}
L\, z = z \times s \\
R\, b = s \Rightarrow b
\end{gathered}
$$

你也许认出了它们的复合正是我们熟悉的 State 单子：

$$R (L\, z) = s \Rightarrow (z \times s)$$

前面我们已经在 Lean 里定义过它：

```lean no-check
structure State (σ α : Type) where
  run : σ → α × σ
```

我们也把这个伴随翻译成 Lean。左函子是积函子：

```lean
/-- L z = z × s。Lean 中用一个结构体包起来，方便给它单独的 Functor 实例。 -/
structure ProdF (s a : Type) where
  val : a
  st : s

instance : Functor (ProdF s) where
  map f p := ⟨f p.val, p.st⟩
```

右函子是 reader 函子：

```lean
/-- R b = s → b。 -/
structure Reader (s a : Type) where
  run : s → a

instance : Functor (Reader s) where
  map f r := ⟨f ∘ r.run⟩
```

它们构成伴随：

```lean
/-- 伴随的单位：a → R (L a) -/
def unitPR (a : α) : Reader s (ProdF s α) := ⟨fun s => ⟨a, s⟩⟩

/-- 伴随的余单位：L (R a) → a，也就是“拿状态去调用函数” -/
def counitPR (p : ProdF s (Reader s a)) : a := p.val.run p.st

-- 两条三角恒等式（ε_L ∘ Lη = id，Rε ∘ η_R = id），都是 rfl
theorem triangle_left (p : ProdF s a) : counitPR (unitPR <$> p) = p := rfl
theorem triangle_right (r : Reader s a) : counitPR <$> unitPR r = r := rfl
```

你可以轻松说服自己：reader 函子跟在积函子之后的复合，确实等价于 state 函子。在 Lean 里，“说服自己”就是写出两个方向的转换，并证明它们互逆：

```lean
def State.toRL (m : State σ α) : Reader σ (ProdF σ α) := ⟨fun s => ⟨(m.run s).1, (m.run s).2⟩⟩
def State.ofRL (r : Reader σ (ProdF σ α)) : State σ α := ⟨fun s => ((r.run s).val, (r.run s).st)⟩

theorem State.of_to (m : State σ α) : State.ofRL m.toRL = m := rfl
theorem State.to_of (r : Reader σ (ProdF σ α)) : (State.ofRL r).toRL = r := rfl
```

不出所料，伴随的 `unit` 等价于 State 单子的 `pure`。`counit` 的作用是把一个函数作用在它的参数上，这可以认出是 `runState` 的非柯里化版本（非柯里化，是因为 `counit` 作用在一个二元组上）：

```lean
def State.runState (m : State σ α) (s : σ) : α × σ := m.run s

theorem unit_is_pure (a : α) : State.ofRL (unitPR (s := σ) a) = stateJ.pure a := rfl
-- 把 State 看成 Reader（函数 s → α × s），余单位就是“非柯里化的 runState”
theorem counit_is_uncurried_runState (m : State σ α) (s : σ) :
    counitPR (⟨⟨m.runState⟩, s⟩ : ProdF σ (Reader σ (α × σ))) = Function.uncurry State.runState (m, s) := rfl
```

现在可以把 State 单子的 `join` 定义为自然变换 $\mu$ 的分量。为此需要三个自然变换的横向复合：

$$\mu = R \circ \varepsilon \circ L$$

换句话说，要把余单位 $\varepsilon$ “偷运”过一层 reader 函子。在 Haskell 里不能直接调用 `fmap`，因为编译器会选中 `State` 函子的 `fmap`，而不是 `Reader` 函子的；Lean 里我们的 `State` 是独立的结构体，情况一样。好在 reader 函子的 `fmap` 不过是“在左边复合一个函数”（后复合），所以我们直接用函数复合。

首先要剥掉 `State` 构造子，露出 `State` 函子里面的函数。这一步用 `run`（即 `runState`）完成：

```lean no-check
ssa : State s (State s a)
ssa.run : s → State s a × s
```

然后在左边复合上余单位——它由 `Function.uncurry State.runState` 定义。最后再给它穿回 `State` 构造子：

```lean
def State.join (ssa : State σ (State σ α)) : State σ α :=
  ⟨Function.uncurry State.runState ∘ ssa.run⟩

-- 这正是我们在第一节手写的 State 单子的 join
theorem State.join_eq (ssa : State σ (State σ α)) : State.join ssa = stateJ.join ssa := rfl
```

这确实就是 `State` 单子的 `join` 实现。

事实证明，不仅每个伴随都会产生一个单子，反过来也成立：每个单子都可以分解为两个伴随函子的复合。不过这种分解并不唯一（我们会在 [3.9 单子的代数](/part3/09-algebras-for-monads)中看到两种极端的分解：Kleisli 范畴和 Eilenberg–Moore 范畴）。

另一个自函子 $L \circ R$，我们下一节（[3.7 余单子](/part3/07-comonads)）再谈。

## 补充练习

原书本章没有挑战题。这里给出几道用 Lean 巩固本章内容的练习。

1. 为 `Except ε` 定义 `MonadJ` 实例，并证明全部定律。
2. 定义一个以 `List String` 为日志的 Writer 函子 `structure Writer (α : Type) where val : α; log : List String`，为它定义 `MonadJ` 实例。注意 `join` 里需要把两层日志拼起来——单子的乘法用到了日志这个幺半群的乘法。
3. 为本章开头的表达式树 `Expr` 定义 `Functor` 和 `MonadJ` 实例（`join` 就是“用 `id` 做代入”），并证明定律。这样一来，“代入就是 bind”这句话就有了严格的含义。
4. 在 (**Type**, ×, Unit) 中，`MonoidObj Type m` 与“带定律的 `MonoidC m`”是一回事。证明：从 `M : MonoidObj Type m` 可以读出满足结合律的乘法 `fun x y => M.μ (x, y)`。

::: details 参考答案
**1. Except**

```lean
def exceptJ : MonadJ (Except ε) where
  pure := .ok
  join x := match x with
    | .ok (.ok a) => .ok a
    | .ok (.error e) => .error e
    | .error e => .error e
  pure_natural _ _ := rfl
  join_natural f x := by rcases x with e | (e | a) <;> rfl
  join_assoc x := by rcases x with e | (e | (e | a)) <;> rfl
  join_pure x := by cases x <;> rfl
  join_map_pure x := by cases x <;> rfl
```

**2. Writer**

```lean
structure Writer (α : Type) where
  val : α
  log : List String

instance : Functor Writer where
  map f w := ⟨f w.val, w.log⟩

def writerJ : MonadJ Writer where
  pure a := ⟨a, []⟩
  join w := ⟨w.val.val, w.log ++ w.val.log⟩   -- 外层日志在前，内层日志在后
  pure_natural _ _ := rfl
  join_natural _ _ := rfl
  join_assoc w := by
    show (⟨w.val.val.val, (w.log ++ w.val.log) ++ w.val.val.log⟩ : Writer _)
       = ⟨w.val.val.val, w.log ++ (w.val.log ++ w.val.val.log)⟩
    simp [List.append_assoc]                  -- 日志拼接的结合律
  join_pure w := by
    show (⟨w.val, [] ++ w.log⟩ : Writer _) = w
    simp                                      -- [] ++ l = l
  join_map_pure w := by
    show (⟨w.val, w.log ++ []⟩ : Writer _) = w
    simp                                      -- l ++ [] = l
```

**3. Expr**

```lean
def Expr.map (f : α → β) : Expr α → Expr β
  | var x => var (f x)
  | lit n => lit n
  | add a b => add (a.map f) (b.map f)
  | mul a b => mul (a.map f) (b.map f)

instance : Functor Expr where
  map := Expr.map

def exprJ : MonadJ Expr where
  pure := .var
  join e := e.subst id
  pure_natural _ _ := rfl
  join_natural f x := by
    induction x with
    | var e => rfl
    | lit n => rfl
    | add a b iha ihb => exact congr (congrArg Expr.add iha) ihb
    | mul a b iha ihb => exact congr (congrArg Expr.mul iha) ihb
  join_assoc x := by
    induction x with
    | var e => rfl
    | lit n => rfl
    | add a b iha ihb => show Expr.add _ _ = Expr.add _ _; exact congr (congrArg Expr.add iha) ihb
    | mul a b iha ihb => show Expr.mul _ _ = Expr.mul _ _; exact congr (congrArg Expr.mul iha) ihb
  join_pure _ := rfl
  join_map_pure x := by
    induction x with
    | var e => rfl
    | lit n => rfl
    | add a b iha ihb => exact congr (congrArg Expr.add iha) ihb
    | mul a b iha ihb => exact congr (congrArg Expr.mul iha) ihb

-- 代入 = 先 map 再 join，正如 bind = join ∘ map
theorem Expr.subst_eq (e : Expr α) (σ : α → Expr β) : e.subst σ = exprJ.join (σ <$> e) := by
  induction e with
  | var x => rfl
  | lit n => rfl
  | add a b iha ihb => exact congr (congrArg Expr.add iha) ihb
  | mul a b iha ihb => exact congr (congrArg Expr.mul iha) ihb
```

**4. 从 MonoidObj 读出结合律**

```lean
theorem MonoidObj.mul_assoc_pointwise {m : Type} (M : MonoidObj Type m) (x y z : m) :
    M.μ (M.μ (x, y), z) = M.μ (x, M.μ (y, z)) :=
  congrFun M.mul_assoc ((x, y), z)
```

`congrFun h a` 把函数等式 `h : f = g` 变成在点 `a` 处的等式 `f a = g a`。等式两边展开后正是逐点的结合律。
:::

## 本章小结

- 从代数的角度看，自函子 $T$ 是“装变量的表达式容器”，代入的签名 $m\,a \to (a \to m\,b) \to m\,b$ 正是 bind。
- 范畴论中，**单子**是自函子 $T$ 加两个自然变换：乘法 $\mu : T\circ T \to T$（`join`）和单位 $\eta : I \to T$（`pure`）。
- 单子定律：**结合律** $\mu \circ (T\circ\mu) = \mu \circ (\mu\circ T)$（先压内层还是外层都一样），**单位律** $\mu \circ (\eta\circ T) = \mathrm{id} = \mu \circ (T\circ\eta)$。这些定律恰好保证 Kleisli 箭头构成范畴——我们在 Lean 中证明了这一点。
- 幺半群可以无点地表述为 $\mu : m\times m \to m$、$\eta : 1 \to m$；但积只在同构意义下结合、有单位，所以需要结合子 $\alpha$、单位子 $\lambda$、$\rho$。
- 把积推广为任意张量积 $\otimes$、把终对象推广为单位对象 $i$，就得到**幺半范畴**；五边形与三角形恒等式保证“怎么换括号都一样”（Mac Lane 相容性定理）。
- **幺半范畴中的幺半群**：对象 $m$ 加 $\mu : m\otimes m\to m$、$\eta : i\to m$，满足结合律与单位律的交换图。
- 自函子范畴 $[\mathcal{C},\mathcal{C}]$ 以**函子复合**为张量积、恒等函子为单位，是一个严格幺半范畴；其中的幺半群正是单子。这就是“单子不过是自函子范畴中的幺半群”，我们在 Lean 中让它通过了类型检查。
- 每个伴随 $L\dashv R$ 都给出单子 $R\circ L$，乘法为 $\mu = R\circ\varepsilon\circ L$。积–指数伴随给出的就是 State 单子，它的 `join` 可以由余单位直接推出。
