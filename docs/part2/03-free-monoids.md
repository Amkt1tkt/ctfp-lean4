# 2.3 自由幺半群

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

end CTFP

open CTFP
```

幺半群无论在范畴论还是在编程里都是一个重要概念。范畴对应于强类型语言，幺半群则对应于无类型语言。这是因为在幺半群里，任意两个箭头都可以复合，就像在无类型语言里任意两个函数都可以复合一样（当然，程序运行起来时你可能会碰上运行时错误）。

我们已经看到，幺半群可以描述成只有一个对象的范畴，所有的逻辑都编码在态射的复合规则里。这个范畴论模型与更传统的、集合论式的幺半群定义完全等价：在集合论的定义里，我们把集合中的两个元素“相乘”，得到第三个元素。这个“乘法”过程还可以进一步拆成两步：先把两个元素配成一对，再把这一对和某个已有的元素——它们的“积”——等同起来。

::: info 数学小课堂：幺半群三句话
一个**幺半群**（monoid）就是：

1. 一个集合 $M$；
2. 一个二元运算 $\cdot : M \times M \to M$（“乘法”，但不一定是数的乘法），满足**结合律**：$(x \cdot y) \cdot z = x \cdot (y \cdot z)$；
3. 一个特殊元素 $e$（**单位元**），满足 $e \cdot x = x = x \cdot e$。

例子：$(\mathbb{N}, +, 0)$、$(\mathbb{N}, \times, 1)$、（字符串，拼接，空串）、（布尔值，与，真）。注意，**不要求交换律**：字符串拼接里 `"ab" ++ "c"` 和 `"c" ++ "ab"` 不一样。

“乘法 = 配对 + 等同”这句话可以这样体会：在 $(\mathbb{N}, \times)$ 里，$2 \times 3$ 首先是一个“对” $(2, 3)$，然后我们宣布这个对“就是” $6$。$(1, 6)$、$(6, 1)$、$(3, 2)$ 也被宣布“就是” $6$——很多不同的对被**等同**到了同一个元素上。
:::

如果我们放弃乘法的第二步——不再把对子和已有的元素等同起来——会发生什么？比如，我们可以从一个任意的集合出发，构造出所有可能的元素对，并把它们叫作新元素。然后再把这些新元素和所有可能的元素配对，如此往复。这是一个连锁反应——我们会永远不停地添加新元素。结果得到一个无限集合，它**几乎**就是一个幺半群了。但幺半群还需要一个单位元和结合律。没问题：我们可以加进一个特殊的单位元，再把一部分对子等同起来——刚好够支撑单位律和结合律就行。

我们用一个简单的例子来看看它是怎么运作的。从一个两元素集合 $\{a, b\}$ 出发。我们把它们叫作自由幺半群的**生成元**（generators）。首先，我们加进一个特殊元素 $e$ 充当单位元。接着，我们加进所有元素对，并把它们叫作“积”。$a$ 和 $b$ 的积是对子 $(a, b)$；$b$ 和 $a$ 的积是对子 $(b, a)$；$a$ 和 $a$ 的积是 $(a, a)$；$b$ 和 $b$ 的积是 $(b, b)$。我们也可以和 $e$ 配对，比如 $(a, e)$、$(e, b)$ 等，但我们会把它们分别等同于 $a$、$b$ 等。所以这一轮我们只加进 $(a, a)$、$(a, b)$、$(b, a)$ 和 $(b, b)$，最后得到集合 $\{e, a, b, (a, a), (a, b), (b, a), (b, b)\}$。

![一群举着牌子的兔子：ab、a、ba、b，还有举着 e 的大象](/img/2.3/bunnies.jpg "自由幺半群的元素：生成元 a、b，它们的各种积 ab、ba……，以及单位元 e。")

下一轮，我们会继续加进像 $(a, (a, b))$、$((a, b), a)$ 这样的元素。这时就得保证结合律成立了，所以我们会把 $(a, (b, a))$ 和 $((a, b), a)$ 等同起来，以此类推。换句话说，我们不再需要内层的括号。

你能猜到这个过程的最终结果：我们会得到由 $a$ 和 $b$ 组成的所有可能的列表。实际上，如果把 $e$ 表示成空列表，就能看出我们的“乘法”不过就是列表拼接。

这种不断生成元素的所有可能组合、并且只做最少的等同（刚好足以维持定律）的构造，叫作**自由构造**（free construction）。我们刚才做的，就是由生成元集合 $\{a, b\}$ 构造出一个**自由幺半群**（free monoid）。

::: info 数学小课堂：“等同”到底是什么操作
“把 $(a, e)$ 等同于 $a$”的意思是：从今以后我们宣布这两个东西**是同一个元素**。数学上这叫**取商**：先定义一个关系 $\sim$（“哪些东西要被看成一样”），然后把互相关联的东西捆成一个“等价类”，每个等价类当作一个新元素。

自由幺半群就是**只**捆了定律强迫我们捆的东西：

- 单位律强迫 $(a, e) \sim a$、$(e, a) \sim a$；
- 结合律强迫 $((x, y), z) \sim (x, (y, z))$。

除此之外一概不捆。于是 $(a, b)$ 和 $(b, a)$ **不会**被等同——没有任何定律要求 $ab = ba$。这就是“自由”的含义：除了定律，没有任何额外的方程。

把括号全部去掉、把 $e$ 全部删掉后，剩下的恰好就是一个**字母序列**——列表。
:::

## Lean 中的自由幺半群

两元素集合在 Lean 中等价于类型 `Bool`，而由这个集合生成的自由幺半群就等价于类型 `List Bool`（`Bool` 的列表）。原书在这里特意说明“故意忽略无限列表带来的问题”——Haskell 的列表可以是无限的。Lean 不需要这个免责声明：Lean 的 `List` 是一个**归纳类型**，每个列表都是用有限次 `cons` 搭出来的，天然就是有限的。

在 Haskell 中，幺半群由一个类型类定义，它只要求有一个单位元 `mempty` 和一个二元函数（乘法）`mappend`；而单位律和结合律在 Haskell 里**无法表达**，每次实现一个幺半群实例时都只能靠程序员自己去验证。

Lean 的类型类则可以直接把定律写成字段：

```lean
namespace CTFP

/-- 幺半群：单位元 + 二元运算 + 三条定律。定律是类型类的字段，实例必须给出证明。 -/
class Monoid (m : Type) where
  mempty : m
  mappend : m → m → m
  mempty_mappend : ∀ x : m, mappend mempty x = x
  mappend_mempty : ∀ x : m, mappend x mempty = x
  mappend_assoc : ∀ x y z : m, mappend (mappend x y) z = mappend x (mappend y z)

/-- 中缀记号：x ⋄ y 表示 mappend x y（输入 \diamond）。 -/
infixr:65 " ⋄ " => Monoid.mappend

end CTFP

open CTFP.Monoid
```

::: tip Lean 深入：把定律放进类型类
`mempty_mappend : ∀ x : m, mappend mempty x = x` 这个字段的类型是一个**命题**。要创建 `Monoid` 的实例，你不仅要给出 `mempty` 和 `mappend` 的实现，还要给出这三个命题的**证明**——否则实例根本编译不过。

这正是 Lean 比 Haskell（以及 Rust）强的地方：Rust 的 trait 也只能写方法签名，`impl Add for MyType` 时编译器不会检查你的加法是否满足结合律。在 Lean 里，“满足幺半群定律”是类型检查的一部分。

这里把 `Monoid` 放进 `CTFP` 命名空间：Lean 核心库没有 `Monoid`，但 Mathlib 有，放在命名空间中可以避免将来冲突。`open CTFP.Monoid` 之后，可以直接写 `mempty`、`mappend_assoc` 等名字。
:::

“任何类型的列表都构成幺半群”这一事实，由下面这个实例描述：

```lean
instance (α : Type) : CTFP.Monoid (List α) where
  mempty := []
  mappend := (· ++ ·)
  -- 三条定律在核心库中都已证明，直接引用即可
  mempty_mappend := List.nil_append
  mappend_mempty := List.append_nil
  mappend_assoc := List.append_assoc
```

它声明：空列表 `[]` 是单位元，列表拼接 `(++)` 是二元运算。

如我们所见，元素类型为 `α` 的列表对应于以集合 `α` 为生成元的自由幺半群。而带乘法的自然数集**不是**自由幺半群，因为我们把很多积等同起来了。

在 Lean 中要说“带乘法的自然数”，还得先解决一个小问题：自然数上至少有两种幺半群结构——加法（单位元 0）和乘法（单位元 1）。而类型类实例对每个类型应该是唯一的。标准的解决办法是用**新类型**（newtype）包一层：

```lean
/-- 自然数的加法幺半群 (ℕ, +, 0)。 -/
structure AddN where
  val : Nat
  deriving Repr, DecidableEq

/-- 自然数的乘法幺半群 (ℕ, ×, 1)。 -/
structure MulN where
  val : Nat
  deriving Repr, DecidableEq

instance : CTFP.Monoid AddN where
  mempty := ⟨0⟩
  mappend x y := ⟨x.val + y.val⟩
  mempty_mappend x := by cases x; simp
  mappend_mempty x := by cases x; simp
  mappend_assoc x y z := by simp [Nat.add_assoc]

instance : CTFP.Monoid MulN where
  mempty := ⟨1⟩
  mappend x y := ⟨x.val * y.val⟩
  mempty_mappend x := by cases x; simp
  mappend_mempty x := by cases x; simp
  mappend_assoc x y z := by simp [Nat.mul_assoc]
```

::: tip Rust 视角：newtype 模式
这和 Rust 里的做法一模一样：标准库中 `std::num::Wrapping<T>`、`std::cmp::Reverse<T>` 都是“给同一个底层类型换一套 trait 实现”的 newtype。想让 `u32` 既能按加法、又能按乘法折叠，就写 `struct Sum(u32);` 和 `struct Product(u32);`，各自 `impl` 一遍。`deriving Repr, DecidableEq` 相当于 Rust 的 `#[derive(Debug, PartialEq, Eq)]`。
:::

现在比较一下：

```lean
example : (⟨2⟩ : MulN) ⋄ ⟨3⟩ = ⟨6⟩ := rfl          -- 2 * 3 = 6
example : ([2] : List Nat) ⋄ [3] = [2, 3] := rfl    -- [2] ++ [3] = [2, 3]
example : ([2] ⋄ [3] : List Nat) ≠ [6] := by decide  -- 和 [6] 不一样
```

::: tip Lean 深入：`decide`
`decide` 适用于**可判定**的命题：Lean 知道如何用计算来判断它真假（这里是比较两个具体的列表）。它直接运行判定过程，若结果为真就完成证明。`≠` 读作“不等于”，`a ≠ b` 就是 `a = b → False`。
:::

这很简单。但问题是：我们能在范畴论里完成这个自由构造吗？在范畴论里，我们不允许看对象的内部。我们要用我们的老黄牛：泛构造。

第二个有趣的问题是：能不能从某个自由幺半群出发，通过等同比定律所要求的最少数目更多的元素，得到**任何**幺半群？我会告诉你，这一点可以直接从泛构造推出来。

## 自由幺半群的泛构造

如果你还记得我们以前和泛构造打交道的经历，你可能会注意到：它与其说是“构造”某样东西，不如说是**挑选**一个最符合给定模式的对象。所以，如果想用泛构造来“构造”自由幺半群，我们就得考察一大堆幺半群，从中挑出一个。我们需要一整个幺半群范畴来供我们挑选。可是，幺半群构成一个范畴吗？

我们先把幺半群看成配备了额外结构（由单位元和乘法定义）的集合。我们选取那些保持幺半群结构的函数作为态射。这种保持结构的函数叫作**同态**（homomorphism）。幺半群同态必须把两个元素的积映到这两个元素的像的积：

$$h(a \cdot b) = h(a) \cdot h(b)$$

并且必须把单位元映到单位元。

```lean
/-- 幺半群同态：保持单位元、保持乘法的函数。 -/
structure MonoidHom (m n : Type) [CTFP.Monoid m] [CTFP.Monoid n] where
  toFun : m → n
  map_mempty : toFun mempty = mempty
  map_mappend : ∀ x y : m, toFun (x ⋄ y) = toFun x ⋄ toFun y
```

::: tip Lean 深入：`structure` 里的证明字段
和 `Monoid` 一样，`MonoidHom` 把一个函数 `toFun` 和两条关于它的证明打包在一起。一个 `MonoidHom m n` 类型的值，就是“一个**已被证明**保持结构的函数”。方括号 `[CTFP.Monoid m]` 是**实例隐式参数**：Lean 会自动去找 `m` 的 `Monoid` 实例，相当于 Rust 的 `where M: Monoid` 约束。
:::

举个例子：考虑一个从整数列表到整数的同态。如果我们把 `[2]` 映到 2、把 `[3]` 映到 3，那就必须把 `[2, 3]` 映到 6，因为拼接

$$[2] \mathbin{+\!\!+} [3] = [2, 3]$$

变成了乘法

$$2 \times 3 = 6$$

这个同态就是“把列表里的数全部乘起来”。我们用 Lean 定义它，并**证明**它确实是一个同态（这里用 `Nat` 演示）：

```lean
/-- 把列表中的数全部乘起来。 -/
def prodList : List Nat → MulN
  | [] => ⟨1⟩
  | x :: xs => ⟨x * (prodList xs).val⟩

/-- 关键引理：拼接变乘法。对 xs 做归纳。 -/
theorem prodList_append (xs ys : List Nat) :
    prodList (xs ++ ys) = prodList xs ⋄ prodList ys := by
  induction xs with
  | nil => exact (mempty_mappend _).symm         -- [] ++ ys = ys，而 1 * p = p
  | cons x xs ih =>
    -- (x :: xs) ++ ys 的积 = x * (xs ++ ys 的积)，用归纳假设 ih 改写，再用结合律
    show (⟨x * (prodList (xs ++ ys)).val⟩ : MulN) = ⟨x * (prodList xs).val * (prodList ys).val⟩
    rw [ih, Nat.mul_assoc]
    rfl

def prodHom : MonoidHom (List Nat) MulN where
  toFun := prodList
  map_mempty := rfl
  map_mappend := prodList_append

example : prodHom.toFun [2, 3] = ⟨6⟩ := rfl
```

::: info 数学小课堂：数学归纳法与 `induction`
要证明“对所有列表 `xs`，某性质成立”，**归纳法**说只需证两件事：

1. **基础情形**：对空列表 `[]` 成立；
2. **归纳步骤**：假设对 `xs` 成立（这叫**归纳假设**，上面记作 `ih`），证明对 `x :: xs` 也成立。

为什么够了？因为每个列表都是从 `[]` 出发、有限次 `cons` 搭出来的：性质沿着搭建过程一步步传递下去，就像推倒多米诺骨牌。Lean 的 `induction xs with | nil => … | cons x xs ih => …` 正是这两件事的书面形式。它和递归函数是一体两面：`prodList` 用递归**定义**，`prodList_append` 就用归纳**证明**。
:::

现在，让我们忘掉单个幺半群的内部结构，只把它们看成对象以及相应的态射。你就得到了一个幺半群范畴 $\mathbf{Mon}$。

原书说“幺半群构成一个范畴”而没有细究；在 Lean 里，我们要给出恒等同态和同态的复合，并验证范畴定律：

```lean
/-- 两个同态只要底层函数相同就相同（证明字段由证明无关性自动相同）。 -/
theorem MonoidHom.ext' {m n : Type} [CTFP.Monoid m] [CTFP.Monoid n] {f g : MonoidHom m n}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

def MonoidHom.id (m : Type) [CTFP.Monoid m] : MonoidHom m m :=
  ⟨fun x => x, rfl, fun _ _ => rfl⟩

/-- 同态的复合还是同态。 -/
def MonoidHom.comp {m n k : Type} [CTFP.Monoid m] [CTFP.Monoid n] [CTFP.Monoid k]
    (g : MonoidHom n k) (f : MonoidHom m n) : MonoidHom m k where
  toFun := g.toFun ∘ f.toFun
  map_mempty := by simp [Function.comp, f.map_mempty, g.map_mempty]
  map_mappend x y := by simp [Function.comp, f.map_mappend, g.map_mappend]

/-- 范畴 Mon 的对象：一个类型连同它的幺半群结构。 -/
structure Mon where
  carrier : Type
  [inst : CTFP.Monoid carrier]

attribute [instance] Mon.inst

instance : Category Mon where
  Hom m n := MonoidHom m.carrier n.carrier
  id m := MonoidHom.id m.carrier
  comp g f := MonoidHom.comp g f
  id_comp _ := MonoidHom.ext' rfl
  comp_id _ := MonoidHom.ext' rfl
  assoc _ _ _ := MonoidHom.ext' rfl
```

::: tip Lean 深入：把结构“打包”成对象
`Mon` 的每个元素都是一个“类型 + 实例”的包。`[inst : CTFP.Monoid carrier]` 把实例当作结构的一个字段存起来；`attribute [instance] Mon.inst` 则告诉 Lean：遇到 `M.carrier` 时，可以从 `M.inst` 里找到它的幺半群实例。这类似于 Rust 的 `Box<dyn Monoid>`——把“类型 + 它的 trait 实现”捆在一起当作一个值传递。注意 `Mon : Type 1`，因为它的元素包含一个 `Type`。
:::

好，也许在忘掉内部结构之前，我们先注意一个重要的性质。$\mathbf{Mon}$ 的每个对象都可以平凡地映到一个集合——就是它的元素组成的集合。这个集合叫作**底层集合**（underlying set）。事实上，我们不仅能把 $\mathbf{Mon}$ 的对象映到集合，还能把 $\mathbf{Mon}$ 的态射（同态）映到函数。同样，这看起来有点平凡，但它很快就会派上用场。这个从 $\mathbf{Mon}$ 到 $\mathbf{Set}$ 的对象与态射的映射，实际上是一个函子。由于这个函子“遗忘”了幺半群结构——一旦进入一个普通的集合，我们就不再区分单位元，也不再关心乘法——它被称为**遗忘函子**（forgetful functor）。遗忘函子在范畴论中经常出现。

```lean
/-- 遗忘函子 U : Mon → Type。函子定律都是 rfl：遗忘什么也不用做。 -/
def forget : CFunctor Mon Type where
  obj m := m.carrier
  map h := h.toFun
  map_id _ := rfl
  map_comp _ _ := rfl
```

现在我们对 $\mathbf{Mon}$ 有了两种不同的看法。我们可以把它当作和其他范畴一样的、由对象和态射构成的范畴。在这种看法下，我们看不到幺半群的内部结构。关于 $\mathbf{Mon}$ 中某个特定对象，我们能说的只是：它通过态射与自己以及其他对象相连。态射的“乘法表”——复合规则——是从另一种看法推导出来的：把幺半群看成集合。转到范畴论之后，我们并没有完全失去这种看法——仍然可以通过遗忘函子访问它。

要应用泛构造，我们需要定义一个特殊性质，让我们能在幺半群范畴中搜索，并挑出自由幺半群的最佳候选者。但自由幺半群是由它的生成元定义的。不同的生成元选择会产生不同的自由幺半群（`List Bool` 和 `List Int` 不一样）。我们的构造必须从一个生成元集合出发。于是我们又回到了集合！

这就是遗忘函子登场的地方。我们可以用它给幺半群拍 X 光片，在这些“团块”的 X 光片里辨认出生成元。具体做法如下：

我们从一个生成元集合 $x$ 出发。这是 $\mathbf{Set}$ 中的一个集合。

我们要匹配的模式由一个幺半群 $m$（$\mathbf{Mon}$ 的一个对象）和 $\mathbf{Set}$ 中的一个函数 $p$ 组成：

$$p : x \to U\,m$$

其中 $U$ 是我们从 $\mathbf{Mon}$ 到 $\mathbf{Set}$ 的遗忘函子。这是一个奇怪的异质模式——一半在 $\mathbf{Mon}$ 里，一半在 $\mathbf{Set}$ 里。

这里的想法是：函数 $p$ 会在 $m$ 的 X 光片里辨认出生成元集合。函数在辨认集合中的点这件事上可能很差劲（它们可能把点压到一起），这没关系，泛构造会把一切理顺，挑出这个模式的最佳代表。

![幺半群的模式：生成元 x 经 p 进入 m 的底层集合](/img/2.3/monoid-pattern.jpg "模式：Set 中的生成元集合 x，经函数 p 映入幺半群 m 的 X 光片 U m。")

我们还得定义候选者之间的排名。假设有另一个候选者：一个幺半群 $n$，以及一个在它的 X 光片里辨认生成元的函数：

$$q : x \to U\,n$$

如果存在一个幺半群态射（也就是保持结构的同态）

$$h : m \to n$$

使得它在 $U$ 下的像（记住，$U$ 是函子，所以它把态射映到函数）经由 $p$ 分解：

$$q = U\,h \circ p$$

我们就说 $m$ 比 $n$ 好。如果把 $p$ 看作在 $m$ 中选出生成元，把 $q$ 看作在 $n$ 中选出“同样的”生成元，那么就可以把 $h$ 看作在两个幺半群之间映射这些生成元。记住，$h$ 按定义保持幺半群结构。这意味着，一个幺半群中两个生成元的积，会被映到第二个幺半群中对应的两个生成元的积，以此类推。

![幺半群候选者的排名](/img/2.3/monoid-ranking.jpg "排名：若存在同态 h : m → n 使 q = U h ∘ p，则 m 比 n 好。")

```diagram
x: (0, 0) "x"
Um: (2, 0) "U\,m"
Un: (2, 1.5) "U\,n"
p: x -> Um "p"
q: x -> Un "q" side=right
Uh: Um -> Un "U\,h" dashed
path "q": q
path "U h ∘ p": p Uh color=green
caption: 在 Set 中看排名：q = U h ∘ p。（h 本身是 Mon 中的态射，U h 是它的 X 光片。）
```

这个排名可以用来找出最佳候选者——自由幺半群。定义如下：

> 我们说 $m$（连同函数 $p$）是以 $x$ 为生成元的**自由幺半群**，当且仅当：对于任何别的幺半群 $n$（连同函数 $q$），都存在**唯一**一个从 $m$ 到 $n$ 的态射 $h$，满足上面的分解性质。

在 Lean 里，这个定义可以逐字写成一个结构：`lift` 给出 $h$（存在性），`fac` 说它满足分解性质，`uniq` 说它是唯一的：

```lean
/-- (m, p) 是以 α 为生成元的自由幺半群。 -/
structure IsFreeMonoid (α : Type) (m : Type) [CTFP.Monoid m] (p : α → m) where
  lift : ∀ {n : Type} [CTFP.Monoid n], (α → n) → MonoidHom m n
  fac : ∀ {n : Type} [CTFP.Monoid n] (q : α → n), (lift q).toFun ∘ p = q
  uniq : ∀ {n : Type} [CTFP.Monoid n] (q : α → n) (h : MonoidHom m n),
    h.toFun ∘ p = q → h = lift q
```

### 补充：证明 `List α` 是自由幺半群

原书到这里就停下了，没有验证 `List α` 真的满足这个定义。我们来补上——这是本章的核心定理。

生成元的嵌入 $p$ 是“把一个字母变成单字母的词”：`fun x => [x]`。给定任意幺半群 `n` 和任意函数 `f : α → n`，同态 $h$ 必须这样定义：把词里的每个字母用 `f` 翻译过去，然后用 `n` 的乘法乘起来。这个操作通常叫作 `foldMap`：

```lean
section Free
variable {α m : Type} [CTFP.Monoid m]

/-- 用 f 翻译每个字母，再用 m 的乘法乘起来：foldMap f [x₁, x₂, …] = f x₁ ⋄ f x₂ ⋄ … ⋄ mempty。 -/
def foldMap (f : α → m) : List α → m
  | [] => mempty
  | x :: xs => f x ⋄ foldMap f xs

/-- foldMap 把拼接变成乘法 —— 这正是“同态”的条件。归纳证明。 -/
theorem foldMap_append (f : α → m) (xs ys : List α) :
    foldMap f (xs ++ ys) = foldMap f xs ⋄ foldMap f ys := by
  induction xs with
  | nil => exact (mempty_mappend _).symm
  | cons x xs ih =>
    show f x ⋄ foldMap f (xs ++ ys) = (f x ⋄ foldMap f xs) ⋄ foldMap f ys
    rw [ih, mappend_assoc]

/-- 存在性：foldMap f 是一个幺半群同态。 -/
def lift (f : α → m) : MonoidHom (List α) m where
  toFun := foldMap f
  map_mempty := rfl
  map_mappend := foldMap_append f

/-- 生成元的嵌入 p : α → List α。 -/
def gens : α → List α := fun x => [x]

/-- 分解性质：U h ∘ p = f，即 lift f 在单字母词上就是 f。 -/
theorem lift_gens (f : α → m) : (lift f).toFun ∘ gens = f := by
  funext x
  exact mappend_mempty (f x)     -- foldMap f [x] = f x ⋄ mempty = f x

/-- 唯一性：任何在生成元上与 f 一致的同态 h 都等于 lift f。 -/
theorem lift_unique (f : α → m) (h : MonoidHom (List α) m)
    (hf : h.toFun ∘ gens = f) : h = lift f := by
  apply MonoidHom.ext'
  funext xs
  induction xs with
  | nil => exact h.map_mempty                -- 同态必须把 [] 送到 mempty
  | cons x xs ih =>
    have : x :: xs = [x] ⋄ xs := rfl          -- 每个非空词都是“首字母 ⋄ 剩下的”
    rw [this, h.map_mappend, ih]              -- h 保持乘法，再对剩下的用归纳假设
    show h.toFun [x] ⋄ foldMap f xs = f x ⋄ foldMap f xs
    rw [← hf]                                 -- 在单字母词上，h 就是 f
    rfl

end Free

/-- 定理：(List α, gens) 是以 α 为生成元的自由幺半群。 -/
def listIsFree (α : Type) : IsFreeMonoid α (List α) gens where
  lift := lift
  fac := lift_gens
  uniq := lift_unique
```

::: info 数学小课堂：唯一性证明在说什么
存在性很直观：你告诉我每个字母去哪（`f`），我就知道每个词去哪（逐字母翻译后乘起来）。

唯一性说的是：**你别无选择**。任何同态 `h`，只要在单字母词上和 `f` 一致，在所有词上都和 `foldMap f` 一致。理由是：

- 空词 `[]` 是单位元，同态必须把它送到单位元；
- 非空词 `x :: xs` 等于 `[x] ⋄ xs`，同态必须把它送到 `h [x] ⋄ h xs = f x ⋄ h xs`，而 `h xs` 由归纳假设已经确定。

一句话：**同态在生成元上的取值，决定了它在一切元素上的取值**——因为自由幺半群的每个元素都是生成元的积，而且没有额外的等式来“打架”。
:::

`foldMap` 其实就是用 `foldr` 写的老朋友：

```lean
theorem foldMap_eq_foldr {α m : Type} [CTFP.Monoid m] (f : α → m) (xs : List α) :
    foldMap f xs = xs.foldr (fun x acc => f x ⋄ acc) mempty := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [foldMap, ih]
```

有了自由性，各种“对列表求某个值”的函数都成了 `lift` 的特例。比如长度：把每个字母送到加法幺半群里的 `1`：

```lean
def lengthHom (α : Type) : MonoidHom (List α) AddN := lift (fun _ => ⟨1⟩)

#guard (lengthHom Char).toFun "abc".toList == ⟨3⟩
#guard (lift (fun n : Nat => (⟨n⟩ : MulN))).toFun [1, 2, 3, 4] == ⟨24⟩
```

::: tip Rust 视角：`fold`、`Vec` 与 `concat`
在 Rust 里，自由幺半群就是 `Vec<T>`（或者切片 `&[T]`）：单位元是 `Vec::new()`，乘法是拼接（`concat`、`extend`、`[a, b].concat()`）。而“唯一的同态”就是 `Iterator::fold`：

```rust
/// 幺半群 trait：Rust 无法强制检查定律，只能写在文档里。
trait Monoid {
    fn empty() -> Self;
    fn combine(self, other: Self) -> Self;
}

impl Monoid for String {
    fn empty() -> Self { String::new() }
    fn combine(mut self, other: Self) -> Self { self.push_str(&other); self }
}

struct Sum(u64);
impl Monoid for Sum {
    fn empty() -> Self { Sum(0) }
    fn combine(self, other: Self) -> Self { Sum(self.0 + other.0) }
}

struct Product(u64);
impl Monoid for Product {
    fn empty() -> Self { Product(1) }
    fn combine(self, other: Self) -> Self { Product(self.0 * other.0) }
}

/// 自由幺半群的泛性质：给定每个生成元的去向 f，整个词的去向被唯一确定。
fn fold_map<T, M: Monoid>(xs: &[T], f: impl Fn(&T) -> M) -> M {
    xs.iter().rev().fold(M::empty(), |acc, x| f(x).combine(acc))
}

pub fn demo() -> (u64, u64, String) {
    let word = vec!['a', 'b', 'a'];
    let len = fold_map(&word, |_| Sum(1)).0;                            // 3
    let prod = fold_map(&word, |c| Product(if *c == 'a' { 2 } else { 3 })).0; // 12
    let upper = fold_map(&word, |c| c.to_uppercase().collect::<String>()); // "ABA"
    // 同态性质：拼接之后再折叠 = 分别折叠之后再合并
    let (u, v) = (vec![1u64, 2], vec![3u64, 4]);
    let joined: Vec<u64> = [u.clone(), v.clone()].concat();
    assert_eq!(fold_map(&joined, |x| Sum(*x)).0,
               fold_map(&u, |x| Sum(*x)).combine(fold_map(&v, |x| Sum(*x))).0);
    (len, prod, upper)
}
```

`fold_map` 里的 `rev().fold(...)` 对应 Lean 的 `foldr`；对于满足结合律的运算，从左折（`fold`）和从右折结果相同——这正是结合律的用处。注意 Rust 的 `Monoid` trait 只能在注释里“要求”定律，而 Lean 的版本把定律写进了类型。
:::

下面的交互组件让你亲手体会“唯一的同态”与“自由”：选一个目标幺半群，指定生成元 `a`、`b` 的去向，看看每个词如何被唯一地映过去，以及哪些词被**等同**了。

<Ch2_3FreeMonoid />

顺便，这也回答了我们的第二个问题。函数 $U\,h$ 有能力把 $U\,m$ 中的多个元素压缩成 $U\,n$ 中的一个元素。这种压缩对应于把自由幺半群的某些元素等同起来。因此，任何以 $x$ 为生成元的幺半群，都可以从基于 $x$ 的自由幺半群出发，通过等同某些元素得到。自由幺半群就是只做了最低限度等同的那个。

::: info 数学小课堂：“任何幺半群都是自由幺半群的商”
在上面的组件里选 $(\mathbb{N}, +)$，令 $a \mapsto 1$、$b \mapsto 1$：所有长度相同的词都被压到同一个数上——`ab`、`ba`、`aa`、`bb` 全都变成了 2。$(\mathbb{N}, +)$ 中由 1 “生成”的部分，正是把自由幺半群里“长度相同的词”全部捆在一起的结果。

一般地，如果幺半群 $n$ 的每个元素都能写成某些“生成元” $q(x)$ 的积，那么 $U\,h$ 就是满射，$n$ 就是自由幺半群按照“$h$ 把哪些词送到同一个地方”取商的结果。自由幺半群是“什么都没捆”的版本，其他所有幺半群都是“捆了一些”的版本。
:::

我们在讲[伴随](/part3/03-free-forgetful-adjunctions)时还会回到自由幺半群。

## 挑战

1. 你可能会认为（我最初也这么认为）“幺半群同态要保持单位元”这个要求是多余的。毕竟，对所有 $a$ 我们知道：

   $$h\,a \cdot h\,e = h\,(a \cdot e) = h\,a$$

   所以 $h\,e$ 的行为像一个右单位元（类似地，也像左单位元）。问题在于，所有 $a$ 的 $h\,a$ 可能只覆盖了目标幺半群的一个子幺半群。在 $h$ 的像之外可能存在一个“真正的”单位元。证明：保持乘法的幺半群**同构**必然自动保持单位元。
2. 考虑一个从“带拼接的整数列表”到“带乘法的整数”的幺半群同态。空列表 `[]` 的像是什么？假设所有单元素列表都被映到它们所包含的整数，即 `[3]` 映到 3，等等。`[1, 2, 3, 4]` 的像是什么？有多少个不同的列表映到整数 12？这两个幺半群之间还有别的同态吗？
3. 由单元素集生成的自由幺半群是什么？你能看出它同构于什么吗？

::: details 参考答案 1：同构自动保持单位元（Lean 证明）
设 $h : m \to n$ 保持乘法，并且有逆函数 $g$（$h(g(y)) = y$，这里只需要 $h$ 是满射）。

1. 先证 $h(e)$ 是 $n$ 中的左单位元：对任意 $y \in n$，$h(e) \cdot y = h(e) \cdot h(g(y)) = h(e \cdot g(y)) = h(g(y)) = y$。关键在于：**满射**保证了每个 $y$ 都在 $h$ 的像里，所以“$h$ 的像之外的真单位元”这种情况不会出现。
2. 单位元是唯一的：$h(e) = h(e) \cdot e_n = e_n$（第一个等号用 $e_n$ 是右单位元，第二个用第 1 步）。

```lean
theorem iso_preserves_unit {m n : Type} [CTFP.Monoid m] [CTFP.Monoid n]
    (h : m → n) (g : n → m) (hg : ∀ y, h (g y) = y)
    (hmul : ∀ x y, h (x ⋄ y) = h x ⋄ h y) : h mempty = mempty := by
  -- 第 1 步：h mempty 是左单位元
  have left : ∀ y : n, h mempty ⋄ y = y := by
    intro y
    calc h mempty ⋄ y = h mempty ⋄ h (g y) := by rw [hg]
      _ = h (mempty ⋄ g y) := (hmul _ _).symm
      _ = h (g y) := by rw [mempty_mappend]
      _ = y := hg y
  -- 第 2 步：单位元唯一
  calc h mempty = h mempty ⋄ mempty := (mappend_mempty _).symm
    _ = mempty := left mempty
```

`calc` 是 Lean 写**链式等式**的方式：每一行 `_ = … := 理由` 都说“上一行的右边等于这一行的右边，理由是……”，整条链合起来证明首尾相等。这和你在纸上写推导一模一样。
:::

::: details 参考答案 2：整数列表到整数乘法
- `[]` 是单位元，必须映到乘法的单位元 **1**。
- 由同态性，`[1, 2, 3, 4] = [1] ++ [2] ++ [3] ++ [4]` 映到 $1 \times 2 \times 3 \times 4 = 24$。
- 映到 12 的列表有**无穷多个**：`[12]`、`[3, 4]`、`[4, 3]`、`[2, 6]`、`[2, 2, 3]`……而且可以在任意位置插入任意多个 `1`（`[1, 12]`、`[1, 1, 12]`……），还可以成对插入 `-1`（`[-1, -12]`、`[-1, 3, -4]`……）。
- 在“单元素列表映到它所含的整数”这个假设下，同态是**唯一**的——这正是自由幺半群的泛性质（同态被它在生成元上的取值完全决定）。但如果去掉这个假设，就有很多别的同态：每个函数 $f : \mathbb{Z} \to \mathbb{Z}$ 都恰好给出一个同态。例如把每个整数都送到 1（于是所有列表都映到 1），或者 $x \mapsto x^2$、$x \mapsto |x|$、$x \mapsto 0$。

Lean 中直接用 `lift` 得到这个同态，所有结论都能计算验证：

```lean
structure MulZ where
  val : Int
  deriving Repr, DecidableEq

instance : CTFP.Monoid MulZ where
  mempty := ⟨1⟩
  mappend x y := ⟨x.val * y.val⟩
  mempty_mappend x := by cases x; simp
  mappend_mempty x := by cases x; simp
  mappend_assoc x y z := by simp [Int.mul_assoc]

/-- 唯一一个把 [k] 送到 k 的同态。 -/
def prodZ : MonoidHom (List Int) MulZ := lift (fun k => ⟨k⟩)

#guard prodZ.toFun [] == ⟨1⟩
#guard prodZ.toFun [1, 2, 3, 4] == ⟨24⟩
#guard [[12], [3, 4], [4, 3], [2, 2, 3], [1, 1, 12], [-1, -12]].all (prodZ.toFun · == ⟨12⟩)

/-- 另一个同态：每个整数先平方。 -/
def squareZ : MonoidHom (List Int) MulZ := lift (fun k => ⟨k * k⟩)
#guard squareZ.toFun [2, 3] == ⟨36⟩
```
:::

::: details 参考答案 3：单生成元的自由幺半群
单元素集 `Unit` 生成的自由幺半群是 `List Unit`：`[]`、`[()]`、`[(), ()]`……一个这样的列表唯一携带的信息就是它的**长度**。所以它同构于**自然数的加法幺半群** $(\mathbb{N}, +, 0)$：拼接对应加法，空列表对应 0。

```lean
def lenU : List Unit → AddN := fun xs => ⟨xs.length⟩
def repU : AddN → List Unit := fun n => List.replicate n.val ()

/-- 往返一：列表 → 长度 → 列表，回到原处。 -/
theorem rep_len (xs : List Unit) : repU (lenU xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x                     -- Unit 只有一个元素 ()
    show () :: List.replicate xs.length () = () :: xs
    exact congrArg (List.cons ()) ih

/-- 往返二：数 → 列表 → 长度，回到原处。 -/
theorem len_rep (n : AddN) : lenU (repU n) = n := by
  cases n; simp [lenU, repU]

/-- 而且长度是一个幺半群同态：拼接变加法。 -/
def lenHomU : MonoidHom (List Unit) AddN where
  toFun := lenU
  map_mempty := rfl
  map_mappend xs ys := by simp [lenU, Monoid.mappend, List.length_append]
```

所以 `List Unit` 和 `AddN` 是**同构的幺半群**。这也解释了为什么自然数如此“基本”：它们就是只有一个生成元时的自由幺半群——“数数”就是“把同一个东西重复若干次”。
:::

## 本章小结

- **幺半群**是带一个满足结合律的乘法和一个单位元的集合；也可以看成只有一个对象的范畴。乘法可以拆成“配对”和“等同”两步。
- **自由构造**：不断生成所有组合，只做定律强迫的最少等同。由生成元 $\{a, b\}$ 得到的**自由幺半群**就是所有 $a$、$b$ 组成的列表，乘法是拼接，单位元是空列表。
- 在 Lean 中，幺半群定律可以作为类型类的字段写进 `class Monoid`，每个实例都必须给出证明——这是 Haskell 和 Rust 都做不到的。
- **幺半群同态**是保持乘法与单位元的函数（`structure MonoidHom`）；幺半群与同态构成范畴 $\mathbf{Mon}$。
- **遗忘函子** $U : \mathbf{Mon} \to \mathbf{Set}$ 把幺半群送到底层集合、把同态送到底层函数，让我们能在 $\mathbf{Mon}$ 中“看到”生成元。
- **泛构造**：$(m, p : x \to U\,m)$ 是自由幺半群，当且仅当对任何 $(n, q : x \to U\,n)$，都有**唯一**的同态 $h : m \to n$ 使 $q = U\,h \circ p$。
- 我们在 Lean 中证明了 `List α` 是自由幺半群：存在性由 `foldMap`（即 `foldr`）给出，唯一性用对列表的归纳法证明。对应到 Rust，就是 `Iterator::fold`。
- 任何幺半群都可以由自由幺半群通过“等同更多元素”得到：$U\,h$ 负责把多个词压到同一个元素上。自由意味着除了定律之外没有任何额外的等式（`ab ≠ ba`）。
