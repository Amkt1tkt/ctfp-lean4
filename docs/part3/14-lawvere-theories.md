# 3.14 Lawvere 理论

如今谈函数式编程，几乎不可能不提到单子。不过，不妨想象一个平行宇宙：在那里，Eugenio Moggi 碰巧没有把目光投向单子，
而是投向了 **Lawvere 理论**（Lawvere theory）。这一章，我们就去那个宇宙里逛一逛。

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

instance typeCategory : Category (Type u) where
  Hom a b := a → b
  id _ := fun x => x
  comp g f := fun x => g (f x)

structure CFunctor (C : Type u₁) [Category.{u₁, v₁} C] (D : Type u₂) [Category.{u₂, v₂} D] where
  obj : C → D
  map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id : ∀ (a : C), map (𝟙 a) = 𝟙 (obj a)
  map_comp : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c), map (g ⊚ f) = map g ⊚ map f

def Op (C : Type u) : Type u := C

instance opCategory (C : Type u) [Category.{u, v} C] : Category.{u, v} (Op C) where
  Hom a b := @Category.Hom C _ b a
  id a := @Category.id C _ a
  comp g f := @Category.comp C _ _ _ _ f g
  id_comp f := @Category.comp_id C _ _ _ f
  comp_id f := @Category.id_comp C _ _ _ f
  assoc f g h := (@Category.assoc C _ _ _ _ _ h g f).symm

end CTFP

open CTFP
```

## 泛代数

描述“代数”的方式有很多，抽象程度也各不相同。我们想找到一种通用的语言，能统一地描述幺半群、群、环这类东西。
在最朴素的层面上，这些构造都是在某个集合的元素上定义一些**运算**（operation），再要求这些运算满足一些**定律**（law）。

比如，幺半群可以用一个满足结合律的二元运算来定义。另外还有一个单位元，以及单位律。不过只要稍微发挥一点想象力，
就可以把单位元也看成一个运算：一个**零元运算**（nullary operation）——它不接受任何参数，直接返回集合中某个特殊的元素。
如果要谈群，就再加一个一元运算：输入一个元素，返回它的逆元；与之配套的还有左逆律和右逆律。环则定义了两个二元运算，外加更多的定律。
依此类推。

大图景是这样的：一个代数由一组**$n$ 元运算**（对各种不同的 $n$）和一组**等式恒等式**（equational identity）来定义。
这些恒等式全都是**全称量化**的：结合律必须对任意三个元素的所有组合都成立，诸如此类。

顺带一提，这就把**域**（field）排除在外了，原因很简单：零（加法的单位元）在乘法下没有逆元。
域的“逆元律”没法写成对所有元素都成立的形式。

::: info 数学小课堂：运算、元数与“全称量化的等式”
- **$n$ 元运算**就是一个“吃 $n$ 个元素、吐 1 个元素”的函数。$n$ 叫作运算的**元数**（arity）。
  加法 $+$ 是二元的（arity 2），取相反数 $-x$ 是一元的，“常数 0”是零元的（不吃任何东西，直接给出 0）。
- **全称量化的等式**形如“对所有 $x, y, z$，都有 $(x \cdot y) \cdot z = x \cdot (y \cdot z)$”。等式两边都是用运算和变量搭出来的“表达式”，
  而且必须对变量的**每一种**取值都成立。
- 为什么域不行？域要求“对所有 $x \neq 0$，存在 $x^{-1}$ 使 $x \cdot x^{-1} = 1$”。这里有一个**条件** $x \neq 0$，
  不是“对所有 $x$”。而“逆元”这个一元运算如果对所有 $x$ 都定义，就会撞上 $0 \cdot 0^{-1} = 1$，矛盾。
  所以域不是一个“泛代数”（universal algebra）。群、幺半群、环、格、布尔代数……都是。
:::

这个关于**泛代数**（universal algebra）的定义可以推广到 $\mathbf{Set}$ 以外的范畴：把运算（函数）换成态射就行。
我们不再选一个集合，而是选一个对象 $a$（称为**泛型对象**，generic object）。一元运算就是 $a$ 上的一个自态射。
其他元数呢？二元运算（元数为 2）可以定义为从积 $a \times a$ 回到 $a$ 的态射。一般的 $n$ 元运算，就是从 $a$ 的 $n$ 次幂到 $a$ 的态射：

$$\alpha_n \colon a^n \to a$$

零元运算是从终对象（$a$ 的零次幂）出发的态射。所以，要定义任何一种代数，我们只需要一个范畴，它的对象全是某个特殊对象 $a$ 的各次幂。
具体是哪一种代数，就编码在这个范畴的 hom-集里。一言以蔽之，这就是 Lawvere 理论。

### 补充：在 Lean 里，“$a$ 的 $n$ 次幂”就是 `Fin n → α`

在动手搭 Lawvere 理论之前，我们先准备一件 Lean 里的趁手工具：`Fin n`。它会贯穿整章。

::: tip Lean 深入：`Fin n` —— 恰好有 $n$ 个元素的类型
Lean 核心库里的 `Fin n` 是“小于 `n` 的自然数”组成的类型。它是一个结构体，大致长这样：

```lean no-check
structure Fin (n : Nat) where
  val  : Nat       -- 数值本身
  isLt : val < n   -- 一个证明：这个数确实小于 n
```

所以 `Fin 3` 恰好有三个元素 `0, 1, 2`；`Fin 1` 只有一个元素 `0`；而 `Fin 0` **一个元素也没有**——
因为不存在小于 0 的自然数，`isLt` 的证明永远造不出来。可以说，`Fin n` 就是“标准的 $n$ 元有限集合”。

几个要点：

- 字面量 `(2 : Fin 3)` 是合法的；Lean 会自动生成 `isLt` 的证明。（字面量会取模，`(7 : Fin 5)` 是 `2`，写代码时留个心眼。）
- `Fin 0` 是空类型，所以从它出发的函数只有一个：`Fin.elim0 : Fin 0 → α`（“空情形分析”，相当于 Rust 里对 `enum Void {}` 做 `match x {}`）。
- 函数 `Fin n → α` 就是“一个长度为 $n$ 的 $\alpha$ 元组”：给每个下标 `i` 指定一个分量。这正是 $a^n$。
:::

::: tip Rust 视角
`Fin n → α` 很像 Rust 的定长数组 `[T; N]`：长度写在类型里，下标访问永远不会越界——
只不过 Rust 靠运行时边界检查（或 `get` 返回 `Option`），而 Lean 的 `Fin n` 把“下标小于 `n`”的证明直接塞进了下标本身。
:::

```lean
/-- 一个具体的 3 元组：(10, 20, 30) -/
def triple : Fin 3 → Nat
  | 0 => 10
  | 1 => 20
  | 2 => 30

example : triple 1 = 20 := rfl
example : (2 : Fin 3).val = 2 := rfl

/-- `a⁰` 只有一个元素：从空类型出发的函数都相等。这就是“零次幂是终对象”。 -/
theorem pow_zero_unique {α : Type} (f g : Fin 0 → α) : f = g :=
  funext (fun i => i.elim0)
```

这里第一次出现了 `funext`：它是**函数外延性**——要证两个函数相等，只需证它们在每个输入上相等。
而对 `Fin 0` 中的“每个输入” `i`，`i.elim0` 立刻告诉 Lean：这种 `i` 根本不存在，所以什么都成立。

有了 `Fin`，就可以把“运算 + 等式”的语法写下来了。先是**签名**（signature）：一组运算的名字，每个名字带一个元数。

```lean
/-- 签名：有哪些运算，每个运算吃几个参数。 -/
structure Signature where
  Op    : Type
  arity : Op → Nat
```

再是**项**（term）：用变量和运算搭出来的表达式树。`Term σ n` 是“签名 `σ` 上、至多使用 `n` 个变量的项”，
变量用 `Fin n` 编号：

```lean
inductive Term (σ : Signature) (n : Nat) where
  /-- 第 `i` 个变量 -/
  | var : Fin n → Term σ n
  /-- 运算 `o` 作用在 `arity o` 个子项上（子项本身也是一个元组！） -/
  | op  : (o : σ.Op) → (Fin (σ.arity o) → Term σ n) → Term σ n
```

请注意 `op` 的第二个参数：一个运算有 `σ.arity o` 个参数，我们用 `Fin (σ.arity o) → Term σ n` 来表示这一串子项——
又是“元组 = 从 `Fin` 出发的函数”。这是一棵分叉数随节点而变的树。

::: tip Lean 深入：依值类型的小用法
`op` 的类型里，第二个参数的类型 `Fin (σ.arity o) → …` **依赖于**第一个参数 `o` 的值。这就是依值类型（dependent type）。
在 Rust 里你得写 `Op(OpName, Vec<Term>)`，然后在运行时祈祷 `Vec` 的长度和元数对得上；在 Lean 里，长度不对的项根本写不出来。
:::

有了语法，还需要“意义”。给项赋予意义就是写一个解释器：每个运算要被解释成载体 `α` 上的一个函数，每个变量要被赋一个值（一个“环境” `env : Fin n → α`，也就是一个 $n$ 元组）。

```lean
namespace Term
variable {σ : Signature}

/-- 求值：给定每个运算的解释 `interp` 和变量的取值 `env`，计算项的值。 -/
def eval {α : Type} (interp : (o : σ.Op) → (Fin (σ.arity o) → α) → α)
    {n : Nat} (env : Fin n → α) : Term σ n → α
  | var i     => env i
  | op o args => interp o (fun i => eval interp env (args i))

end Term
```

这就是一个最普通的递归解释器——程序员一看就懂。本章接下来要做的，就是看出：
**签名 + 项 + 解释器**这套东西，背后藏着一个范畴（Lawvere 理论），而一个“解释”正是从这个范畴到 $\mathbf{Set}$ 的保积函子（模型）。

Lawvere 理论的推导要经过好几步，先给出路线图：

1. 有限集合的范畴 $\mathbf{FinSet}$。
2. 它的骨架 $\mathbf{F}$。
3. 骨架的对偶 $\mathbf{F}^{op}$。
4. Lawvere 理论 $\mathbf{L}$：范畴 $\mathbf{Law}$ 中的一个对象。
5. Lawvere 范畴的模型 $M$：范畴 $\mathbf{Mod}(\mathbf{L}, \mathbf{Set})$ 中的一个对象。

![Lawvere 理论的路线图](/img/3.14/lawvere1.png "从左到右：有限集合的骨架 F，它的对偶 F^op，经 I_L 嵌入 Lawvere 理论 L，再由模型 M 映到 Set，其中 M n = (M 1)^n。")

## Lawvere 理论

所有 Lawvere 理论共享同一副骨架。Lawvere 理论中的所有对象，都是用积（准确地说，只用幂）从同一个对象生成出来的。
可是在一般的范畴里，该怎么定义这些积呢？事实证明，可以借助一个更简单的范畴的映射来定义积。
而且这个更简单的范畴里定义的甚至可以是**余积**，然后我们用一个**逆变**函子把它嵌入目标范畴。逆变函子会把余积变成积，把内射变成投影。

Lawvere 范畴的骨架，最自然的选择是有限集合的范畴 $\mathbf{FinSet}$。它包含空集 $\varnothing$、单元素集 $1$、二元素集 $2$，等等。
这个范畴里的所有对象都可以用余积从单元素集生成出来（把空集看作零个对象的余积这一特例）。例如，二元素集就是两个单元素集的和，$2 = 1 + 1$。
用 Lean 写出来：

```lean
abbrev Two := Unit ⊕ Unit

def Two.first  : Two := .inl ()
def Two.second : Two := .inr ()
```

不过，尽管我们很自然地认为空集只有一个，单元素集却可能有许多个互不相同的。特别地，集合 $1 + \varnothing$ 与 $\varnothing + 1$ 不同，也与 $1$ 不同——
尽管它们彼此同构。集合范畴中的余积**不满足结合律**（严格意义上）。在 Lean 里这一点看得清清楚楚：

```lean
-- `Unit ⊕ Empty` 和 `Empty ⊕ Unit` 是两个不同的类型，但它们同构：
def swapUE : Unit ⊕ Empty → Empty ⊕ Unit
  | .inl u => .inr u
  | .inr e => e.elim

def swapEU : Empty ⊕ Unit → Unit ⊕ Empty
  | .inl e => e.elim
  | .inr u => .inl u

theorem swap_iso₁ (x : Unit ⊕ Empty) : swapEU (swapUE x) = x := by
  cases x with
  | inl u => rfl
  | inr e => exact e.elim

theorem swap_iso₂ (x : Empty ⊕ Unit) : swapUE (swapEU x) = x := by
  cases x with
  | inl e => exact e.elim
  | inr u => rfl
```

补救的办法是构造一个范畴，把所有彼此同构的集合认同为一个。这样的范畴叫作**骨架**（skeleton）。
换句话说，任何 Lawvere 理论的骨架都是 $\mathbf{FinSet}$ 的骨架 $\mathbf{F}$。这个范畴的对象可以与自然数（包括零）一一对应，
也就是 $\mathbf{FinSet}$ 中集合的元素个数。余积扮演加法的角色。$\mathbf{F}$ 中的态射对应有限集合之间的函数。例如：

- 从 $\varnothing$ 到 $n$ 有唯一一个态射（空集是始对象）；
- 从 $n$ 到 $\varnothing$ 没有态射（$\varnothing \to \varnothing$ 除外）；
- 从 $1$ 到 $n$ 有 $n$ 个态射（即各个内射）；
- 从 $n$ 到 $1$ 有一个态射；

等等。这里的 $n$ 表示 $\mathbf{F}$ 中的一个对象，它代表了 $\mathbf{FinSet}$ 里所有经同构认同在一起的 $n$ 元集合。

::: info 数学小课堂：骨架
把一个范畴里“彼此同构的对象”都只留一个代表，得到的子范畴就叫**骨架**。
就像整理衣柜：十件一模一样的白 T 恤，你只需要记住“白 T 恤”这一种。
对有限集合来说，同构 = 元素个数相同，所以每个元素个数 $n$ 留一个代表就够了——Lean 里正好有现成的代表：`Fin n`。
:::

在 Lean 中，骨架 $\mathbf{F}$ 可以直接写出来：对象是自然数，从 $m$ 到 $n$ 的态射就是函数 `Fin m → Fin n`。

```lean
/-- 有限集合范畴的骨架 𝐅：对象是自然数 n（代表 n 元集合 `Fin n`）。
用一个新名字包一层，免得给 `Nat` 本身挂上范畴实例。 -/
def FinSk : Type := Nat

instance : Category FinSk where
  Hom m n := Fin m → Fin n
  id _ := fun i => i
  comp g f := fun i => g (f i)
```

三条范畴定律都由 `rfl` 自动完成（`Category` 定义里给了默认证明 `by intros; rfl`）。上面列出的那几条计数事实，也都可以在 Lean 里证明：

```lean
/-- 0 是始对象：从 0 到 n 的态射只有一个。 -/
theorem from_zero_unique {n : Nat} (f g : Fin 0 → Fin n) : f = g :=
  funext (fun i => i.elim0)

/-- 从 1 到 0 没有态射。 -/
theorem no_map_one_zero (f : Fin 1 → Fin 0) : False :=
  (f 0).elim0

/-- 从 n 到 1 的态射只有一个（1 是终对象）。 -/
theorem to_one_unique {n : Nat} (f g : Fin n → Fin 1) : f = g := by
  funext i
  apply Fin.ext          -- 两个 Fin 相等 ⇔ 数值相等
  have h₁ := (f i).isLt  -- (f i).val < 1
  have h₂ := (g i).isLt  -- (g i).val < 1
  omega                  -- 所以两者都只能是 0

/-- 从 1 到 n 的态射恰好与 `Fin n` 一一对应：一共 n 个（“选出第 k 个元素”）。 -/
def fromOne {n : Nat} (f : Fin 1 → Fin n) : Fin n := f 0
def toFromOne {n : Nat} (k : Fin n) : Fin 1 → Fin n := fun _ => k

theorem fromOne_toFromOne {n : Nat} (k : Fin n) : fromOne (toFromOne k) = k := rfl
theorem toFromOne_fromOne {n : Nat} (f : Fin 1 → Fin n) : toFromOne (fromOne f) = f := by
  funext i
  have : i = 0 := Fin.ext (by have := i.isLt; omega)
  subst this
  rfl
```

::: tip Lean 深入：`omega`
`omega` 是一个判定程序：只要目标是关于整数/自然数的**线性**算术命题（加减、常数倍、比较），而且所需的事实都在上下文里，它就能自动证完。
上面它从 `(f i).val < 1` 和 `(g i).val < 1` 推出两者相等。
:::

在骨架里，余积对应加法：`Fin (m + n)` 可以拆成“前 `m` 个”和“后 `n` 个”两段。Lean 核心库提供了两个内射
`Fin.castAdd n : Fin m → Fin (m + n)` 与 `Fin.natAdd m : Fin n → Fin (m + n)`，以及按段做情形分析的 `Fin.addCases`——
这正是余积的泛性质：要定义一个从 $m + n$ 出发的函数，只需分别给出从 $m$ 和从 $n$ 出发的函数。

```lean
/-- 余积的“配对”：[f, g] : m + n → k。 -/
def copair {m n k : Nat} (f : Fin m → Fin k) (g : Fin n → Fin k) : Fin (m + n) → Fin k :=
  Fin.addCases f g

/-- 泛性质的一半：先内射再配对，等于原来的 f。 -/
theorem copair_castAdd {m n k : Nat} (f : Fin m → Fin k) (g : Fin n → Fin k) (i : Fin m) :
    copair f g (Fin.castAdd n i) = f i :=
  Fin.addCases_left i
```

借助范畴 $\mathbf{F}$，我们可以给出 **Lawvere 理论**的正式定义：它是一个范畴 $\mathbf{L}$，配有一个特殊的函子

$$I_{\mathbf{L}} \colon \mathbf{F}^{op} \to \mathbf{L}$$

这个函子必须在对象上是双射，并且必须保持有限积（$\mathbf{F}^{op}$ 中的积就是 $\mathbf{F}$ 中的余积）：

$$I_{\mathbf{L}} (m \times n) = I_{\mathbf{L}}\, m \times I_{\mathbf{L}}\, n$$

你有时会看到人们说这个函子是“对象上的恒等”（identity-on-objects），意思是 $\mathbf{F}$ 和 $\mathbf{L}$ 的对象是同一批。
因此我们给它们用同样的名字——都用自然数来表示。但要记住，$\mathbf{F}$ 中的对象并不是集合（它们是同构集合组成的类）。

$\mathbf{L}$ 中的 hom-集一般比 $\mathbf{F}^{op}$ 中的更丰富。除了与 $\mathbf{FinSet}$ 中的函数相对应的那些态射（后者有时被称为**基本积运算**，basic product operations），
它们还可以包含别的态射。Lawvere 理论的等式定律，就编码在这些态射之中。

关键的观察是：$\mathbf{F}$ 中的单元素集 $1$ 被映到 $\mathbf{L}$ 中某个我们也叫作 $1$ 的对象，而 $\mathbf{L}$ 中的其他所有对象自动成了这个对象的幂。
例如，$\mathbf{F}$ 中的二元素集 $2$ 是余积 $1 + 1$，所以它必须被映到 $\mathbf{L}$ 中的积 $1 \times 1$（即 $1^2$）。
从这个意义上说，范畴 $\mathbf{F}$ 表现得像是 $\mathbf{L}$ 的**对数**。

$\mathbf{L}$ 的态射中，有一些是由函子 $I_{\mathbf{L}}$ 从 $\mathbf{F}$ 搬运过来的。它们在 $\mathbf{L}$ 中起结构性作用。
特别地，余积的内射 $i_k$ 变成了积的投影 $p_k$。一个有用的直觉是把投影

$$p_k \colon 1^n \to 1$$

想象成“一个 $n$ 元函数的原型：它忽略除第 $k$ 个变量以外的所有变量”。反过来，$\mathbf{F}$ 中的常值态射 $n \to 1$ 在 $\mathbf{L}$ 中变成了对角态射 $1 \to 1^n$，它们对应于**复制变量**。

$\mathbf{L}$ 中真正有趣的态射，是那些定义了投影以外的 $n$ 元运算的态射。正是它们把一个 Lawvere 理论与另一个区分开来。
它们是乘法、加法、单位元的选取等等——也就是定义代数的那些东西。但为了让 $\mathbf{L}$ 成为完整的范畴，我们还需要复合运算 $n \to m$（等价地，$1^n \to 1^m$）。
由于这个范畴的结构很简单，它们原来就是一些更简单的、类型为 $n \to 1$ 的态射的积。
这推广了“返回积的函数就是函数的积”这一说法；我们之前见过，hom-函子是连续的。

![Lawvere 理论 L 建立在 F^op 之上](/img/3.14/lawvere1.png "Lawvere 理论 L 以 F^op 为基础，从那里继承了定义积的那些“无聊”态射；它又添加了描述 n 元运算的“有趣”态射（虚线箭头）。")

### 补充：用项搭出一个 Lawvere 理论

上面的描述在 Lean 里可以原样搭出来。给定签名 `σ`，我们来构造一个范畴 `Syn σ`（“syntax”，语法范畴）：

- 对象：自然数 $n$（代表 $1^n$）。
- 从 $n$ 到 $m$ 的态射：**$m$ 个**、每个都含 $n$ 个变量的项，即 `Fin m → Term σ n`。
  当 $m = 1$ 时，它就是“一个 $n$ 元运算的原型”——一个含 $n$ 个变量的表达式。正如上面所说，$n \to m$ 的态射就是 $m$ 个 $n \to 1$ 态射的积（一个元组）。
- 复合：**代入**（substitution）。若 $f \colon k \to m$ 给出了 $m$ 个含 $k$ 个变量的项，$g \colon m \to n$ 给出了 $n$ 个含 $m$ 个变量的项，
  那么 $g \circ f$ 就是把 $f$ 的那些项代入 $g$ 的项中的变量。
- 恒等态射：变量本身，`var`。

先写代入，并证明两条关键引理：

```lean
namespace Term
variable {σ : Signature}

/-- 代入：把项里的第 i 个变量替换成 `s i`。 -/
def subst {m n : Nat} (s : Fin m → Term σ n) : Term σ m → Term σ n
  | var i     => s i
  | op o args => op o (fun i => subst s (args i))

/-- 用变量本身代入，什么都不变（单位律）。 -/
theorem subst_var {n : Nat} (t : Term σ n) : t.subst var = t := by
  induction t with
  | var i => rfl
  | op o args ih =>
    -- 归纳假设 ih : ∀ i, (args i).subst var = args i
    simp only [subst]
    congr
    funext i
    exact ih i

/-- 先代入 f 再代入 g，等于一次性代入“f 代入 g 之后的结果”（结合律）。 -/
theorem subst_subst {k m n : Nat} (f : Fin k → Term σ m) (g : Fin m → Term σ n) (t : Term σ k) :
    (t.subst f).subst g = t.subst (fun i => (f i).subst g) := by
  induction t with
  | var i => rfl
  | op o args ih =>
    simp only [subst]
    congr
    funext i
    exact ih i

end Term
```

::: tip Lean 深入：对“分叉数可变的树”做归纳
`induction t with` 会为 `Term` 的每个构造子生成一个目标。对 `op o args`，归纳假设 `ih` 的形状是 `∀ i, P (args i)`——
对**每个**子项都成立。这比 Rust 里手写 `children.iter().all(...)` 要省心得多：Lean 根据 `inductive` 的定义自动推出了正确的归纳原理。
`congr` 把 `op o A = op o B` 化简为 `A = B`，`funext i` 再把函数相等化为逐点相等。
:::

现在可以搭出语法范畴，并把 $\mathbf{F}^{op}$ 嵌进去：

```lean
/-- 签名 σ 的语法范畴：一个（没有额外等式的）Lawvere 理论。
对象仍是自然数；签名只是一个“标签”，决定下面用哪种项作态射，所以参数不必命名。 -/
def Syn (_ : Signature) : Type := Nat

instance (σ : Signature) : Category (Syn σ) where
  Hom n m := Fin m → Term σ n
  id _ := Term.var
  comp g f := fun i => (g i).subst f
  id_comp _ := rfl
  comp_id g := by funext i; exact Term.subst_var (g i)
  assoc f g h := by funext i; exact (Term.subst_subst g f (h i)).symm

/-- I_L : 𝐅ᵒᵖ ⥤ Syn σ。𝐅 中的函数 f : m → n（一个“基本积运算”）
变成 Syn σ 中的态射 n → m：第 i 个输出就是第 (f i) 个变量。 -/
def embed (σ : Signature) : CFunctor (Op FinSk) (Syn σ) where
  obj n := (n : Nat)
  map f := fun i => Term.var (f i)
  map_id _ := rfl
  map_comp _ _ := rfl
```

看看 `embed` 把什么变成了什么：$\mathbf{F}$ 中的内射 $1 \to n$（“选第 $k$ 个元素”）变成了 `fun _ => var k`，
也就是“只用第 $k$ 个变量的项”——投影 $p_k$。$\mathbf{F}$ 中的常值函数 $n \to 1$ 变成了 $n$ 个都等于 `var 0` 的项——把一个变量复制 $n$ 份，即对角态射。
而 `op` 搭出的那些项，就是“有趣”的态射，它们不来自 $\mathbf{F}$。

::: warning 易错点：这个 `Syn σ` 还没有等式
`Syn σ` 中两个态射相等，当且仅当它们是**字面上相同**的项。所以它是由签名 σ **自由生成**的 Lawvere 理论，不包含任何定律。
要得到幺半群的理论，还得把“结合律、单位律能推出相等的项”认同起来（数学上是对项做商；Lean 里可以用 `Quot`）。
本章稍后会走另一条更省力的路：给幺半群的项找一个**范式**。
:::

Lawvere 理论构成一个范畴 $\mathbf{Law}$。其中的态射是保持有限积、并且与函子 $I$ 交换的函子。给定两个这样的理论
$(\mathbf{L}, I_{\mathbf{L}})$ 和 $(\mathbf{L'}, I'_{\mathbf{L'}})$，它们之间的态射是一个函子 $F \colon \mathbf{L} \to \mathbf{L'}$，满足：

$$F (m \times n) = F m \times F n$$

$$F \circ I_{\mathbf{L}} = I'_{\mathbf{L'}}$$

Lawvere 理论之间的态射体现了“在一个理论内部解释另一个理论”的想法。例如，如果忽略逆元，群的乘法就可以被解释为幺半群的乘法。

最简单的平凡例子就是 $\mathbf{F}^{op}$ 本身（对应于把 $I_{\mathbf{L}}$ 选为恒等函子）。这个既没有运算也没有定律的 Lawvere 理论，恰好是 $\mathbf{Law}$ 中的始对象。

在这个时候，如果能给出一个非平凡的 Lawvere 理论的例子，会很有帮助；但如果不先理解什么是模型，这个例子很难讲清楚。

## Lawvere 理论的模型

理解 Lawvere 理论的关键在于认识到：一个这样的理论概括了许多结构相同的具体代数。
例如，幺半群的 Lawvere 理论描述了“作为幺半群”的本质，它必须对所有幺半群都成立。一个具体的幺半群，就成了这个理论的一个**模型**（model）。
模型被定义为从 Lawvere 理论 $\mathbf{L}$ 到集合范畴 $\mathbf{Set}$ 的函子。（Lawvere 理论有一些推广，会使用别的范畴作为模型的去处，但这里我只关注 $\mathbf{Set}$。）
由于 $\mathbf{L}$ 的结构高度依赖于积，我们要求这样的函子保持有限积。因此，$\mathbf{L}$ 的模型——也称为 Lawvere 理论 $\mathbf{L}$ 上的**代数**——由这样一个函子定义：

$$M \colon \mathbf{L} \to \mathbf{Set}$$

$$M (a \times b) \cong M a \times M b$$

注意，我们只要求积在**同构意义下**被保持。这一点非常重要，因为严格地保持积会把绝大多数有趣的理论排除在外。

::: tip Lean 深入：为什么只能要求“同构意义下”
在 Lean 里，模型会把对象 $n$ 送到 `Fin n → α`。那么 $M(2 + 1)$ 是 `Fin (2 + 1) → α`，而 $M 2 \times M 1$ 是 `(Fin 2 → α) × (Fin 1 → α)`。
这显然是两个**不同的类型**：一个是函数，一个是序对。但它们之间有一对互逆的转换（用 `Fin.addCases` 拼起来，用 `Fin.castAdd`/`Fin.natAdd` 拆开），所以同构。
要求“等于”是不现实的；要求“同构”恰到好处。
:::

模型保持积，意味着 $M$ 在 $\mathbf{Set}$ 中的像是一串由集合 $M 1$ 的幂生成的集合——$M 1$ 是 $\mathbf{L}$ 中对象 $1$ 的像。我们把这个集合叫作 $a$。
（这个集合有时被称为一个**种类**（sort），这样的代数被称为**单种类的**（single-sorted）。Lawvere 理论也有面向多种类代数的推广。）
特别地，$\mathbf{L}$ 中的二元运算被映成函数：

$$a \times a \to a$$

和任何函子一样，$\mathbf{L}$ 中的多个态射有可能被压缩成 $\mathbf{Set}$ 中的同一个函数。

顺带一提，所有定律都是全称量化的等式，这意味着每个 Lawvere 理论都有一个平凡模型：常值函子，把所有对象映到单元素集，把所有态射映到它上面的恒等函数。

$\mathbf{L}$ 中一般形如 $m \to n$ 的态射被映成函数：

$$a^m \to a^n$$

如果有两个不同的模型 $M$ 和 $N$，它们之间的自然变换是一族以 $n$ 为下标的函数：

$$\mu_n \colon M n \to N n$$

或者等价地：

$$\mu_n \colon a^n \to b^n$$

其中 $b = N 1$。

注意，自然性条件保证了 $n$ 元运算被保持：

$$N f \circ \mu_n = \mu_1 \circ M f$$

其中 $f \colon n \to 1$ 是 $\mathbf{L}$ 中的一个 $n$ 元运算。

```diagram
Mn: (0, 0) "M n"
Nn: (2.4, 0) "N n"
M1: (0, 1.6) "M 1"
N1: (2.4, 1.6) "N 1"
mun: Mn -> Nn "\mu_n"
Mf: Mn -> M1 "M f" side=right
Nf: Nn -> N1 "N f"
mu1: M1 -> N1 "\mu_1" side=right
path "先运算，再变换": Mf mu1
path "先变换，再运算": mun Nf color=green
caption: 自然性方块（M n = aⁿ，M 1 = a，N n = bⁿ，N 1 = b）：在 a 里做运算再搬到 b，与先逐个搬到 b 再在 b 里做运算，结果相同——这就是“同态”。
```

定义模型的那些函子构成一个模型范畴 $\mathbf{Mod}(\mathbf{L}, \mathbf{Set})$，以自然变换为态射。

考虑平凡 Lawvere 范畴 $\mathbf{F}^{op}$ 的模型。这样的模型完全由它在 $1$ 处的取值 $M 1$ 决定。由于 $M 1$ 可以是任意集合，
这样的模型和 $\mathbf{Set}$ 中的集合一样多。此外，$\mathbf{Mod}(\mathbf{F}^{op}, \mathbf{Set})$ 中的每个态射（函子 $M$ 与 $N$ 之间的自然变换）都由它在 $1$ 处的分量唯一确定。
反过来，每个函数 $M 1 \to N 1$ 都诱导出两个模型 $M$ 与 $N$ 之间的一个自然变换。因此 $\mathbf{Mod}(\mathbf{F}^{op}, \mathbf{Set})$ 等价于 $\mathbf{Set}$。

### 补充：在 Lean 里，模型就是解释器

对签名 `σ` 而言，一个模型只需要两样东西：载体 `carrier`（就是上面的 $a = M 1$），以及每个运算在载体上的解释。
其余的一切——$M n = a^n$、态射 $n \to m$ 怎么变成函数 $a^n \to a^m$——都由 `eval` 自动给出。我们先证明“求值与代入可交换”：

```lean
/-- 求值与代入可交换：先代入再求值 = 先把代入的项求值、再求值。 -/
theorem Term.eval_subst {σ : Signature} {α : Type}
    (interp : (o : σ.Op) → (Fin (σ.arity o) → α) → α) {m n : Nat}
    (s : Fin m → Term σ n) (env : Fin n → α) (t : Term σ m) :
    (t.subst s).eval interp env = t.eval interp (fun i => (s i).eval interp env) := by
  induction t with
  | var i => rfl
  | op o args ih =>
    simp only [Term.subst, Term.eval]
    congr
    funext i
    exact ih i

structure Model (σ : Signature) where
  carrier : Type
  interp  : (o : σ.Op) → (Fin (σ.arity o) → carrier) → carrier

/-- 每个模型都是一个函子 Syn σ ⥤ Type：n ↦ carrierⁿ，项的元组 ↦ 逐分量求值。 -/
def Model.toFunctor {σ : Signature} (M : Model σ) : CFunctor (Syn σ) Type where
  obj n := Fin (n : Nat) → M.carrier
  map ts := fun env i => (ts i).eval M.interp env
  map_id _ := rfl
  map_comp f g := by
    funext env i
    exact Term.eval_subst M.interp f env (g i)
```

函子定律在这里有非常朴素的含义：`map_id` 说“把每个变量求值，得到的就是环境本身”；`map_comp` 说“代入后再求值，等于先求值再代入”——
任何写过解释器的人都相信这件事，现在它被证明了。

`Model.toFunctor` 把对象 $n$ 送到 `Fin n → carrier`，也就是 $a^n$，所以它自动“在同构意义下保积”。
每个签名还都有一个平凡模型——载体是 `Unit`：

```lean
def trivialModel (σ : Signature) : Model σ := ⟨Unit, fun _ _ => ()⟩

/-- 在平凡模型里，任何两个项的值都相等，因此任何等式都成立。 -/
theorem trivialModel_satisfies {σ : Signature} {n : Nat} (t₁ t₂ : Term σ n) (env : Fin n → Unit) :
    t₁.eval (trivialModel σ).interp env = t₂.eval (trivialModel σ).interp env := rfl
```

模型之间的自然变换，就是程序员熟悉的**同态**（homomorphism）：一个保持每个运算的函数。
自然性条件对所有 $n$ 元运算 $f \colon n \to 1$ 都成立——在 Lean 里，就是“同态与任意项的求值可交换”：

```lean
structure ModelHom {σ : Signature} (M N : Model σ) where
  h    : M.carrier → N.carrier
  comm : ∀ o args, h (M.interp o args) = N.interp o (fun i => h (args i))

/-- 自然性：N f ∘ μₙ = μ₁ ∘ M f，对每个“n 元运算”（项）f 成立。 -/
theorem ModelHom.naturality {σ : Signature} {M N : Model σ} (φ : ModelHom M N)
    {n : Nat} (t : Term σ n) (env : Fin n → M.carrier) :
    t.eval N.interp (fun i => φ.h (env i)) = φ.h (t.eval M.interp env) := by
  induction t with
  | var i => rfl
  | op o args ih =>
    simp only [Term.eval]
    rw [φ.comm]
    congr
    funext i
    exact ih i
```

## 幺半群的理论

最简单的非平凡 Lawvere 理论描述的是幺半群的结构。它是**一个**理论，却提炼出了所有可能的幺半群的结构，
因为这个理论的模型铺满了整个幺半群范畴 $\mathbf{Mon}$。我们已经见过一个[泛构造](/part2/03-free-monoids)，
它表明每个幺半群都可以从某个合适的自由幺半群出发，通过认同一部分态射得到。所以单单一个自由幺半群就已经概括了大量的幺半群。
然而自由幺半群有无穷多个。幺半群的 Lawvere 理论 $\mathbf{L}_{\mathbf{Mon}}$ 用一个优雅的构造把它们全都结合在一起。

每个幺半群都必须有单位元，所以 $\mathbf{L}_{\mathbf{Mon}}$ 中必须有一个特殊的态射 $\eta$，从 $0$ 指向 $1$。
注意，$\mathbf{F}$ 中不可能有对应的态射。那样的态射方向相反，从 $1$ 到 $0$；在 $\mathbf{FinSet}$ 中，它会是一个从单元素集到空集的函数。
这样的函数不存在。（我们刚刚在 Lean 里证明过：`no_map_one_zero`。）

接下来，考虑态射 $2 \to 1$，也就是 $\mathbf{L}_{\mathbf{Mon}}(2, 1)$ 的成员，其中必须包含所有二元运算的原型。
在 $\mathbf{Mod}(\mathbf{L}_{\mathbf{Mon}}, \mathbf{Set})$ 中构造模型时，这些态射会被映成从笛卡尔积 $M 1 \times M 1$ 到 $M 1$ 的函数。换句话说，就是二元函数。

问题是：只用幺半群运算，能实现多少个二元函数？把两个参数叫作 $a$ 和 $b$。有一个函数忽略两个参数，返回幺半群单位元。
接着是两个投影，分别返回 $a$ 和 $b$。然后是返回 $ab$、$ba$、$aa$、$bb$、$aab$ 等等的函数……
实际上，这样的二元函数的个数，恰好与以 $a$ 和 $b$ 为生成元的自由幺半群的元素一样多。
注意，$\mathbf{L}_{\mathbf{Mon}}(2, 1)$ 必须包含所有这些态射，因为模型之一就是自由幺半群，而在自由幺半群里，它们对应的是互不相同的函数。
其他模型可能会把 $\mathbf{L}_{\mathbf{Mon}}(2, 1)$ 中的多个态射压缩成一个函数，但自由幺半群不会。

如果把有 $n$ 个生成元的自由幺半群记作 $n^*$，就可以把 hom-集 $\mathbf{L}(2, 1)$ 与幺半群范畴 $\mathbf{Mon}$ 中的 hom-集 $\mathbf{Mon}(1^*, 2^*)$ 认同起来。
一般地，我们取 $\mathbf{L}_{\mathbf{Mon}}(m, n)$ 为 $\mathbf{Mon}(n^*, m^*)$。换句话说，范畴 $\mathbf{L}_{\mathbf{Mon}}$ 是自由幺半群范畴的对偶。

::: info 数学小课堂：为什么 $\mathbf{Mon}(1^*, 2^*)$ 就是“二元运算”
$1^*$ 是一个生成元 $x$ 的自由幺半群（$x$ 的所有幂 $\varepsilon, x, xx, \dots$）。一个幺半群同态 $1^* \to 2^*$ 完全由“$x$ 被送到哪里”决定（这就是自由幺半群的泛性质），
而 $x$ 可以被送到 $2^*$ 中的任意一个词，例如 $aab$。所以 $\mathbf{Mon}(1^*, 2^*)$ 就是 $2^*$ 本身，即由 $a, b$ 组成的所有词——
每个词正好描述了一个二元函数：$(a, b) \mapsto aab$。
:::

幺半群 Lawvere 理论的**模型**范畴 $\mathbf{Mod}(\mathbf{L}_{\mathbf{Mon}}, \mathbf{Set})$ 等价于所有幺半群的范畴 $\mathbf{Mon}$。

### 补充：在 Lean 里验证“在所有幺半群中都成立”

现在让本章的 Lean 机器完整地跑一遍。幺半群的签名有两个运算：零元的 `unit` 和二元的 `mul`。

```lean
inductive MonOp
  | unit   -- 单位元 η : 0 → 1
  | mul    -- 乘法   μ : 2 → 1

@[reducible] def MonOp.arity : MonOp → Nat
  | .unit => 0
  | .mul  => 2

abbrev MonSig : Signature := ⟨MonOp, MonOp.arity⟩
```

::: tip Lean 深入：为什么要 `@[reducible]` 和 `abbrev`
稍后我们会写 `args 0`，其中 `args : Fin (MonSig.arity .mul) → …`。Lean 要把字面量 `0` 解释成 `Fin (MonSig.arity .mul)` 的元素，
就得先“看穿” `MonSig.arity .mul` 其实是 `2`。普通的 `def` 在类型类搜索时是不透明的；`abbrev`（以及 `@[reducible]`）告诉 Lean：这个定义可以随时展开。
:::

为了写起来舒服，再定义几个“智能构造子”和三个变量 `x y z`：

```lean
namespace MonTerm

def e {n : Nat} : Term MonSig n := .op MonOp.unit Fin.elim0
def mul {n : Nat} (a b : Term MonSig n) : Term MonSig n :=
  .op MonOp.mul (fun i => if i.val = 0 then a else b)

scoped infixl:70 " ⬝ " => mul

def x : Term MonSig 3 := .var 0
def y : Term MonSig 3 := .var 1
def z : Term MonSig 3 := .var 2

end MonTerm
```

幺半群的定律——它们是 $\mathbf{L}_{\mathbf{Mon}}$ 的“方程”——我们用一个类型类来表达，并给出三个模型：自然数加法、字符串拼接、布尔“与”。

```lean
class MonoidStr (α : Type) where
  one : α
  mul : α → α → α
  one_mul   : ∀ a, mul one a = a
  mul_one   : ∀ a, mul a one = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

instance : MonoidStr Nat    := ⟨0, (· + ·), Nat.zero_add, Nat.add_zero, Nat.add_assoc⟩
instance : MonoidStr String := ⟨"", (· ++ ·), fun _ => String.empty_append,
                                fun _ => String.append_empty, fun _ _ _ => String.append_assoc⟩
instance : MonoidStr Bool   := ⟨true, (· && ·), Bool.true_and, Bool.and_true, Bool.and_assoc⟩

/-- 幺半群给出 MonSig 的一个模型：unit ↦ one，mul ↦ mul。 -/
def MonoidStr.interp (α : Type) [MonoidStr α] : (o : MonSig.Op) → (Fin (MonSig.arity o) → α) → α
  | .unit, _    => MonoidStr.one
  | .mul,  args => MonoidStr.mul (args 0) (args 1)

def MonoidStr.model (α : Type) [MonoidStr α] : Model MonSig := ⟨α, MonoidStr.interp α⟩
```

试着求值：

```lean
/-- 一个 3 元组环境 (a, b, c) -/
def env3 {α : Type} (a b c : α) : Fin 3 → α
  | 0 => a
  | 1 => b
  | 2 => c

open MonTerm in
#guard ((x ⬝ y) ⬝ z).eval (MonoidStr.interp Nat) (env3 1 2 3) == 6
open MonTerm in
#guard ((x ⬝ y) ⬝ z).eval (MonoidStr.interp String) (env3 "ab" "c" "d") == "abcd"
open MonTerm in
#guard ((x ⬝ y) ⬝ z).eval (MonoidStr.interp Bool) (env3 true false true) == false

-- 交换律不是幺半群的定律：在字符串模型里 x ⬝ y 与 y ⬝ x 不同。
open MonTerm in
#guard (x ⬝ y).eval (MonoidStr.interp String) (env3 "a" "b" "") != (y ⬝ x).eval (MonoidStr.interp String) (env3 "a" "b" "")
```

`#guard` 会在编译时计算右边的布尔表达式，若结果不是 `true` 就报错——所以你在这里看到的“输出”，都是被机器检查过的。

现在来做本节的重头戏。上一段说 $\mathbf{L}_{\mathbf{Mon}}(n, 1)$ 就是 $n$ 个生成元的自由幺半群，也就是 `List (Fin n)`：
每个幺半群项都可以**压平**成一个变量序列（括号和单位元都消失了）。

```lean
/-- 范式：把幺半群项压平成自由幺半群中的一个词。 -/
def MonTerm.toList {n : Nat} : Term MonSig n → List (Fin n)
  | .var i            => [i]
  | .op .unit _       => []
  | .op .mul args     => toList (args 0) ++ toList (args 1)

open MonTerm in
#guard MonTerm.toList ((e ⬝ x) ⬝ (y ⬝ e) ⬝ z) == [0, 1, 2]
```

接着证明：在**任意**幺半群模型中，项的值等于“把它的范式中的变量按顺序乘起来”。

```lean
/-- 把一串元素用幺半群乘法乘起来（右结合）。 -/
def mconcat {α : Type} [MonoidStr α] : List α → α
  | []      => MonoidStr.one
  | a :: as => MonoidStr.mul a (mconcat as)

theorem mconcat_append {α : Type} [MonoidStr α] (l₁ l₂ : List α) :
    mconcat (l₁ ++ l₂) = MonoidStr.mul (mconcat l₁) (mconcat l₂) := by
  induction l₁ with
  | nil => simp [mconcat, MonoidStr.one_mul]
  | cons a as ih => simp [mconcat, ih, MonoidStr.mul_assoc]

/-- 核心定理：求值 = 范式的 mconcat。用到了结合律与单位律。 -/
theorem eval_eq_mconcat {α : Type} [MonoidStr α] {n : Nat} (env : Fin n → α) (t : Term MonSig n) :
    t.eval (MonoidStr.interp α) env = mconcat ((MonTerm.toList t).map env) := by
  induction t with
  | var i => simp [Term.eval, MonTerm.toList, mconcat, MonoidStr.mul_one]
  | op o args ih =>
    cases o with
    | unit => rfl
    | mul =>
      simp only [Term.eval, MonoidStr.interp, MonTerm.toList, List.map_append, mconcat_append]
      rw [ih 0, ih 1]

/-- 推论：范式相同的两个项，在所有幺半群模型中都相等。 -/
theorem eq_of_toList {n : Nat} (t₁ t₂ : Term MonSig n)
    (h : MonTerm.toList t₁ = MonTerm.toList t₂) :
    ∀ (α : Type) [MonoidStr α] (env : Fin n → α),
      t₁.eval (MonoidStr.interp α) env = t₂.eval (MonoidStr.interp α) env := by
  intro α _ env
  rw [eval_eq_mconcat, eval_eq_mconcat, h]
```

有了它，判断“某个等式是否在**所有**幺半群中成立”，就变成了比较两个列表——一个可以让计算机直接算的问题：

```lean
open MonTerm in
/-- (e·x)·(y·e)·z = x·(y·z) 在每一个幺半群中、对每一组取值都成立。 -/
theorem example_identity : ∀ (α : Type) [MonoidStr α] (env : Fin 3 → α),
    ((e ⬝ x) ⬝ (y ⬝ e) ⬝ z).eval (MonoidStr.interp α) env =
      (x ⬝ (y ⬝ z)).eval (MonoidStr.interp α) env :=
  eq_of_toList _ _ (by decide)
```

`by decide` 让 Lean 直接计算两边的 `toList` 并比较。我们一行代数推导都没写，却证明了一个关于**所有**幺半群（包括还没被发明出来的）的定理。
这正是 Lawvere 理论的精神：一个等式“在理论中成立”，就是在每一个模型中都成立；而“自由模型”（这里是 `List`）是最挑剔的那个——在它里面成立，就处处成立。

下面这个小组件把这一切做成了可以动手玩的东西。

<div class="ctfp-widget-host"><Ch3_14TermModels /></div>

## Lawvere 理论与单子

你也许还记得，代数理论可以用单子来描述——特别是[单子的代数](/part3/09-algebras-for-monads)。所以 Lawvere 理论与单子之间有联系，也就不奇怪了。

首先，我们来看一个 Lawvere 理论如何诱导出一个单子。它通过遗忘函子与自由函子之间的一个[伴随](/part3/03-free-forgetful-adjunctions)来做到这一点。
遗忘函子 $U$ 给每个模型指定一个集合：这个集合就是把 $\mathbf{Mod}(\mathbf{L}, \mathbf{Set})$ 中的函子 $M$ 在 $\mathbf{L}$ 的对象 $1$ 处求值的结果。

推导 $U$ 的另一种方式，是利用 $\mathbf{F}^{op}$ 是 $\mathbf{Law}$ 中的始对象这一事实。这意味着，对任何 Lawvere 理论 $\mathbf{L}$，都存在唯一一个函子 $\mathbf{F}^{op} \to \mathbf{L}$。
这个函子诱导出模型之间方向相反的函子（因为模型是**从**理论到集合的函子）：

$$\mathbf{Mod}(\mathbf{L}, \mathbf{Set}) \to \mathbf{Mod}(\mathbf{F}^{op}, \mathbf{Set})$$

而正如我们讨论过的，$\mathbf{F}^{op}$ 的模型范畴等价于 $\mathbf{Set}$，于是得到遗忘函子：

$$U \colon \mathbf{Mod}(\mathbf{L}, \mathbf{Set}) \to \mathbf{Set}$$

可以证明，这样定义的 $U$ 总有一个左伴随，即自由函子 $F$。

对有限集合来说，这一点很容易看出来。自由函子 $F$ 产生自由代数。自由代数是 $\mathbf{Mod}(\mathbf{L}, \mathbf{Set})$ 中一个特殊的模型，由一个有限生成元集合 $n$ 生成。
我们可以把 $F$ 实现为可表函子：

$$\mathbf{L}(n, -) \colon \mathbf{L} \to \mathbf{Set}$$

要说明它确实是自由的，只需证明它是遗忘函子的左伴随：

$$\mathbf{Mod}(\mathbf{L}, \mathbf{Set})(\mathbf{L}(n, -), M) \cong \mathbf{Set}(n, U(M))$$

先化简右边：

$$\mathbf{Set}(n, U(M)) \cong \mathbf{Set}(n, M 1) \cong (M 1)^n \cong M n$$

（这里用到了：态射的集合同构于指数对象，而在这里指数对象就是迭代的积。）于是这个伴随就是米田引理的结果：

$$[\mathbf{L}, \mathbf{Set}](\mathbf{L}(n, -), M) \cong M n$$

遗忘函子与自由函子一起，在 $\mathbf{Set}$ 上定义了一个[单子](/part3/06-monads-categorically) $T = U \circ F$。因此，每个 Lawvere 理论都生成一个单子。

事实证明，[这个单子的代数](/part3/09-algebras-for-monads)范畴等价于模型范畴。

你可能还记得，单子代数定义了对“用单子构成的表达式”求值的方式。Lawvere 理论定义了可以用来生成表达式的 $n$ 元运算，而模型提供了对这些表达式求值的手段。

::: tip Lean 深入：没有等式的理论，生成的就是“自由单子”
对 `Syn σ` 这种没有任何等式的理论，诱导出的单子 $T a$ 就是“变量取自 `a` 的项”。把 `Term σ n` 中的 `Fin n` 换成任意类型 `α`，就得到下面这个类型——
函数式程序员管它叫**自由单子**（free monad）。`bind` 恰好就是代入：

```lean
inductive Free (σ : Signature) (α : Type) where
  | pure : α → Free σ α
  | op   : (o : σ.Op) → (Fin (σ.arity o) → Free σ α) → Free σ α

def Free.bind {σ : Signature} {α β : Type} : Free σ α → (α → Free σ β) → Free σ β
  | .pure a,    k => k a
  | .op o args, k => .op o (fun i => (args i).bind k)

instance {σ : Signature} : Monad (Free σ) where
  pure := .pure
  bind := Free.bind

instance {σ : Signature} : LawfulMonad (Free σ) := LawfulMonad.mk'
  (id_map := by
    intro α t
    induction t with
    | pure a => rfl
    | op o args ih => show Free.op o _ = _; congr; funext i; exact ih i)
  (pure_bind := by intros; rfl)
  (bind_assoc := by
    intro α β γ t f g
    induction t with
    | pure a => rfl
    | op o args ih => show Free.op o _ = Free.op o _; congr; funext i; exact ih i)
```

`LawfulMonad.mk'` 只要求我们证明三条最核心的定律（`id_map`、`pure_bind`、`bind_assoc`），其余的由核心库推出。
单子定律在这里就是代入的单位律与结合律——与我们为 `Syn σ` 证明的范畴定律是同一回事。而有了等式（比如幺半群的理论），得到的单子就不再“自由”：
幺半群理论生成的单子是 `List`（见本章挑战）。
:::

不过，单子与 Lawvere 理论之间的联系并不是双向的。只有**有限型单子**（finitary monad）才能导出 Lawvere 理论。有限型单子基于有限型函子。
$\mathbf{Set}$ 上的**有限型函子**（finitary functor）完全由它在有限集合上的作用决定。它在任意集合 $a$ 上的作用，可以用下面的余端求出：

$$F a = \int^n a^n \times (F n)$$

由于余端推广了余积（也就是求和），这个公式是幂级数展开的一种推广。或者，我们可以借助“函子是一种广义容器”的直觉。
那样的话，一个装着 $a$ 的有限型容器可以描述为“形状”与“内容”的和。这里 $F n$ 是存放 $n$ 个元素的形状的集合，内容则是一个 $n$ 元组，本身是 $a^n$ 的一个元素。
例如，列表（作为函子）是有限型的，每种元数恰好对应一种形状。树在每种元数下有更多的形状，诸如此类。

::: tip Lean 深入：`List α` 就是 $\sum_n \alpha^n$
对列表来说，每个长度 $n$ 只有一种形状，所以 $\mathrm{List}\ a \cong \sum_n a^n \times 1$。在 Lean 里，“对 $n$ 求和”就是依值序对 `(n : Nat) × (Fin n → α)`（Σ 类型）：

```lean
def List.toSigma {α : Type} (l : List α) : (n : Nat) × (Fin n → α) := ⟨l.length, fun i => l[i]⟩
def List.ofSigma {α : Type} (p : (n : Nat) × (Fin n → α)) : List α := List.ofFn p.2

theorem List.ofSigma_toSigma {α : Type} (l : List α) : List.ofSigma (List.toSigma l) = l := by
  simp [List.ofSigma, List.toSigma]

#guard List.ofSigma ⟨3, triple⟩ == [10, 20, 30]
```

`(n : Nat) × (Fin n → α)` 读作“先选一个长度 `n`，再给出一个 `n` 元组”。（反方向的往返也成立，但要处理“长度相等”的类型转换，这里从略。）
:::

首先，所有由 Lawvere 理论生成的单子都是有限型的，并且都可以表示为余端：

$$T_{\mathbf{L}}\, a = \int^n a^n \times \mathbf{L}(n, 1)$$

反过来，给定 $\mathbf{Set}$ 上的任意有限型单子 $T$，我们可以构造一个 Lawvere 理论。先为 $T$ 构造一个 Kleisli 范畴。
你也许还记得，Kleisli 范畴中从 $a$ 到 $b$ 的态射，由底层范畴中的一个态射给出：

$$a \to T b$$

限制在有限集合上，它就变成：

$$m \to T n$$

这个 Kleisli 范畴的对偶 $\mathbf{Kl}^{op}_{T}$，限制在有限集合上，就是我们要找的 Lawvere 理论。
特别地，描述 $\mathbf{L}$ 中 $n$ 元运算的 hom-集 $\mathbf{L}(n, 1)$，由 hom-集 $\mathbf{Kl}_{T}(1, n)$ 给出。

事实证明，我们在编程中遇到的大多数单子都是有限型的，著名的例外是续体单子（continuation monad）。也可以把 Lawvere 理论的概念推广到有限型运算之外。

## 作为余端的单子

我们来更仔细地研究一下这个余端公式：

$$T_{\mathbf{L}}\, a = \int^n a^n \times \mathbf{L}(n, 1)$$

首先，这个余端是对 $\mathbf{F}$ 中的一个剖函子 $P$ 取的，其定义为：

$$P\, n\, m = a^n \times \mathbf{L}(m, 1)$$

这个剖函子在第一个参数 $n$ 上是逆变的。看看它是如何提升态射的。$\mathbf{FinSet}$ 中的一个态射是有限集合之间的映射 $f \colon m \to n$。
这样的映射描述的是从一个 $n$ 元集合中挑出 $m$ 个元素（允许重复）。它可以被提升为 $a$ 的幂之间的映射，也就是（注意方向）：

$$a^n \to a^m$$

这个提升只是从一个 $n$ 元组 $(a_1, a_2, \ldots, a_n)$ 中挑出 $m$ 个元素（可能有重复）。

![把 f 提升为幂之间的映射](/img/3.14/liftpower.png "下方：有限集合之间的函数 f : m → n；上方：它被提升为 a^n → a^m——从 n 元组中按 f 挑出 m 个分量（方向反过来了）。")

例如，取 $f_k \colon 1 \to n$——从 $n$ 元集合中选出第 $k$ 个元素。它被提升为一个函数：接受一个由 $a$ 中元素组成的 $n$ 元组，返回其中第 $k$ 个。

或者取 $f \colon m \to 1$——一个把全部 $m$ 个元素都映到同一处的常值函数。它的提升是一个函数：接受 $a$ 中的单个元素，把它复制 $m$ 次：

$$\lambda x \to (\underbrace{x, x, \ldots, x}_{m})$$

在 Lean 里，这个提升简单得出奇——就是函数复合（预复合）：

```lean
/-- 𝐅 中的 f : m → n 提升为 aⁿ → aᵐ：按 f 挑选分量。注意方向反了。 -/
def liftPow {α : Type} {m n : Nat} (f : Fin m → Fin n) (xs : Fin n → α) : Fin m → α :=
  fun i => xs (f i)

-- 选出第 k 个分量：f_k : 1 → n
#guard liftPow (fun (_ : Fin 1) => (2 : Fin 3)) triple 0 == 30
-- 复制：f : m → 1 是常值函数
#guard List.ofFn (liftPow (fun (_ : Fin 4) => (0 : Fin 1)) (fun _ => 7)) == [7, 7, 7, 7]
```

你也许注意到了，这个剖函子在第二个参数上是协变的，这一点并不是一眼就能看出来的。hom-函子 $\mathbf{L}(m, 1)$ 其实在 $m$ 上是逆变的。
然而，我们取余端不是在范畴 $\mathbf{L}$ 中，而是在范畴 $\mathbf{F}$ 中。余端变量 $n$ 遍历的是有限集合（或者说它们的骨架）。
范畴 $\mathbf{L}$ 包含了 $\mathbf{F}$ 的对偶，所以 $\mathbf{F}$ 中的态射 $m \to n$ 是 $\mathbf{L}$ 中 $\mathbf{L}(n, m)$ 的成员（这个嵌入由函子 $I_{\mathbf{L}}$ 给出）。

我们来检查 $\mathbf{L}(m, 1)$ 作为从 $\mathbf{F}$ 到 $\mathbf{Set}$ 的函子的函子性。我们想提升函数 $f \colon m \to n$，所以目标是实现一个从 $\mathbf{L}(m, 1)$ 到 $\mathbf{L}(n, 1)$ 的函数。
与函数 $f$ 相对应，$\mathbf{L}$ 中有一个从 $n$ 到 $m$ 的态射（注意方向）。把这个态射预复合到 $\mathbf{L}(m, 1)$ 上，就得到 $\mathbf{L}(n, 1)$ 的一个子集。

```diagram
Lm: (0, 0.3) "\mathbf{L}(m, 1)" shape=dot
Ln: (2.4, 0.3) "\mathbf{L}(n, 1)" shape=dot
m: (0, 1.3) "m" shape=dot
n: (2.4, 1.3) "n" shape=dot
lift: Lm -> Ln ""
f: m -> n "f" side=right
caption: F 中的 f : m → n 把 m 元运算变成 n 元运算（协变方向）。
```

在 `Syn σ` 中，这个提升就是**变量重命名**：把一个含 $m$ 个变量的项里的第 $i$ 个变量，改名为第 $f(i)$ 个变量。

```lean
/-- 𝐋(m,1) → 𝐋(n,1)：按 f 给变量改名（协变）。 -/
def Term.rename {σ : Signature} {m n : Nat} (f : Fin m → Fin n) (t : Term σ m) : Term σ n :=
  t.subst (fun i => .var (f i))
```

注意，通过提升一个函数 $1 \to n$，我们可以从 $\mathbf{L}(1, 1)$ 走到 $\mathbf{L}(n, 1)$。后面会用到这个事实。

逆变函子 $a^n$ 与协变函子 $\mathbf{L}(m, 1)$ 的积是一个剖函子 $\mathbf{F}^{op} \times \mathbf{F} \to \mathbf{Set}$。
记得余端可以定义为剖函子所有对角成员的余积（不交并），其中一些元素被认同在一起。这些认同对应于余楔条件。

在这里，余端一开始是所有 $n$ 上的集合 $a^n \times \mathbf{L}(n, 1)$ 的不交并。认同关系可以通过把[余端表示为余等化子](/part3/10-ends-and-coends)来生成。
我们从一个非对角项 $a^n \times \mathbf{L}(m, 1)$ 出发。要回到对角线，可以把态射 $f \colon m \to n$ 作用在积的第一个分量或第二个分量上。得到的两个结果被认同。

```diagram
top: (1.5, 0) "a^n \times \mathbf{L}(m, 1)"
left: (0.45, 1.8) "a^m \times \mathbf{L}(m, 1)"
right: (2.55, 1.8) "a^n \times \mathbf{L}(n, 1)"
l: top -> left "\langle f, \mathrm{id} \rangle" side=right
r: top -> right "\langle \mathrm{id}, f \rangle"
mid: (1.5, 1.8) "\sim"
caption: 余端的认同：同一个元素沿两种方式提升 f : m → n，得到的两个结果被视为相等。
```

这个认同为什么“合理”？因为在任何模型里，两边的求值结果都一样：先把元组按 $f$ 挑选、再对 $m$ 元运算求值，
与先把运算的变量按 $f$ 改名、再对原 $n$ 元组求值，是同一回事。Lean 可以证明这一点：

```lean
/-- 余楔条件在求值下成立：(xs, rename f t) 与 (liftPow f xs, t) 求值相同。 -/
theorem eval_rename {σ : Signature} {α : Type} (interp : (o : σ.Op) → (Fin (σ.arity o) → α) → α)
    {m n : Nat} (f : Fin m → Fin n) (xs : Fin n → α) (t : Term σ m) :
    (t.rename f).eval interp xs = t.eval interp (liftPow f xs) :=
  Term.eval_subst interp _ xs t
```

下面的组件让你亲手挑一个 $f \colon m \to n$，同时观察它的两种提升：对元组是“挑选分量”（逆变，$a^n \to a^m$），对运算是“给变量改名”（协变，$\mathbf{L}(m,1) \to \mathbf{L}(n,1)$）。

<div class="ctfp-widget-host"><Ch3_14FinLift /></div>

我之前说明过，提升 $f \colon 1 \to n$ 会得到这两个变换：

$$a^n \to a$$

和：

$$\mathbf{L}(1, 1) \to \mathbf{L}(n, 1)$$

因此，从 $a^n \times \mathbf{L}(1, 1)$ 出发，我们既能到达

$$a \times \mathbf{L}(1, 1)$$

（提升 $\langle f, \mathrm{id} \rangle$ 时），也能到达

$$a^n \times \mathbf{L}(n, 1)$$

（提升 $\langle \mathrm{id}, f \rangle$ 时）。然而，这并不意味着 $a^n \times \mathbf{L}(n, 1)$ 的所有元素都能与 $a \times \mathbf{L}(1, 1)$ 认同。
这是因为，并不是 $\mathbf{L}(n, 1)$ 的所有元素都能从 $\mathbf{L}(1, 1)$ 到达。记住，我们只能提升 $\mathbf{F}$ 中的态射。
$\mathbf{L}$ 中一个非平凡的 $n$ 元运算，无法通过提升一个态射 $f \colon 1 \to n$ 构造出来。

换句话说，我们只能把余端公式中这样的被加项全部认同：其中的 $\mathbf{L}(n, 1)$ 可以通过应用基本态射从 $\mathbf{L}(1, 1)$ 到达。它们全都等价于 $a \times \mathbf{L}(1, 1)$。
基本态射就是 $\mathbf{F}$ 中态射的像。

来看看这在最简单的 Lawvere 理论——$\mathbf{F}^{op}$ 本身——中是怎么运作的。在这个理论里，每个 $\mathbf{L}(n, 1)$ 都能从 $\mathbf{L}(1, 1)$ 到达。
这是因为 $\mathbf{L}(1, 1)$ 是只含恒等态射的单元素集，而 $\mathbf{L}(n, 1)$ 只包含与 $\mathbf{F}$ 中的内射 $1 \to n$ 相对应的态射，它们**正是**基本态射。
所以余积中的所有被加项都等价，我们得到：

$$T a = a \times \mathbf{L}(1, 1) = a$$

这就是恒等单子。

::: tip Lean 深入：没有运算的签名，自由单子就是恒等单子
取一个没有任何运算的签名（`Op := Empty`）。此时 `Free σ α` 中只剩下 `pure a` 这一种值，所以它与 `α` 同构——正是上面算出的 $T a = a$：

```lean
abbrev NoOpSig : Signature := ⟨Empty, Empty.elim⟩

def Free.unpure {α : Type} : Free NoOpSig α → α
  | .pure a => a
  | .op o _ => o.elim

theorem Free.pure_unpure {α : Type} (t : Free NoOpSig α) : Free.pure (Free.unpure t) = t := by
  cases t with
  | pure a => rfl
  | op o _ => exact o.elim
```
:::

## 副作用的 Lawvere 理论

既然单子与 Lawvere 理论之间有如此紧密的联系，人们自然会问：在编程中，Lawvere 理论能否作为单子的替代品？
单子的主要问题是它们不能很好地复合。构建单子变换器（monad transformer）没有通用的配方。Lawvere 理论在这方面有优势：它们可以用余积和张量积来复合。
另一方面，只有有限型单子才能方便地转换成 Lawvere 理论。这里的异类是续体单子。这一领域的研究仍在进行中（见参考文献）。

为了让你尝尝用 Lawvere 理论描述副作用的滋味，我来讨论一个简单的情形：异常。传统上，异常是用 `Maybe` 单子（Lean 中的 `Option`）实现的。

`Option` 单子由只含一个零元运算 $0 \to 1$ 的 Lawvere 理论生成。这个理论的一个模型是一个函子，它把 $1$ 映到某个集合 $a$，并把这个零元运算映到一个函数：

```lean
/-- 零元运算的解释：从 a⁰ = (Fin 0 → α) 到 a 的函数。
在任何 Lean 程序里，它的样子就是“抛出异常”。 -/
def raiseAt {α : Type} (r : α) : (Fin 0 → α) → α := fun _ => r
```

原书在 Haskell 中把它写成 `raise :: () -> a`。在 Lean 里，`Fin 0 → α` 和 `Unit` 一样都只有一个值，所以零元运算就是“载体中一个被选中的元素”——
在 `Option α` 这个模型里，它就是 `none`。

我们可以用余端公式重新得到 `Option` 单子。考虑加入这个零元运算会对 hom-集 $\mathbf{L}(n, 1)$ 产生什么影响。
除了在 $\mathbf{L}(0, 1)$ 中创造一个新元素（$\mathbf{F}^{op}$ 中没有它）之外，它还给 $\mathbf{L}(n, 1)$ 添加了新的态射：
它们是 $n \to 0$ 型的态射与我们的 $0 \to 1$ 复合的结果。在余端公式中，这些贡献全都与 $a^0 \times \mathbf{L}(0, 1)$ 认同，
因为它们可以从

$$a^n \times \mathbf{L}(0, 1)$$

出发，以两种不同方式提升 $0 \to n$ 而得到。

```diagram
top: (1.5, 0) "a^n \times \mathbf{L}(0, 1)"
left: (0.45, 1.8) "a^0 \times \mathbf{L}(0, 1)"
right: (2.55, 1.8) "a^n \times \mathbf{L}(n, 1)"
l: top -> left "\langle f, \mathrm{id} \rangle" side=right
r: top -> right "\langle \mathrm{id}, f \rangle"
mid: (1.5, 1.8) "\sim"
caption: f : 0 → n。所有“丢弃全部变量、然后抛出异常”的 n 元运算，都被认同为 a⁰ × L(0, 1) 中的那个唯一元素。
```

余端化简为：

$$T_{\mathbf{L}}\, a = a^0 + a^1$$

用 Lean 写就是：

```lean
abbrev MaybeViaSum (α : Type) := Unit ⊕ α
```

它等价于：

```lean no-check
inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α
```

（这是 Lean 核心库中 `Option` 的定义，这里只是展示，不重复定义。）我们可以在 Lean 里把整个故事验证一遍：
只有一个零元运算 `raise` 的签名，它的自由单子与 `Option` 同构。

```lean
inductive ExcOp | raise
abbrev ExcSig : Signature := ⟨ExcOp, fun _ => 0⟩

def Free.toOption {α : Type} : Free ExcSig α → Option α
  | .pure a => some a
  | .op _ _ => none

def Free.ofOption {α : Type} : Option α → Free ExcSig α
  | some a => .pure a
  | none   => .op .raise Fin.elim0

theorem Free.toOption_ofOption {α : Type} (o : Option α) : (Free.ofOption o).toOption = o := by
  cases o <;> rfl

theorem Free.ofOption_toOption {α : Type} (t : Free ExcSig α) : Free.ofOption t.toOption = t := by
  cases t with
  | pure a => rfl
  | op o args =>
    cases o
    simp only [Free.toOption, Free.ofOption]
    congr
    funext i
    exact i.elim0   -- 零元运算的参数元组只有一个：空元组
```

注意，这个 Lawvere 理论只支持**抛出**异常，不支持**处理**异常。

::: tip Rust 视角
Rust 的 `?` 运算符就是这里的 `raise`：遇到 `None`/`Err` 就“丢弃后续计算、直接返回”。而 `match` 一个 `Result` 并从错误中恢复，
是**处理**（handling）——它不是一个代数运算。原因在于：代数运算对后续计算是“透明”的（`op o args` 之后接上 `k`，等于把 `k` 接到每个 `args i` 后面，这就是 `Free.bind` 的定义），
而 `catch` 需要“看穿”整个子计算再决定怎么做，不满足这条规律。后来 Plotkin 与 Pretnar 提出的**效应处理器**（effect handler）正是为了处理这件事；
它们被 Koka、Eff、OCaml 5 等语言采用。
:::

### 补充：状态的代数表示

原书只讲了异常。再看一个程序员天天用的副作用：**状态**。Plotkin 与 Power 指出，状态单子同样来自一个 Lawvere 理论。
为了简单，设状态只有两种取值（`Bool`）。签名有两类运算：

- `lookup`：二元运算。它的两个参数是两段“后续程序”：当前状态为 `false` 时走第 0 个，为 `true` 时走第 1 个。（一般地，状态集合为 $S$ 时，`lookup` 的元数是 $|S|$。）
- `update b`：一元运算（每个 `b : Bool` 一个）。把状态设为 `b`，然后执行唯一的参数。

它们满足一组等式，例如：

- 连续两次写，只有后一次算数：`update b (update b' k) = update b' k`；
- 写完立刻读，读到的就是刚写的：`update b (lookup k₀ k₁) = update b k_b`；
- 读到什么就写回什么，等于什么都没做：`lookup (update false k) (update true k) = k`；

等等（完整的列表见 Plotkin 与 Power 的论文）。下面把这个签名写出来，并在 Lean 自带的 `StateM Bool` 中给出一个模型（解释器）：

```lean
inductive StOp
  | lookup
  | update (b : Bool)

@[reducible] def StOp.arity : StOp → Nat
  | .lookup   => 2
  | .update _ => 1

abbrev StSig : Signature := ⟨StOp, StOp.arity⟩

/-- 用状态单子解释状态理论的项（这就是一个“效应处理器”）。 -/
def runSt {α : Type} : Free StSig α → StateM Bool α
  | .pure a => pure a
  | .op .lookup k => do
      let s ← get
      runSt (k (if s then 1 else 0))
  | .op (.update b) k => do
      set b
      runSt (k 0)

/-- 一个小程序：读状态；若为 false 返回 10，否则把状态改成 false 并返回 20。 -/
def prog : Free StSig Nat :=
  .op .lookup fun i =>
    if i.val = 0 then .pure 10
    else .op (.update false) fun _ => .pure 20

#guard Id.run ((runSt prog).run true)  == (20, false)
#guard Id.run ((runSt prog).run false) == (10, false)
```

再验证一条等式在这个模型中成立：连续两次写，只有后一次算数。

```lean
theorem update_update {α : Type} (b b' : Bool) (k : Free StSig α) :
    runSt (.op (.update b) fun _ => .op (.update b') fun _ => k) =
      runSt (.op (.update b') fun _ => k) := rfl
```

这里 `rfl` 就够了：两边展开后都是“`set b'` 然后运行 `k`”（左边多出来的那个 `set b` 被后面的 `set b'` 覆盖，`StateM` 的定义让 Lean 能直接算出这一点）。

## 挑战

1. 列举 $\mathbf{F}$（$\mathbf{FinSet}$ 的骨架）中 $2$ 与 $3$ 之间的所有态射。
2. 证明：幺半群 Lawvere 理论的模型范畴，等价于列表单子的单子代数范畴。
3. 幺半群的 Lawvere 理论生成列表单子。证明它的二元运算可以用相应的 Kleisli 箭头生成。
4. $\mathbf{FinSet}$ 是 $\mathbf{Set}$ 的子范畴，有一个函子把它嵌入 $\mathbf{Set}$。$\mathbf{Set}$ 上的任何函子都可以限制到 $\mathbf{FinSet}$ 上。
   证明：有限型函子是它自身限制的左 Kan 扩张。

::: details 参考答案
**1.** $\mathbf{F}$ 中从 $m$ 到 $n$ 的态射就是函数 `Fin m → Fin n`，它由 $m$ 个取值决定，所以一共有 $n^m$ 个。
从 $2$ 到 $3$ 有 $3^2 = 9$ 个，从 $3$ 到 $2$ 有 $2^3 = 8$ 个。用一个“取值表”把它们全部列出来：

```lean
/-- 所有 Fin m → Fin n 的函数，表示为长度为 m 的取值表。 -/
def allMaps : (m n : Nat) → List (List (Fin n))
  | 0,     _ => [[]]
  | m + 1, n => (List.finRange n).flatMap fun i => (allMaps m n).map (i :: ·)

#guard allMaps 2 3 == [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2]]
#guard (allMaps 2 3).length == 9
#guard allMaps 3 2 == [[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1]]
#guard (allMaps 3 2).length == 8
```

例如取值表 `[2, 0]` 表示 $0 \mapsto 2,\ 1 \mapsto 0$。从 $2$ 到 $3$ 的 9 个态射里，有 6 个是单射（取值互不相同），3 个不是；从 $3$ 到 $2$ 的 8 个里，有 6 个是满射，2 个是常值函数。

**2.** 列表单子的代数是一个载体 $a$ 和一个求值函数 `alg : List a → a`，满足两条定律：`alg [x] = x`，以及“先拍平再求值 = 先逐个求值再求值”。
从幺半群出发，取 `alg := mconcat`；反过来，从代数出发，令单位元为 `alg []`、乘法为 `alg [x, y]`。下面证明两个方向都满足各自的定律：

```lean
structure ListAlg (α : Type) where
  alg      : List α → α
  alg_pure : ∀ a, alg [a] = a
  alg_join : ∀ ls : List (List α), alg ls.flatten = alg (ls.map alg)

def MonoidStr.toListAlg (α : Type) [MonoidStr α] : ListAlg α where
  alg := mconcat
  alg_pure a := by simp [mconcat, MonoidStr.mul_one]
  alg_join ls := by
    induction ls with
    | nil => rfl
    | cons l ls ih => simp [mconcat_append, mconcat, ih]

@[reducible] def ListAlg.toMonoid {α : Type} (A : ListAlg α) : MonoidStr α where
  one := A.alg []
  mul a b := A.alg [a, b]
  one_mul b := by
    have := A.alg_join [[], [b]]   -- alg [b] = alg [alg [], alg [b]]
    simp [A.alg_pure] at this
    exact this.symm
  mul_one a := by
    have := A.alg_join [[a], []]
    simp [A.alg_pure] at this
    exact this.symm
  mul_assoc a b c := by
    have h₁ := A.alg_join [[a, b], [c]]   -- alg [a,b,c] = alg [alg [a,b], c]
    have h₂ := A.alg_join [[a], [b, c]]   -- alg [a,b,c] = alg [a, alg [b,c]]
    simp [A.alg_pure] at h₁ h₂
    exact h₁.symm.trans h₂
```

要得到范畴的等价，还需验证：这两个构造互逆（`mconcat [x, y] = x * y`、`mconcat [] = 1`；反方向则用 `alg_join` 把任意列表拆成二元乘积），
并且幺半群同态恰好就是保持 `alg` 的函数（同态与 `mconcat` 可交换，由对列表归纳得到）。再结合本章的结论 $\mathbf{Mod}(\mathbf{L}_{\mathbf{Mon}}, \mathbf{Set}) \simeq \mathbf{Mon}$，就得到所求的等价。

**3.** 列表单子的 Kleisli 箭头 $1 \to \mathrm{List}\ 2$ 就是 `List (Fin 2)` 的一个元素——由两个变量组成的词。按本章的说法，$\mathbf{L}(2, 1) = \mathbf{Kl}_{\mathrm{List}}(1, 2)$。
具体地，每个词都对应一个项（`ofList`），每个项的范式又是一个词（`toList`），并且一来一回不变；在任何幺半群中，项的值都由它的词决定（`eval_eq_mconcat`）。
更妙的是，项的**代入**（$\mathbf{L}$ 中的复合）恰好对应列表的 `flatMap`（Kleisli 复合）：

```lean
def MonTerm.ofList {n : Nat} : List (Fin n) → Term MonSig n
  | []      => MonTerm.e
  | i :: is => MonTerm.mul (.var i) (ofList is)

theorem MonTerm.toList_ofList {n : Nat} (l : List (Fin n)) : toList (ofList l) = l := by
  induction l with
  | nil => rfl
  | cons i is ih => simp [ofList, MonTerm.mul, toList, ih]

/-- 𝐋 中的复合（代入）= Kleisli 复合（flatMap）。 -/
theorem MonTerm.toList_subst {m n : Nat} (s : Fin m → Term MonSig n) (t : Term MonSig m) :
    toList (t.subst s) = (toList t).flatMap (fun i => toList (s i)) := by
  induction t with
  | var i => simp [Term.subst, toList]
  | op o args ih =>
    cases o with
    | unit => rfl
    | mul => simp only [Term.subst, toList, List.flatMap_append, ih]

-- 二元运算 “a b a” 作为 Kleisli 箭头 1 → List 2：
#guard MonTerm.toList (MonTerm.ofList [0, 1, 0] : Term MonSig 2) == [0, 1, 0]
```

**4.** 设 $J \colon \mathbf{FinSet} \to \mathbf{Set}$ 为嵌入。左 Kan 扩张有余端公式

$$(\mathrm{Lan}_J (F \circ J))\, a = \int^{n} \mathbf{Set}(J n, a) \times F (J n)$$

而 $\mathbf{Set}(n, a) \cong a^n$，所以右边就是 $\int^n a^n \times F n$。按有限型函子的定义（它在任意集合上的作用由在有限集合上的作用通过这个余端给出），它等于 $F a$。
直观地说：$a$ 上的一个“有限型容器”里只装了有限多个元素，所以它总可以看成“某个有限集 $n$ 上的容器 + 一个 $n \to a$ 的标签函数”；
余端的认同关系恰好抹掉了“选哪个 $n$、怎么标号”的任意性。
:::

## 延伸阅读

1. [Functorial Semantics of Algebraic Theories](http://www.tac.mta.ca/tac/reprints/articles/5/tr5.pdf)，F. William Lawvere。
2. [Notions of computation determine monads](http://homepages.inf.ed.ac.uk/gdp/publications/Comp_Eff_Monads.pdf)，Gordon Plotkin 与 John Power。

## 本章小结

- **泛代数** = 一组 $n$ 元运算 + 一组全称量化的等式。幺半群、群、环都是；域不是（逆元律带条件）。
- 在 Lean 中，$a^n$ 就是 `Fin n → α`；`Fin n` 是标准的 $n$ 元有限集合，`Fin 0` 为空，因此 $a^0$ 只有一个元素（终对象）。
- 有限集合范畴的**骨架** $\mathbf{F}$ 以自然数为对象、以 `Fin m → Fin n` 为态射；余积就是加法。
- **Lawvere 理论**是一个范畴 $\mathbf{L}$ 加上一个对象上恒等、保积的函子 $I_{\mathbf{L}} \colon \mathbf{F}^{op} \to \mathbf{L}$。$\mathbf{F}$ 提供“无聊”的投影与复制，$\mathbf{L}$ 再添上“有趣”的运算。
- 程序员视角：签名 + 项构成一个 Lawvere 理论，**复合就是代入**；理论的**模型**是保积函子 $\mathbf{L} \to \mathbf{Set}$，也就是一个**解释器**；模型间的自然变换是**同态**。
- 幺半群理论中 $\mathbf{L}_{\mathbf{Mon}}(n, 1)$ 是 $n$ 个生成元的自由幺半群（`List (Fin n)`），所以“等式在所有幺半群中成立”可以通过比较范式来判定。
- 每个 Lawvere 理论通过自由/遗忘伴随生成一个**有限型单子** $T_{\mathbf{L}}\, a = \int^n a^n \times \mathbf{L}(n, 1)$；反过来，有限型单子的 Kleisli 范畴（限制到有限集合再取对偶）给出 Lawvere 理论。续体单子不是有限型的。
- 没有等式的理论生成**自由单子**，其 `bind` 就是代入；没有运算的理论生成恒等单子；一个零元运算生成 `Option`（只能抛出、不能处理异常）；`lookup`/`update` 生成状态单子。
