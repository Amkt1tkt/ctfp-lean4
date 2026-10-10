# 3.2 伴随

数学里有好几种方式来说“这个东西和那个东西差不多”。最严格的是**相等**：两样东西相等，意味着没有任何办法把它们区分开，
在一切可以想象的语境里，一个都可以替换另一个。比如，你有没有注意到，每次我们谈论交换图时，用的都是态射的**相等**（equality）？
这是因为态射构成一个集合（hom-集），而集合的元素是可以比较是否相等的。

但相等往往太强了。有许多东西在一切实际用途上都是“一样的”，却并不真的相等。比如，积类型 `Bool × Char` 并不严格等于 `Char × Bool`，
但我们明白它们装着同样的信息。这个概念最好用两个类型之间的**同构**（isomorphism）来刻画——一个可逆的态射。
因为它是态射，所以它保持结构；而“同构”的“同”，意味着它是一趟往返旅程的一半：无论你从哪一边出发，绕一圈回来都落在原地。
对积来说，这个同构叫作 `swap`：

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

end CTFP

open CTFP

set_option linter.unusedSectionVars false
```

```lean
def swap {α β : Type} : α × β → β × α
  | (a, b) => (b, a)

-- swap 恰好是它自己的逆
theorem swap_swap {α β : Type} (p : α × β) : swap (swap p) = p := rfl
```

`swap` 恰好是它自己的逆。

## 伴随与单位/余单位对

当我们说两个范畴同构时，用的是范畴之间的映射，也就是函子。我们希望能这样说：范畴 $\mathcal{C}$ 和 $\mathcal{D}$ 同构，
如果存在一个从 $\mathcal{C}$ 到 $\mathcal{D}$ 的函子 $R$（“右”），并且它可逆。换句话说，存在另一个从 $\mathcal{D}$ 回到 $\mathcal{C}$ 的函子 $L$（“左”），
它和 $R$ 复合之后等于恒等函子 $I$。复合有两种可能，$R \circ L$ 和 $L \circ R$；恒等函子也有两个：$\mathcal{C}$ 上的一个，$\mathcal{D}$ 上的一个。

![两个范畴之间来回的函子](/img/3.2/adj-1.jpg "函子 R 从 C 到 D，函子 L 从 D 回到 C。")

但棘手之处来了：两个函子**相等**是什么意思？下面这个等式：

$$R \circ L = I_{\mathcal{D}}$$

或者这一个：

$$L \circ R = I_{\mathcal{C}}$$

究竟是什么意思？用对象的相等来定义函子的相等，似乎很合理：两个函子作用在相等的对象上，应该产生相等的对象。
可是，一般的范畴里并没有“对象相等”这个概念——它根本不是范畴定义的一部分。（如果沿着“相等到底是什么”这个兔子洞一直往下钻，
我们最终会掉进同伦类型论（Homotopy Type Theory）。）

::: tip Lean 深入：Lean 里的类型相等
在 Lean 中，`Bool × Char = Char × Bool` 这个命题是可以写出来的，但你既证明不了它，也否定不了它——Lean 的核心理论对“两个类型是否相等”
基本保持沉默。实践中我们从不依赖类型相等，而是构造同构（就像 `swap`）。这正好印证了本节的观点：对象之间，**同构**才是有用的“相同”。
:::

你也许会反驳说，函子**就是**范畴的范畴中的态射，所以它们应该可以比较相等。确实，只要我们讨论的是小范畴（对象构成一个集合），
就可以借用集合元素的相等来比较对象。

但是别忘了，$\mathbf{Cat}$ 其实是一个 2-范畴。2-范畴中的 hom-集带有额外的结构——在 1-态射之间还有 2-态射。在 $\mathbf{Cat}$ 中，
1-态射是函子，2-态射是自然变换。所以，在讨论函子时，用自然同构来代替相等要更**自然**一些（这个双关实在躲不开！）。

于是，与其谈论范畴的同构，不如考虑一个更一般的概念：**等价**（equivalence）。两个范畴 $\mathcal{C}$ 和 $\mathcal{D}$ 是**等价**的，
如果我们能找到两个在它们之间来回的函子，它们的复合（无论哪个顺序）都**自然同构**（naturally isomorphic）于恒等函子。
换句话说，在复合 $R \circ L$ 与恒等函子 $I_{\mathcal{D}}$ 之间有一个双向的自然变换，在 $L \circ R$ 与恒等函子 $I_{\mathcal{C}}$ 之间也有一个。

伴随比等价还要弱，因为它不要求两个函子的复合**同构**于恒等函子。它只要求存在一个从 $I_{\mathcal{D}}$ 到 $R \circ L$ 的**单向**自然变换，
以及另一个从 $L \circ R$ 到 $I_{\mathcal{C}}$ 的单向自然变换。这两个自然变换的签名是：

$$\eta :: I_{\mathcal{D}} \to R \circ L$$

$$\varepsilon :: L \circ R \to I_{\mathcal{C}}$$

$\eta$ 叫作伴随的**单位**（unit），$\varepsilon$ 叫作伴随的**余单位**（counit）。

注意这两个定义之间的不对称。一般而言，我们**没有**另外两个方向的映射：

$$R \circ L \to I_{\mathcal{D}} \qquad \text{（不一定有）}$$

$$I_{\mathcal{C}} \to L \circ R \qquad \text{（不一定有）}$$

正因为这种不对称，函子 $L$ 被称为函子 $R$ 的**左伴随**（left adjoint），而 $R$ 则是 $L$ 的**右伴随**（right adjoint）。
（当然，“左”和“右”只有在你按某种特定方式画图时才有意义。）

伴随的简洁记法是：

$$L \dashv R$$

::: info 数学小课堂：等价、同构、伴随——一个强弱阶梯
设想你要比较两个范畴，从强到弱有三档：

| 关系 | 要求 |
|---|---|
| 同构 | $R \circ L$ 和 $L \circ R$ **等于**恒等函子 |
| 等价 | $R \circ L$ 和 $L \circ R$ **自然同构**于恒等函子（两个方向都有，而且互逆） |
| 伴随 | 只要一个 $\eta : I \to R \circ L$ 和一个 $\varepsilon : L \circ R \to I$（各自只朝一个方向），外加两条“三角恒等式” |

越往下越弱，例子也越多。伴随弱到在数学和编程里随处可见，却又强到能推出大量结论（比如每个伴随都给出一个单子）。
:::

为了更好地理解伴随，我们来仔细分析单位和余单位。

![单位](/img/3.2/adj-unit.jpg "单位 η：从 D 中任意对象 d 出发，射出一支箭到 d' = (R ∘ L) d。")

先看单位。它是一个自然变换，所以它是一族态射。给定 $\mathcal{D}$ 中的对象 $d$，$\eta$ 的分量是一个从 $I d$（就是 $d$）到 $(R \circ L) d$
（图中称为 $d'$）的态射：

$$\eta_d :: d \to (R \circ L) d$$

注意，复合 $R \circ L$ 是 $\mathcal{D}$ 上的一个自函子。

这个式子告诉我们：可以从 $\mathcal{D}$ 中任选一个对象 $d$ 作为起点，用“往返”函子 $R \circ L$ 选出目标对象 $d'$，然后射出一支箭——
态射 $\eta_d$——到达目标。

![余单位](/img/3.2/adj-counit.jpg "余单位 ε：在 C 中任选目标 c，用 L ∘ R 选出起点 c' = (L ∘ R) c，再射一支箭回 c。")

同理，余单位 $\varepsilon$ 的分量可以描述为：

$$\varepsilon_c :: (L \circ R) c \to c$$

它告诉我们：可以在 $\mathcal{C}$ 中任选一个对象 $c$ 作为目标，用往返函子 $L \circ R$ 选出起点 $c' = (L \circ R) c$，
然后从起点向目标射出一支箭——态射 $\varepsilon_c$。

看待单位和余单位的另一种方式是：单位让我们在任何可以插入 $\mathcal{D}$ 上恒等函子的地方，**引入**复合 $R \circ L$；
余单位让我们**消去**复合 $L \circ R$，把它换成 $\mathcal{C}$ 上的恒等函子。由此引出一些“显然”的一致性条件，确保先引入、再消去，什么也不会改变：

$$L = L \circ I_{\mathcal{D}} \to L \circ R \circ L \to I_{\mathcal{C}} \circ L = L$$

$$R = I_{\mathcal{D}} \circ R \to R \circ L \circ R \to R \circ I_{\mathcal{C}} = R$$

它们叫作**三角恒等式**（triangular identities），因为它们让下面两张图交换：

```diagram
L1: (0, 0) "L"
LRL: (2.3, 0) "LRL"
L2: (2.3, 1.6) "L"
Leta: L1 => LRL "L \circ \eta"
epsL: LRL => L2 "\varepsilon \circ L"
idL: L1 => L2 "\mathrm{id}_L" side=right
path "先 L∘η 再 ε∘L": Leta epsL
path "什么都不做": idL color=green
caption: 第一条三角恒等式：(ε ∘ L) · (L ∘ η) = id_L。图中 LRL 是 L ∘ R ∘ L 的简写。
```

```diagram
R1: (0, 0) "R"
RLR: (2.3, 0) "RLR"
R2: (2.3, 1.6) "R"
etaR: R1 => RLR "\eta \circ R"
Reps: RLR => R2 "R \circ \varepsilon"
idR: R1 => R2 "\mathrm{id}_R" side=right
path "先 η∘R 再 R∘ε": etaR Reps
path "什么都不做": idR color=green
caption: 第二条三角恒等式：(R ∘ ε) · (η ∘ R) = id_R。图中 RLR 是 R ∘ L ∘ R 的简写。
```

这些是函子范畴里的图：箭头是自然变换，而它们的复合是自然变换的水平复合（这里是自然变换与函子的“须复合”）。
写成分量，这两条恒等式变成：

$$\varepsilon_{L d} \circ L \eta_d = \mathrm{id}_{L d}$$

$$R \varepsilon_c \circ \eta_{R c} = \mathrm{id}_{R c}$$

::: info 数学小课堂：读懂分量形式
第一条：从 $L d$ 出发。先用 $L$ 把 $\eta_d : d \to R(L d)$ 提升成 $L \eta_d : L d \to L(R(L d))$；
再用余单位在对象 $L d$ 处的分量 $\varepsilon_{L d} : L(R(L d)) \to L d$ 回到原地。结论：绕这一圈等于什么都没做。

第二条：从 $R c$ 出发。先用单位在 $R c$ 处的分量 $\eta_{R c} : R c \to R(L(R c))$；再用 $R$ 提升余单位
$R\varepsilon_c : R(L(R c)) \to R c$ 回到原地。同样，绕一圈等于什么都没做。

记忆诀窍：$\eta$ 负责“插入一对 $R L$”，$\varepsilon$ 负责“拿掉一对 $L R$”。在 $L$ 后面插入再拿掉，或在 $R$ 前面插入再拿掉，都等于没动。
:::

在编程中，我们常常以别的名字见到单位和余单位。单位就是 `pure`（Haskell 中叫 `return`，也是 `Applicative` 定义中的 `pure`）：

```lean no-check
pure : d → m d
```

余单位则是 `extract`：

```lean no-check
extract : w c → c
```

这里，`m` 是对应于 $R \circ L$ 的（自）函子，`w` 是对应于 $L \circ R$ 的（自）函子。我们以后会看到，它们分别是单子（monad）和
余单子（comonad）定义的一部分。Lean 核心库有 `Pure` 和 `Monad`，但没有 `Comonad`；我们会在 [3.7 余单子](/part3/07-comonads) 里自己定义它。

如果把自函子想象成容器，那么单位（或 `pure`）就是一个多态函数，它在任意类型的值外面套上一个“默认的盒子”。余单位（或 `extract`）
则做相反的事：从容器里取出（或者生产出）一个值。

```lean
-- 把 3 装进默认的盒子
example : (pure 3 : Option Nat) = some 3 := rfl
example : (pure 3 : Except String Nat) = .ok 3 := rfl
```

我们以后会看到，每一对伴随函子都定义了一个单子和一个余单子。反过来，每个单子或余单子都可以分解成一对伴随函子——
不过这种分解不是唯一的。

在 Haskell 中，人们大量使用单子，却很少把它们分解成伴随函子对，主要是因为那些函子通常会把我们带出 **Hask**（Haskell 类型的范畴）。
Lean 也是一样：`StateM`、`Option` 用起来很顺手，没人会先去构造它们背后的伴随。

不过，我们**可以**在 Lean 中定义**自函子**（endofunctor）之间的伴随。Haskell 的库 `Data.Functor.Adjunction` 用一个多参数类型类来定义它；
在 Lean 里，最清楚的写法是一个**结构体**，把单位、余单位以及它们必须满足的定律统统放进字段里：

```lean
/-- Type 上两个自函子之间的伴随 L ⊣ R（单位/余单位版本）。 -/
structure Adjunction (L R : Type → Type) [Functor L] [Functor R] where
  /-- 单位 η_d : d → R (L d) -/
  unit   : {d : Type} → d → R (L d)
  /-- 余单位 ε_c : L (R c) → c -/
  counit : {c : Type} → L (R c) → c
  /-- η 是自然变换：(R ∘ L) h ∘ η = η ∘ h -/
  unit_natural : ∀ {d d' : Type} (h : d → d') (x : d),
    Functor.map (Functor.map h) (unit x) = unit (h x)
  /-- ε 是自然变换：k ∘ ε = ε ∘ (L ∘ R) k -/
  counit_natural : ∀ {c c' : Type} (k : c → c') (y : L (R c)),
    k (counit y) = counit (Functor.map (Functor.map k) y)
  /-- 三角恒等式一：ε_{L d} ∘ L η_d = id -/
  left_triangle : ∀ {d : Type} (x : L d),
    counit (Functor.map unit x) = x
  /-- 三角恒等式二：R ε_c ∘ η_{R c} = id -/
  right_triangle : ∀ {c : Type} (y : R c),
    Functor.map counit (unit y) = y
```

这个定义需要解释几句。

- 结构体以两个**类型构造子** `L R : Type → Type` 为参数，`[Functor L] [Functor R]` 要求它们都是函子（方括号是**实例参数**，Lean 会自动去找）。
  它确立了 `L` 和 `R` 之间一种叫作 `Adjunction` 的关系。一个 `Adjunction L R` 类型的值，就是“$L \dashv R$ 的一份证据”。
- `{d : Type}` 是**隐式参数**：使用 `unit x` 时，Lean 会从 `x` 的类型推断出 `d`，你不用写出来。这让 `unit` 读起来就像一个多态函数。
- 前两个字段是“数据”，后四个字段是“定律”。数据字段的类型是 `Type`，定律字段的类型是 `Prop`（一个命题）——构造一个 `Adjunction`，
  就得同时给出函数和证明。这是 Lean 比 Haskell 强的地方：Haskell 的类型类只能在文档里**嘱咐**你遵守定律，而 Lean 的结构体**要求**你证明它们。

::: tip Lean 深入：函数依赖与 `outParam`
Haskell 的定义是 `class (Functor f, Representable u) => Adjunction f u | f -> u, u -> f`。竖线后面的 `f -> u, u -> f` 是**函数依赖**
（functional dependencies）：`f -> u` 表示“知道了 `f` 就能唯一确定 `u`”（`f` 与 `u` 之间的关系是一个函数，这里是类型构造子上的函数），
反之 `u -> f` 表示知道了 `u` 就能确定 `f`。

Lean 的类型类里，类似的效果用 `outParam` 实现：

```lean no-check
class IsLeftAdjoint (L : Type → Type) (R : outParam (Type → Type))
    [Functor L] [Functor R] where
  adj : Adjunction L R
```

`outParam` 告诉实例搜索：“`R` 是输出，请根据 `L` 把它找出来”。我们这里用结构体而非类型类，是因为同一对函子可以有不同的伴随证据，
而且显式地传来传去更利于讲解。
:::

稍后我会解释，为什么在 Haskell 中可以要求右伴随 `u` 是一个**可表**（representable）函子。

## 伴随与 hom-集

伴随还有一个等价的定义，用的是 hom-集的自然同构。这个定义和我们一直在研究的泛构造衔接得非常好。每当你听到“存在某个唯一的态射，
它分解了某个构造”这样的说法时，你都应该把它想成“某个集合到一个 hom-集的映射”。这就是“挑出一个唯一的态射”的含义。

进一步说，分解往往可以用自然变换来描述。分解涉及交换图——某个态射等于两个态射（因子）的复合。而自然变换把态射映成交换图。
所以，在一个泛构造中，我们从一个态射走到一张交换图，再走到一个唯一的态射。最后得到的是一个从态射到态射的映射，
或者说，从一个 hom-集到另一个 hom-集的映射（通常在不同的范畴里）。如果这个映射可逆，而且可以自然地推广到所有的 hom-集，
我们就得到了一个伴随。

泛构造与伴随的主要区别在于，后者是**全局**定义的——针对所有 hom-集。例如，用泛构造，你可以为两个**特定**的对象定义积，
哪怕该范畴中其他的对象对都没有积。我们很快会看到，如果一个范畴中**任意一对**对象都有积，那么积也可以通过伴随来定义。

![伴随的 hom-集定义](/img/3.2/adj-homsets.jpg "hom-集定义：C 中的 hom-集 C(L d, c) 与 D 中的 hom-集 D(d, R c) 一一对应。")

下面是用 hom-集给出的伴随的另一个定义。和之前一样，我们有两个函子 $L :: \mathcal{D} \to \mathcal{C}$ 和 $R :: \mathcal{C} \to \mathcal{D}$。
我们任取两个对象：$\mathcal{D}$ 中的起点对象 $d$，以及 $\mathcal{C}$ 中的终点对象 $c$。可以用 $L$ 把起点对象 $d$ 映到 $\mathcal{C}$ 中。
现在 $\mathcal{C}$ 中有了两个对象 $L d$ 和 $c$，它们确定了一个 hom-集：

$$\mathcal{C}(L d, c)$$

类似地，可以用 $R$ 把终点对象 $c$ 映过去。现在 $\mathcal{D}$ 中有了两个对象 $d$ 和 $R c$，它们也确定了一个 hom-集：

$$\mathcal{D}(d, R c)$$

我们说 $L$ 是 $R$ 的左伴随，当且仅当存在一个 hom-集的同构：

$$\mathcal{C}(L d, c) \cong \mathcal{D}(d, R c)$$

并且它对 $d$ 和 $c$ 都是自然的。

自然性意味着，起点 $d$ 可以在 $\mathcal{D}$ 中平滑地变化，终点 $c$ 可以在 $\mathcal{C}$ 中平滑地变化。更精确地说，在下面两个
从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的（协变）函子之间，有一个自然变换 $\varphi$。这两个函子在对象上的作用是：

$$c \to \mathcal{C}(L d, c)$$

$$c \to \mathcal{D}(d, R c)$$

另一个自然变换 $\psi$，作用在下面两个（逆变）函子之间：

$$d \to \mathcal{C}(L d, c)$$

$$d \to \mathcal{D}(d, R c)$$

这两个自然变换都必须可逆。

::: info 数学小课堂：“对 d 和 c 都自然”到底在要求什么
把同构记作 $\varphi_{d,c} : \mathcal{C}(L d, c) \to \mathcal{D}(d, R c)$。“自然”说的是它和复合相容，具体有两条：

- **在 $c$ 上自然**：对任意 $k : c \to c'$，在左边先后接 $k$ 再过 $\varphi$，等于先过 $\varphi$ 再在右边后接 $R k$：
  $$\varphi(k \circ f) = R k \circ \varphi(f)$$
- **在 $d$ 上自然**：对任意 $h : d' \to d$，在左边先前接 $L h$ 再过 $\varphi$，等于先过 $\varphi$ 再在右边前接 $h$：
  $$\varphi(f \circ L h) = \varphi(f) \circ h$$

直观地说：“改终点”和“改起点”这两种操作，都能顺畅地穿过这个一一对应。它不是随手配的对，而是“结构化”的配对。
（一个同构对某个变量自然，它的逆对同一个变量也自然；所以只检查一个方向就够了。）
:::

::: warning 易错点
原书把 $\varphi$ 和 $\psi$ 说成两个自然变换：一个强调“对 $c$ 自然”，一个强调“对 $d$ 自然”。实际上它们是**同一族**映射
$\mathcal{C}(L d, c) \cong \mathcal{D}(d, R c)$ 分别从两个变量的角度去看。编程里则习惯把这个同构的两个**方向**分别命名：
从左到右叫 `leftAdjunct`，从右到左叫 `rightAdjunct`。下面的 Lean 定义就采用这种说法。
:::

在动手证明之前，先“看见”这个同构。取 $L = (\cdot \times \mathrm{Bool})$、$R = (\mathrm{Bool} \to \cdot)$、$c = \mathrm{Bool}$：
左边是所有 `d × Bool → Bool` 的函数，右边是所有 `d → (Bool → Bool)` 的函数。（我们在本章最后一节会证明这的确是一个伴随。）

<Ch3_2HomSetBijection />

很容易证明，伴随的两种定义是等价的。比如，我们从 hom-集的同构出发推导出单位变换：

$$\mathcal{C}(L d, c) \cong \mathcal{D}(d, R c)$$

既然这个同构对任何对象 $c$ 都成立，那么它对 $c = L d$ 也必须成立：

$$\mathcal{C}(L d, L d) \cong \mathcal{D}(d, (R \circ L) d)$$

我们知道左边至少包含一个态射：恒等态射。自然变换会把这个态射映到 $\mathcal{D}(d, (R \circ L) d)$ 中的一个元素，或者插入恒等函子 $I$ 后写成

$$\mathcal{D}(I d, (R \circ L) d)$$

中的一个态射。我们得到了一族以 $d$ 为参数的态射。它们构成了从函子 $I$ 到函子 $R \circ L$ 的一个自然变换（自然性条件很容易验证）。
这恰恰就是我们的单位 $\eta$。

反过来，从单位和余单位的存在出发，我们可以定义 hom-集之间的变换。例如，在 hom-集 $\mathcal{C}(L d, c)$ 中任取一个态射 $f$。
我们想定义一个 $\varphi$，它作用在 $f$ 上，产生 $\mathcal{D}(d, R c)$ 中的一个态射。

其实没有太多选择。我们能尝试的一件事是用 $R$ 提升 $f$。这会得到一个从 $R (L d)$ 到 $R c$ 的态射 $R f$——它是
$\mathcal{D}((R \circ L) d, R c)$ 的一个元素。

而 $\varphi$ 的一个分量需要的是一个从 $d$ 到 $R c$ 的态射。这不成问题，因为我们可以先用分量 $\eta_d$ 从 $d$ 走到 $(R \circ L) d$。于是得到：

$$\varphi_f = R f \circ \eta_d$$

另一个方向与此类似，$\psi$ 的推导也一样。

```diagram
d: (0, 0) "d"
RLd: (2, 0) "R(L\,d)"
Rc: (2, 1.5) "R\,c"
eta: d -> RLd "\eta_d"
Rf: RLd -> Rc "R f"
phif: d -> Rc "\varphi_f" side=right
path "先 η_d 再 R f": eta Rf
path "φ_f": phif color=green
caption: 从单位得到 hom-集映射：φ_f = R f ∘ η_d。
```

回到 Haskell 对 `Adjunction` 的定义：自然变换 $\varphi$ 和 $\psi$ 被替换成了对 `a`、`b` 多态的函数 `leftAdjunct` 和 `rightAdjunct`。
在 Lean 中，我们同样把它写成一个结构体，并把“互逆”和“自然”作为定律字段：

```lean
/-- Type 上两个自函子之间的伴随 L ⊣ R（hom-集版本）。 -/
structure HomAdjunction (L R : Type → Type) [Functor L] [Functor R] where
  /-- φ : C(L d, c) → D(d, R c) -/
  leftAdjunct  : {d c : Type} → (L d → c) → (d → R c)
  /-- φ⁻¹ : D(d, R c) → C(L d, c) -/
  rightAdjunct : {d c : Type} → (d → R c) → (L d → c)
  /-- 两个方向互逆 -/
  right_left : ∀ {d c : Type} (f : L d → c), rightAdjunct (leftAdjunct f) = f
  left_right : ∀ {d c : Type} (g : d → R c), leftAdjunct (rightAdjunct g) = g
  /-- 对 c 自然：φ(k ∘ f) = R k ∘ φ f -/
  natural_c : ∀ {d c c' : Type} (k : c → c') (f : L d → c),
    leftAdjunct (k ∘ f) = Functor.map k ∘ leftAdjunct f
  /-- 对 d 自然：φ(f ∘ L h) = φ f ∘ h -/
  natural_d : ∀ {d' d c : Type} (h : d' → d) (f : L d → c),
    leftAdjunct (f ∘ Functor.map h) = leftAdjunct f ∘ h
```

单位/余单位的表述与 `leftAdjunct`/`rightAdjunct` 的表述之间的等价，由下面这些映射见证：

```lean no-check
unit           = leftAdjunct id
counit         = rightAdjunct id
leftAdjunct f  = Functor.map f ∘ unit
rightAdjunct g = counit ∘ Functor.map g
```

把伴随的范畴论描述一步步翻译成代码，是非常有启发的练习，我强烈推荐你亲自做一遍。在 Lean 里，我们可以做得更彻底：
不仅写出这些映射，还**证明**由此得到的东西满足全部定律。下面就是“两种定义可以互相导出”的完整证明。
它对 Type 上任意一对守法的自函子都成立，不只是某个具体例子。

```lean
variable {L R : Type → Type} [Functor L] [Functor R]
  [LawfulFunctor L] [LawfulFunctor R]

/-- 单位/余单位 ⟹ hom-集同构 -/
def Adjunction.toHom (A : Adjunction L R) : HomAdjunction L R where
  leftAdjunct f  := Functor.map f ∘ A.unit
  rightAdjunct g := A.counit ∘ Functor.map g
  right_left f := by
    funext x
    simp only [Function.comp_apply]
    -- ε (L (R f ∘ η) x) = ε (L R f (L η x)) = f (ε (L η x)) = f x
    rw [comp_map, ← A.counit_natural, A.left_triangle]
  left_right g := by
    funext x
    simp only [Function.comp_apply]
    -- R (ε ∘ L g) (η x) = R ε (R L g (η x)) = R ε (η (g x)) = g x
    rw [comp_map, A.unit_natural, A.right_triangle]
  natural_c k f := by
    funext x
    simp only [Function.comp_apply, comp_map]   -- R (k ∘ f) = R k ∘ R f
  natural_d h f := by
    funext x
    simp only [Function.comp_apply]
    rw [comp_map, A.unit_natural]               -- η 的自然性
```

::: details 另一个方向：hom-集同构 ⟹ 单位/余单位（完整证明）
先证明一个小引理：`rightAdjunct` 作为 `leftAdjunct` 的逆，也自动是自然的。

```lean
theorem HomAdjunction.natural_c' (H : HomAdjunction L R) {d c c' : Type}
    (k : c → c') (g : d → R c) :
    H.rightAdjunct (Functor.map k ∘ g) = k ∘ H.rightAdjunct g := by
  have := H.natural_c k (H.rightAdjunct g)
  rw [H.left_right] at this     -- this : φ(k ∘ φ⁻¹ g) = R k ∘ g
  rw [← this, H.right_left]     -- φ⁻¹(φ(…)) = …

theorem HomAdjunction.natural_d' (H : HomAdjunction L R) {d' d c : Type}
    (h : d' → d) (g : d → R c) :
    H.rightAdjunct (g ∘ h) = H.rightAdjunct g ∘ Functor.map h := by
  have := H.natural_d h (H.rightAdjunct g)
  rw [H.left_right] at this
  rw [← this, H.right_left]

/-- hom-集同构 ⟹ 单位/余单位：η = φ id，ε = φ⁻¹ id -/
def HomAdjunction.toAdj (H : HomAdjunction L R) : Adjunction L R where
  unit   := H.leftAdjunct id
  counit := H.rightAdjunct id
  unit_natural h x := by
    have e1 := H.natural_c (Functor.map h) (id : L _ → L _)
    have e2 := H.natural_d h (id : L _ → L _)
    show (Functor.map (Functor.map h) ∘ H.leftAdjunct id) x
      = (H.leftAdjunct id ∘ h) x
    rw [← e1, ← e2]
    rfl
  counit_natural k y := by
    have e1 := H.natural_c' k (id : R _ → R _)
    have e2 := H.natural_d' (Functor.map k) (id : R _ → R _)
    show (k ∘ H.rightAdjunct id) y
      = (H.rightAdjunct id ∘ Functor.map (Functor.map k)) y
    rw [← e1, ← e2]
    rfl
  left_triangle x := by
    show (H.rightAdjunct id ∘ Functor.map (H.leftAdjunct id)) x = x
    rw [← H.natural_d', Function.id_comp, H.right_left]
    rfl
  right_triangle y := by
    show (Functor.map (H.rightAdjunct id) ∘ H.leftAdjunct id) y = y
    rw [← H.natural_c, Function.comp_id, H.left_right]
    rfl
```

最后确认这两个构造确实互逆：从 hom-集版本出发，转成单位/余单位再转回来，得到的 `leftAdjunct` 和原来的一样；
从单位/余单位出发绕一圈，单位也不变。

```lean
theorem toAdj_toHom_left (H : HomAdjunction L R) {d c : Type} (f : L d → c) :
    H.toAdj.toHom.leftAdjunct f = H.leftAdjunct f := by
  show Functor.map f ∘ H.leftAdjunct id = _
  rw [← H.natural_c, Function.comp_id]

theorem toHom_toAdj_unit (A : Adjunction L R) {d : Type} (x : d) :
    A.toHom.toAdj.unit x = A.unit x := by
  show Functor.map id (A.unit x) = A.unit x
  rw [id_map]
```
:::

::: tip Lean 深入：`variable`、`show` 与 `rw [← …]`
- `variable {L R : Type → Type} [Functor L] …` 声明了一组“本节公共参数”。之后的定义只要用到 `L`、`R`，就会自动把它们（及所需实例）加为参数，省得每次重写。
- `show t` 把当前目标换成一个与之**定义上相等**的写法 `t`。这里常用它把 `f (g x)` 改写成 `(f ∘ g) x` 的样子，好让后面的 `rw` 匹配得上。
- `rw [h]` 用等式 `h : a = b` 把目标中的 `a` 改写成 `b`；`rw [← h]` 则反过来，把 `b` 改写成 `a`。
:::

现在可以解释，为什么在 Haskell 中，右伴随自动是一个[可表函子](/part2/04-representable-functors)了。原因在于，作为一阶近似，
我们可以把 Haskell 类型的范畴当作集合范畴。

当右边的范畴 $\mathcal{D}$ 是 $\mathbf{Set}$ 时，右伴随 $R$ 是一个从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的函子。如果能在 $\mathcal{C}$ 中找到一个对象 $\mathit{rep}$，
使得 hom-函子 $\mathcal{C}(\mathit{rep}, -)$ 自然同构于 $R$，那么这个函子就是可表的。事实证明，如果 $R$ 是某个从 $\mathbf{Set}$ 到 $\mathcal{C}$ 的
函子 $L$ 的右伴随，那么这样的对象总是存在——它就是单元素集合 $()$ 在 $L$ 下的像：

$$\mathit{rep} = L\, ()$$

确实，伴随告诉我们，下面两个 hom-集是自然同构的：

$$\mathcal{C}(L\, (), c) \cong \mathbf{Set}((), R c)$$

对给定的 $c$，右边是从单元素集合 $()$ 到 $R c$ 的函数的集合。我们早先见过，每个这样的函数都恰好从集合 $R c$ 中挑出一个元素。
这些函数构成的集合同构于集合 $R c$。于是有：

$$\mathcal{C}(L\, (), -) \cong R$$

这说明 $R$ 确实是可表的。

::: info 数学小课堂：“从单元素集合出发的函数 = 一个元素”
单元素集合 $() = \{\star\}$ 只有一个元素。一个函数 $x : () \to S$ 唯一要决定的，就是 $x(\star)$ 是 $S$ 的哪个元素。
所以“函数 $() \to S$”和“$S$ 的元素”一一对应。在 Lean 中，这就是 `fun x => x ()` 和 `fun s => fun _ => s` 这一对互逆函数。
:::

## 由伴随得到积

我们之前用泛构造引入过好几个概念。其中许多概念，一旦在全局意义下定义，用伴随来表达会更容易。最简单的非平凡例子就是积。
[积的泛构造](/part1/05-products-and-coproducts)的要义，是任何“像积的”候选者都能通过泛积来分解。

更准确地说，两个对象 $a$ 和 $b$ 的积是对象 $a \times b$（Lean 中写作 `a × b`），它配备两个态射 $\mathit{fst}$ 和 $\mathit{snd}$，
使得对于任何其他配备了两个态射 $p : c \to a$ 和 $q : c \to b$ 的候选者 $c$，都存在唯一的态射 $m : c \to a \times b$，
它通过 $\mathit{fst}$ 和 $\mathit{snd}$ 分解 $p$ 和 $q$。

我们早先见过，可以实现一个 `factorizer`，由两个投影生成这个态射：

```lean
def factorizer {c a b : Type} (p : c → a) (q : c → b) : c → a × b :=
  fun x => (p x, q x)
```

很容易验证分解条件成立——在 Lean 里，“很容易”意味着 `rfl`：

```lean
example {c a b : Type} (p : c → a) (q : c → b) :
    Prod.fst ∘ factorizer p q = p := rfl
example {c a b : Type} (p : c → a) (q : c → b) :
    Prod.snd ∘ factorizer p q = q := rfl
```

我们有一个映射：它接收一对态射 `p` 和 `q`，产生另一个态射 `m = factorizer p q`。

怎样把它翻译成定义伴随所需要的两个 hom-集之间的映射呢？诀窍是跳出 **Type**，把这一对态射当作**积范畴**中的单个态射。

我来提醒你一下什么是积范畴。任取两个范畴 $\mathcal{C}$ 和 $\mathcal{D}$。积范畴 $\mathcal{C} \times \mathcal{D}$ 中的对象是对象对，一个来自 $\mathcal{C}$，
一个来自 $\mathcal{D}$。态射则是态射对，一个来自 $\mathcal{C}$，一个来自 $\mathcal{D}$。

要在某个范畴 $\mathcal{C}$ 中定义积，我们应该从积范畴 $\mathcal{C} \times \mathcal{C}$ 出发。来自 $\mathcal{C}$ 的一对态射，就是积范畴 $\mathcal{C} \times \mathcal{C}$ 中的单个态射。

![积范畴](/img/3.2/adj-productcat.jpg "积范畴 C × C：对象是对象对，态射是态射对。")

```lean
/-- 积范畴 Type × Type：对象是一对类型，态射是一对函数。三条定律都是 rfl。 -/
instance prodCat : Category (Type × Type) where
  Hom p q := (p.1 → q.1) × (p.2 → q.2)
  id _ := (fun x => x, fun y => y)
  comp g f := (fun x => g.1 (f.1 x), fun y => g.2 (f.2 y))
```

一开始你可能有点困惑：我们居然用积范畴来定义积。但这是两种非常不同的积。定义积范畴并不需要泛构造，
我们只需要“一对对象”和“一对态射”的概念。

然而，来自 $\mathcal{C}$ 的一对对象**不是** $\mathcal{C}$ 中的对象。它是另一个范畴 $\mathcal{C} \times \mathcal{C}$ 中的对象。我们可以把这对对象形式地记作
$\langle a, b \rangle$，其中 $a$ 和 $b$ 是 $\mathcal{C}$ 中的对象。另一方面，要定义对象 $a \times b$（Lean 中的 `a × b`），就必须用到泛构造——
它是**同一个**范畴 $\mathcal{C}$ 中的对象。这个对象应该按泛构造所规定的方式，“代表”对子 $\langle a, b \rangle$。它不一定存在；
即使对某些对象对存在，对 $\mathcal{C}$ 中的其他对象对也可能不存在。

::: tip Lean 深入：两种“积”在 Lean 里一目了然
`(Nat, Bool) : Type × Type` 是积范畴的一个**对象**——一对类型，它本身不是类型，你不能拿它来声明变量。
而 `Nat × Bool : Type` 是 **Type** 中的一个对象——一个真正的类型，它的元素是 `(3, true)` 这样的对子。
注意 `(Nat, Bool)` 用的是逗号（构造一个对子），`Nat × Bool` 用的是 `×`（类型构造子 `Prod`）。
:::

现在来把 `factorizer` 看成 hom-集之间的映射。第一个 hom-集在积范畴 $\mathcal{C} \times \mathcal{C}$ 中，第二个在 $\mathcal{C}$ 中。
$\mathcal{C} \times \mathcal{C}$ 中一般的态射是一对态射 $\langle f, g \rangle$：

$$f :: c' \to a$$

$$g :: c'' \to b$$

其中 $c''$ 可能与 $c'$ 不同。但是为了定义积，我们感兴趣的是 $\mathcal{C} \times \mathcal{C}$ 中一种特殊的态射：起点对象相同的那一对 $p$ 和 $q$。
这没问题：在伴随的定义中，左边 hom-集的起点不是随便哪个对象——它是左函子 $L$ 作用于右边范畴中某个对象的结果。
符合要求的函子很容易猜到——就是从 $\mathcal{C}$ 到 $\mathcal{C} \times \mathcal{C}$ 的**对角函子** $\Delta$，它在对象上的作用是：

$$\Delta c = \langle c, c \rangle$$

```lean
/-- 对角函子 Δ : Type → Type × Type -/
def diag : CFunctor Type (Type × Type) where
  obj c := (c, c)
  map f := (f, f)
  map_id _ := rfl
  map_comp _ _ := rfl
```

因此，我们伴随中左边的 hom-集应该是：

$$(\mathcal{C} \times \mathcal{C})(\Delta c, \langle a, b \rangle)$$

这是积范畴中的一个 hom-集。它的元素是一对态射，我们认得出它们正是 `factorizer` 的参数：

$$(c \to a) \to (c \to b) \to \ldots$$

右边的 hom-集位于 $\mathcal{C}$ 中，它在起点对象 $c$ 与某个函子 $R$ 作用于 $\mathcal{C} \times \mathcal{C}$ 中终点对象的结果之间。
这个函子就是把对子 $\langle a, b \rangle$ 映到我们的积对象 $a \times b$ 的那个函子。我们认得出，这个 hom-集的元素正是 `factorizer` 的**结果**：

$$\ldots \to (c \to a \times b)$$

![积作为伴随](/img/3.2/adj-product.jpg "积作为对角函子的右伴随：(C×C)(Δc, ⟨a, b⟩) ≅ C(c, a×b)。")

```lean
/-- 积函子 Product : Type × Type → Type，⟨a, b⟩ ↦ a × b -/
def product : CFunctor (Type × Type) Type where
  obj p := p.1 × p.2
  map f := fun x => (f.1 x.1, f.2 x.2)
  map_id _ := rfl
  map_comp _ _ := rfl
```

但我们还没有得到一个完整的伴随。为此，首先需要 `factorizer` 可逆——我们要构建的是 hom-集之间的**同构**。`factorizer` 的逆
应该从一个态射 $m$ 出发——一个从某个对象 $c$ 到积对象 $a \times b$ 的态射。换句话说，$m$ 应该是下面这个集合的元素：

$$\mathcal{C}(c, a \times b)$$

逆 factorizer 应该把 $m$ 映到 $\mathcal{C} \times \mathcal{C}$ 中一个从 $\langle c, c \rangle$ 到 $\langle a, b \rangle$ 的态射 $\langle p, q \rangle$；换句话说，映到下面这个集合的元素：

$$(\mathcal{C} \times \mathcal{C})(\Delta c, \langle a, b \rangle)$$

如果这个映射存在，我们就可以断定对角函子有右伴随。这个函子定义了积。

在 Lean 中，我们总能构造 `factorizer` 的逆：把 `m` 分别与 `Prod.fst` 和 `Prod.snd` 复合即可。

```lean no-check
p = Prod.fst ∘ m
q = Prod.snd ∘ m
```

为了把它写成一个真正的同构，我们先定义一个小小的“同构”结构体（Lean 核心库里没有现成的 `Equiv`）：

```lean
/-- 两个类型之间的同构：一对互逆的函数。 -/
structure Iso (α β : Type u) where
  to : α → β
  inv : β → α
  inv_to : ∀ x, inv (to x) = x
  to_inv : ∀ y, to (inv y) = y

infix:25 " ≅ " => Iso

/-- 积是对角函子的右伴随：(C×C)(Δc, ⟨a,b⟩) ≅ C(c, a×b) -/
def prodAdj (c : Type) (ab : Type × Type) :
    (diag.obj c ⟶ ab) ≅ (c ⟶ product.obj ab) where
  -- factorizer
  to pq := fun x => (pq.1 x, pq.2 x)
  -- 逆 factorizer：分别后接 fst、snd
  inv m := (fun x => (m x).1, fun x => (m x).2)
  inv_to _ := rfl
  to_inv _ := rfl
```

要完成“两种定义积的方式等价”的证明，我们还需要证明这个 hom-集之间的映射对 $a$、$b$ 和 $c$ 都是自然的。我把这个留给有毅力的读者做练习。

::: details 有毅力的读者：自然性的 Lean 证明
对 $c$ 自然：沿 $h : c' \to c$ 前复合（在左边是前复合 $\Delta h = \langle h, h \rangle$）。
对 $\langle a, b \rangle$ 自然：沿积范畴中的态射 $k = \langle k_1, k_2 \rangle$ 后复合（在右边是后复合 $\mathit{Product}\, k$）。
两件事可以一并写成一个等式，而 Lean 只用 `rfl` 就能确认它：

```lean
theorem prodAdj_natural (c' c : Type) (ab ab' : Type × Type)
    (h : c' ⟶ c) (k : ab ⟶ ab') (pq : diag.obj c ⟶ ab) :
    (prodAdj c' ab').to (k ⊚ pq ⊚ diag.map h)
      = product.map k ⊚ (prodAdj c ab).to pq ⊚ h := rfl
```
:::

总结一下我们所做的事：范畴论意义上的积，可以在全局意义下定义为对角函子的**右伴随**（right adjoint）：

$$(\mathcal{C} \times \mathcal{C})(\Delta c, \langle a, b \rangle) \cong \mathcal{C}(c, a \times b)$$

这里，$a \times b$ 是我们的右伴随函子 $\mathit{Product}$ 作用于对子 $\langle a, b \rangle$ 的结果。注意，任何从 $\mathcal{C} \times \mathcal{C}$ 出发的函子都是一个双函子，
所以 $\mathit{Product}$ 是一个双函子。在 Lean 中，$\mathit{Product}$ 双函子就是 `Prod`（中缀写作 `×`）。你可以把它应用到两个类型上，得到它们的积类型，例如：

```lean
example : Prod Nat Bool = (Nat × Bool) := rfl
example : product.obj (Nat, Bool) = (Nat × Bool) := rfl
```

## 由伴随得到指数

指数 $b^a$，或者说函数对象 $a \Rightarrow b$，可以用[泛构造](/part1/09-function-types)来定义。如果这个构造对所有对象对都存在，
它就可以看作一个伴随。诀窍同样是抓住这句陈述：

> 对任何其他带有态射 $g :: z \times a \to b$ 的对象 $z$，都存在唯一的态射 $h :: z \to (a \Rightarrow b)$。

这句陈述建立了 hom-集之间的一个映射。

在这里，我们处理的是同一个范畴中的对象，所以两个伴随函子都是自函子。左（自）函子 $L$ 作用在对象 $z$ 上，产生 $z \times a$。
它对应于“和某个固定的 $a$ 取积”。

右（自）函子 $R$ 作用在 $b$ 上，产生函数对象 $a \Rightarrow b$（或 $b^a$）。同样，$a$ 是固定的。这两个函子之间的伴随通常写作：

$$- \times a \dashv (-)^a$$

把我们在泛构造中用过的那张图重新画一遍，就最能看清这个伴随背后的 hom-集映射。

![指数作为伴随](/img/3.2/adj-expo.jpg "指数作为伴随：C(z × a, b) ≅ C(z, a ⇒ b)；eval 就是余单位。")

注意，$\mathit{eval}$ 态射（见 [1.9 函数类型](/part1/09-function-types) 中的泛构造）不是别的，正是这个伴随的余单位：

$$(a \Rightarrow b) \times a \to b$$

其中：

$$(a \Rightarrow b) \times a = (L \circ R)\, b$$

```diagram
za: (0, 0) "z \times a"
expa: (0, 1.6) "(a \Rightarrow b) \times a"
b: (2.4, 1.6) "b"
z: (-1.8, 0) "z"
ex: (-1.8, 1.6) "a \Rightarrow b"
hid: za --> expa "h \times \mathrm{id}" side=right
g: za -> b "g"
ev: expa -> b "\mathit{eval}" side=right
h: z --> ex "h" side=right
path "g": g
path "eval ∘ (h × id)": hid ev color=green
caption: 指数的泛性质：任意 g 都唯一地分解为 eval ∘ (h × id)。左边的 h 与右边的 g 一一对应——这就是 hom-集同构。
```

现在用 Lean 把它完整地写出来。我们需要两个自函子：`Pair a`（即 `(· × a)`）和 `Expo a`（即 `(a → ·)`）。

```lean
/-- 左伴随 L z = z × a -/
def Pair (a : Type) (z : Type) : Type := z × a
/-- 右伴随 R b = a → b -/
def Expo (a : Type) (b : Type) : Type := a → b

instance (a : Type) : Functor (Pair a) where
  map f p := (f p.1, p.2)            -- 只改第一个分量
instance (a : Type) : Functor (Expo a) where
  map f g := f ∘ g                   -- 后复合

instance (a : Type) : LawfulFunctor (Pair a) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
instance (a : Type) : LawfulFunctor (Expo a) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

::: tip Lean 深入：为什么不直接写 `Functor (· × a)`
`(· × a)` 是一个 lambda 表达式 `fun z => z × a`。Lean 的实例搜索按“头部符号”来索引实例，而 lambda 没有一个稳定的头部，
所以给它注册实例会让类型推断找不到它。给它起个名字（`def Pair a z := z × a`），问题就消失了。
因为 `def` 默认不会被实例搜索展开，`Pair a z` 和 `z × a` 在定义上相等，却拥有各自独立的实例。
:::

伴随本身：单位把 `z` 变成“等着接收一个 `a` 的对子”，余单位就是 `eval`——把函数作用在参数上。全部六条定律都是 `rfl`：

```lean
/-- 柯里化伴随：(· × a) ⊣ (a → ·) -/
def curryAdj (a : Type) : Adjunction (Pair a) (Expo a) where
  unit z := fun x => (z, x)          -- η_z : z → (a → z × a)
  counit p := p.1 p.2                -- ε_b = eval : (a → b) × a → b
  unit_natural _ _ := rfl
  counit_natural _ _ := rfl
  left_triangle _ := rfl             -- eval (fun x => (z, x), y) = (z, y)
  right_triangle _ := rfl            -- fun x => eval (g, x) = g
```

由此得到的 hom-集同构，正是柯里化与反柯里化：

```lean
example (a z c : Type) (f : z × a → c) :
    (curryAdj a).toHom.leftAdjunct f = Function.curry f := rfl

example (a z c : Type) (g : z → a → c) :
    (curryAdj a).toHom.rightAdjunct g = Function.uncurry g := by
  funext ⟨x, y⟩   -- 把输入对子拆成 (x, y)
  rfl
```

::: tip Rust 视角
在 Rust 里，柯里化就是在 `Fn((Z, A)) -> B` 与 `Fn(Z) -> impl Fn(A) -> B` 之间来回转换：

```rust
fn curry<Z, A, B, F>(f: F) -> impl Fn(Z) -> Box<dyn Fn(A) -> B>
where
    Z: Clone + 'static,
    A: 'static,
    B: 'static,
    F: Fn((Z, A)) -> B + Clone + 'static,
{
    move |z: Z| {
        let f = f.clone();
        Box::new(move |a: A| f((z.clone(), a)))
    }
}

fn uncurry<Z, A, B, G: Fn(A) -> B>(g: impl Fn(Z) -> G) -> impl Fn((Z, A)) -> B {
    move |(z, a)| g(z)(a)
}
```

Rust 需要 `Clone`、`Box<dyn …>` 和 `'static` 之类的生命周期约束，才能把“返回一个闭包”表达出来；而在 Lean 里，`z → a → c` 与 `z × a → c`
之间的转换是零成本的 `rfl`。伴随说的是：这两种写法装着**完全相同的信息**，而且这种对应与复合相容。
:::

这个伴随还免费送给我们一个单子和一个余单子。往返函子 $R \circ L$ 把 $z$ 送到 `a → z × a`——这正是 **State 单子**！
单位就是 State 单子的 `pure`：

```lean
-- R ∘ L 就是 State 单子
example (s z : Type) : Expo s (Pair s z) = StateM s z := rfl
-- 单位 η 就是 StateM 的 pure
example (s z : Type) (x : z) : (pure x : StateM s z) = (curryAdj s).unit x := rfl
```

另一个往返函子 $L \circ R$ 把 $b$ 送到 `(a → b) × a`，余单位 `eval` 从中取出一个值——这是 **Store 余单子**。
我们会在 [3.4 单子：程序员的定义](/part3/04-monads-programmers-definition)、[3.5 单子与副作用](/part3/05-monads-and-effects)
和 [3.7 余单子](/part3/07-comonads) 中再见到它们。

我之前提到过，泛构造在同构意义下定义了唯一的对象。这就是为什么我们说“**那个**”积、“**那个**”指数。这个性质也可以搬到伴随上：
如果一个函子有伴随，那么这个伴随在同构意义下是唯一的。

## 挑战

1. 推导 $\psi$ 的自然性方块。$\psi$ 是下面两个（逆变）函子之间的变换：

   $$a \to \mathcal{C}(L a, b)$$

   $$a \to \mathcal{D}(a, R b)$$

2. 从伴随的第二个定义（hom-集同构）出发，推导出余单位 $\varepsilon$。
3. 完成伴随两种定义等价性的证明。
4. 证明余积可以用伴随来定义。从余积的 factorizer 的定义开始。
5. 证明余积是对角函子的左伴随。
6. 用 Lean 定义积与函数对象之间的伴随。

::: details 参考答案 1：ψ 的自然性方块
对 $\mathcal{D}$ 中任意态射 $h : a' \to a$，两个逆变函子分别作用为“在左边前接 $L h$”和“在右边前接 $h$”。自然性方块是：

```diagram
CLa: (0, 0) "\mathcal{C}(L a, b)"
CLa2: (3, 0) "\mathcal{C}(L a', b)"
DaR: (0, 1.6) "\mathcal{D}(a, R b)"
DaR2: (3, 1.6) "\mathcal{D}(a', R b)"
top: CLa -> CLa2 "- \circ L h"
bot: DaR -> DaR2 "- \circ h" side=right
psi: CLa -> DaR "\psi_a" side=right
psi2: CLa2 -> DaR2 "\psi_{a'}"
path "先 ψ_a 再前接 h": psi bot
path "先前接 L h 再 ψ_{a'}": top psi2 color=green
caption: ψ 的自然性：ψ_{a'}(f ∘ L h) = ψ_a(f) ∘ h。
```

也就是说，对任意 $f : L a \to b$，有 $\psi_{a'}(f \circ L h) = \psi_a(f) \circ h$。在 Lean 中，这正是 `HomAdjunction` 的字段 `natural_d`；
而它的逆方向（从右到左）的自然性，就是我们证明的 `HomAdjunction.natural_d'`。
:::

::: details 参考答案 2：从 hom-集同构推导余单位
与推导单位对称。同构对任意 $d$ 都成立，所以取 $d = R c$：

$$\mathcal{C}(L(R c), c) \cong \mathcal{D}(R c, R c)$$

右边至少有一个元素：恒等态射 $\mathrm{id}_{R c}$。把它沿同构的逆方向送回左边，得到 $\varepsilon_c : (L \circ R) c \to c$。
即 $\varepsilon_c = \varphi^{-1}(\mathrm{id}_{R c})$。它对 $c$ 的自然性来自同构的自然性。这正是上面 `HomAdjunction.toAdj` 中的
`counit := H.rightAdjunct id` 以及 `counit_natural` 的证明。
:::

::: details 参考答案 3：两种定义的等价
本章正文里的 `Adjunction.toHom` 与 `HomAdjunction.toAdj` 就是完整的证明：前者从单位/余单位与三角恒等式出发，构造出互逆且自然的
`leftAdjunct`/`rightAdjunct`；后者从自然同构出发，构造出单位与余单位，并证明它们的自然性与两条三角恒等式。
`toAdj_toHom_left` 与 `toHom_toAdj_unit` 则说明这两个构造互逆。全部证明都被 Lean 检查过。
:::

::: details 参考答案 4、5：余积是对角函子的左伴随
余积的 factorizer 接收两个**汇聚**到同一个 $c$ 的态射，产生一个从余积出发的态射：

```lean
def coFactorizer {a b c : Type} (i : a → c) (j : b → c) : a ⊕ b → c
  | .inl x => i x
  | .inr y => j y
```

这一次，“同一个 $c$”出现在**终点**上：一对态射 $\langle i, j \rangle$ 是积范畴中从 $\langle a, b \rangle$ 到 $\Delta c = \langle c, c \rangle$ 的态射。
所以对角函子这次出现在右边，余积是它的**左**伴随：

$$\mathcal{C}(a + b, c) \cong (\mathcal{C} \times \mathcal{C})(\langle a, b \rangle, \Delta c)$$

```lean
/-- 余积函子 Coproduct : Type × Type → Type，⟨a, b⟩ ↦ a ⊕ b -/
def coproduct : CFunctor (Type × Type) Type where
  obj p := p.1 ⊕ p.2
  map f := Sum.map f.1 f.2
  map_id _ := by funext s; cases s <;> rfl
  map_comp _ _ := by funext s; cases s <;> rfl

/-- 余积 ⊣ 对角：C(a ⊕ b, c) ≅ (C×C)(⟨a,b⟩, Δc) -/
def coprodAdj (ab : Type × Type) (c : Type) :
    (coproduct.obj ab ⟶ c) ≅ (ab ⟶ diag.obj c) where
  to m := (fun x => m (.inl x), fun y => m (.inr y))   -- 分别前接两个内射
  inv ij := coFactorizer ij.1 ij.2                       -- 余积的 factorizer
  inv_to m := by funext s; cases s <;> rfl
  to_inv _ := rfl

/-- 自然性：对 ⟨a,b⟩ 前复合、对 c 后复合，都能穿过这个同构 -/
theorem coprodAdj_natural (ab' ab : Type × Type) (c c' : Type)
    (h : ab' ⟶ ab) (k : c ⟶ c') (m : coproduct.obj ab ⟶ c) :
    (coprodAdj ab' c').to (k ⊚ m ⊚ coproduct.map h)
      = diag.map k ⊚ (coprodAdj ab c).to m ⊚ h := rfl
```

对照一下：积是 $\Delta$ 的右伴随（$\Delta \dashv \times$），余积是 $\Delta$ 的左伴随（$+ \dashv \Delta$）——这又是一次对偶。
:::

::: details 参考答案 6：积与函数对象之间的伴随
就是正文中的 `curryAdj`：

```lean no-check
def curryAdj (a : Type) : Adjunction (Pair a) (Expo a) where
  unit z := fun x => (z, x)
  counit p := p.1 p.2
  unit_natural _ _ := rfl
  counit_natural _ _ := rfl
  left_triangle _ := rfl
  right_triangle _ := rfl
```

它的 `leftAdjunct` 是 `Function.curry`，`rightAdjunct` 是 `Function.uncurry`。作为额外的练习，试着直接构造
`HomAdjunction (Pair a) (Expo a)`（用 `Function.curry`/`Function.uncurry` 填写数据字段），再用 `HomAdjunction.toAdj`
得到单位和余单位，看看它们是否就是上面的 `fun z x => (z, x)` 和 `eval`。

```lean
def curryHomAdj (a : Type) : HomAdjunction (Pair a) (Expo a) where
  leftAdjunct f  := Function.curry f
  rightAdjunct g := Function.uncurry g
  right_left _ := by funext ⟨_, _⟩; rfl
  left_right _ := rfl
  natural_c _ _ := rfl
  natural_d _ _ := rfl

example (a z : Type) (x : z) :
    (curryHomAdj a).toAdj.unit x = (curryAdj a).unit x := rfl
example (a b : Type) (p : Pair a (Expo a b)) :
    (curryHomAdj a).toAdj.counit p = (curryAdj a).counit p := rfl
```
:::

## 本章小结

- 相等太强，同构才是对象之间有用的“相同”。对函子来说，“相同”应理解为**自然同构**，于是有了范畴的**等价**。
- **伴随** $L \dashv R$ 比等价更弱：只要单位 $\eta : I_{\mathcal{D}} \to R \circ L$ 和余单位 $\varepsilon : L \circ R \to I_{\mathcal{C}}$ 两个单向的自然变换，
  外加两条**三角恒等式**（先引入再消去等于什么都没做）。
- 等价的另一种定义：hom-集的自然同构 $\mathcal{C}(L d, c) \cong \mathcal{D}(d, R c)$。单位 $= \varphi(\mathrm{id})$，余单位 $= \varphi^{-1}(\mathrm{id})$；
  反过来 $\varphi f = R f \circ \eta$，$\varphi^{-1} g = \varepsilon \circ L g$。我们在 Lean 中对 Type 上任意守法自函子证明了两种定义互相导出。
- 泛构造可以只针对个别对象；伴随是全局的。当所有对象对都有积时，积就是对角函子的**右**伴随；余积则是它的**左**伴随。
- 指数是 $(- \times a)$ 的右伴随：$\mathcal{C}(z \times a, b) \cong \mathcal{C}(z, b^a)$ 就是**柯里化**；余单位是 `eval`。
- 每个伴随都给出一个单子 $R \circ L$ 和一个余单子 $L \circ R$。柯里化伴随给出 **State 单子**（`StateM`）与 Store 余单子。
- 当右边的范畴是 $\mathbf{Set}$ 时，右伴随是可表的，表示对象是 $L\,()$。
- 伴随（若存在）在同构意义下唯一——这就是我们能说“那个积”“那个指数”的原因。
