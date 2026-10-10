# 1.8 函子性

现在你已经知道函子是什么，也见过几个例子了，我们来看看怎样用小的函子搭出更大的函子。
特别有意思的是看一看：哪些类型构造器（它们对应于范畴中对象之间的映射）能被扩充成函子（函子还包括态射之间的映射）。
一个映射“能把态射也一起映过去、并且守规矩”，就是本章标题所说的**函子性**（functoriality）。

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

-- 本章后面会定义一个也叫 `Op` 的类型构造器，所以打开命名空间时把对偶范畴的 `Op` 藏起来，
-- 需要它时写全名 `CTFP.Op`。
open CTFP hiding Op
```

::: tip 本章用到的公共定义
本章沿用 [1.7 函子](/part1/07-functors) 中的 `CTFP.Category`（记号 `a ⟶ b`、`g ⊚ f`、`𝟙 a`）、
`CTFP.typeCategory` 和 `CTFP.CFunctor`，以及对偶范畴 `CTFP.Op`。它们已经放在本章开头一个隐藏的代码块里，
点“在线运行”时会自动带上。
:::

## 双函子

既然函子是 $\mathbf{Cat}$（范畴的范畴）中的态射，那么我们关于态射——尤其是关于函数——的许多直觉，对函子也同样适用。
比如，正如函数可以有两个参数，函子也可以有两个参数，这就是**双函子**（bifunctor）。在对象上，双函子把每一对对象——
一个来自范畴 $\mathcal{C}$，一个来自范畴 $\mathcal{D}$——映到范畴 $\mathcal{E}$ 中的一个对象。
注意，这不过是在说：它是从范畴的**笛卡尔积**（Cartesian product）$\mathcal{C} \times \mathcal{D}$ 到 $\mathcal{E}$ 的一个映射。

![双函子](/img/1.8/bifunctor.jpg "双函子把一对对象——一个来自 C，一个来自 D——映到 E 中的一个对象。")

这相当直白。但函子性意味着双函子还必须映射态射。只不过这一次，它必须把一对态射——一个来自 $\mathcal{C}$，
一个来自 $\mathcal{D}$——映到 $\mathcal{E}$ 中的一个态射。

同样地，一对态射也不过是积范畴 $\mathcal{C} \times \mathcal{D}$ 中的**一个**态射。我们把范畴笛卡尔积中的态射定义为一对态射，
它从一对对象走到另一对对象：从 $(a, b)$ 到 $(a', b')$ 的态射是 $(f, g)$，其中 $f : a \to a'$ 在 $\mathcal{C}$ 中，
$g : b \to b'$ 在 $\mathcal{D}$ 中。这些态射对可以按最显然的方式复合：

$$(f, g) \circ (f', g') = (f \circ f', g \circ g')$$

这个复合满足结合律，并且有恒等态射——一对恒等态射 $(\mathrm{id}, \mathrm{id})$。所以范畴的笛卡尔积确实是一个范畴。

```diagram
P: (0, 0) "(a, b)"
Q: (2.4, 0) "(a', b')"
R: (4.8, 0) "(a'', b'')"
fg': P -> Q "(f', g')"
fg: Q -> R "(f, g)"
comp: P -> R "(f \circ f',\ g \circ g')" bend=-46 side=right color=green
path "先 (f', g') 再 (f, g)": fg' fg
path "一步走 (f∘f', g∘g')": comp color=green
caption: 积范畴 C × D 中的复合：两个分量各自复合，互不干扰。
```

::: info 数学小课堂：两个集合的笛卡尔积，两个范畴的笛卡尔积
你在中学就见过**笛卡尔积**：集合 $A = \{1, 2\}$ 与 $B = \{x, y, z\}$ 的笛卡尔积
$A \times B$ 是所有有序对组成的集合 $\{(1,x), (1,y), (1,z), (2,x), (2,y), (2,z)\}$，一共 $2 \times 3 = 6$ 个元素。
平面直角坐标系就是 $\mathbb{R} \times \mathbb{R}$。

两个**范畴**的笛卡尔积只是把同一个想法用了两次：对象是“对象对”，箭头是“箭头对”。
可以把它想象成两条并排的流水线：一个箭头对 $(f, g)$ 就是“左边流水线走一步 $f$，同时右边流水线走一步 $g$”。
两条流水线各干各的，复合也就各复合各的。
:::

在 Lean 里，积范畴就是给 `C × D` 写一个 `Category` 实例。三条定律都归结为“每个分量上的定律”：

```lean
instance prodCategory (C : Type u₁) [Category.{u₁, v₁} C] (D : Type u₂) [Category.{u₂, v₂} D] :
    Category (C × D) where
  -- 从 (a, b) 到 (a', b') 的态射 = 一对态射
  Hom p q := (p.1 ⟶ q.1) × (p.2 ⟶ q.2)
  id p := (𝟙 p.1, 𝟙 p.2)
  -- 逐分量复合
  comp g f := (g.1 ⊚ f.1, g.2 ⊚ f.2)
  -- 三条定律：逐分量用 C 和 D 自己的定律
  id_comp f := by simp [Category.id_comp]
  comp_id f := by simp [Category.comp_id]
  assoc f g h := by simp [Category.assoc]
```

::: tip Lean 深入：`simp [引理]`
`simp` 是 Lean 的“化简器”：它反复用等式从左往右改写目标，直到改不动为止。方括号里可以塞进额外的引理。
这里目标是一个**对**的等式，比如 `(𝟙 ⊚ f.1, 𝟙 ⊚ f.2) = f`；`simp` 先用 `Category.id_comp` 把两个分量化简成
`(f.1, f.2) = f`，再用它自带的知识（一个对等于它两个分量拼回去）收尾。
:::

考虑双函子还有一种更省事的办法：把它看成在每个参数上**分别**是函子。这样，就不必把函子定律——结合性和保持恒等——
从函子整体翻译到双函子上，只要对每个参数分别检查就够了。然而一般而言，分别的函子性并不足以证明联合的函子性。
联合函子性不成立的那些范畴，被称为**预幺半范畴**（premonoidal category）。

我们来在 Lean 中定义一个双函子。这里三个范畴都是同一个：Lean 类型的范畴。双函子就是一个接受两个类型参数的类型构造器
`F : Type → Type → Type`。下面是 `Bifunctor` 类型类的定义，原书直接取自 Haskell 的库 `Control.Bifunctor`；
Lean 核心库里没有它，我们原样照搬过来：

```lean
class Bifunctor (F : Type → Type → Type) where
  /-- 同时映射两个参数 -/
  bimap : (a → c) → (b → d) → F a b → F c d := fun g h => first g ∘ second h
  /-- 只映射第一个参数 -/
  first : (a → c) → F a b → F c b := fun g => bimap g id
  /-- 只映射第二个参数 -/
  second : (b → d) → F a b → F a d := fun h => bimap id h

open Bifunctor
```

![bimap](/img/1.8/bimap.jpg "bimap：把一对函数 g 和 h 同时提升，作用在 F a b 上，得到 F c d。")

类型变量 `F` 代表双函子。你可以看到，在所有类型签名中，它总是被应用到两个类型参数上。第一个类型签名定义了 `bimap`：
一次映射两个函数。结果是一个被**提升**（lift）了的函数 `F a b → F c d`，它作用在由双函子的类型构造器生成的类型上。
`bimap` 有一个用 `first` 和 `second` 写成的默认实现。（前面提到过，这并不总是行得通，因为两个映射可能不可交换，
也就是说，`first g ∘ second h` 未必等于 `second h ∘ first g`。）

另外两个类型签名 `first` 和 `second`，就是分别见证 `F` 在第一个参数和第二个参数上具有函子性的两个 `fmap`。

<div style="display:flex;gap:16px;flex-wrap:wrap;justify-content:center">
<div style="flex:1;min-width:220px">

![first](/img/1.8/first.jpg "first：只提升第一个分量上的函数 g。")

</div>
<div style="flex:1;min-width:220px">

![second](/img/1.8/second.jpg "second：只提升第二个分量上的函数 h。")

</div>
</div>

类型类的定义为它们俩都提供了用 `bimap` 写成的默认实现。

声明 `Bifunctor` 的实例时，你可以选择实现 `bimap`，接受 `first` 和 `second` 的默认实现；也可以选择实现 `first` 和 `second`，
接受 `bimap` 的默认实现。（当然，你也可以三个全都自己实现，但那样就得由你自己来保证它们之间满足上述关系。）

::: tip Lean 深入：互相引用的默认方法
`class` 的字段可以带默认值（`:= ...`），而且默认值可以引用**其他字段**——甚至可以像这里一样**互相引用**：
`bimap` 的默认值用到 `first`、`second`，而它俩的默认值又用到 `bimap`。写实例时，Lean 会把你给出的字段代进去，
把剩下的默认值一个个解出来。

和 Haskell 相比，Lean 在这里更安全：如果你一个字段都不写（`instance : Bifunctor Prod where`），
Haskell 会编译通过，然后在运行时陷入 `bimap` 调 `first`、`first` 又调 `bimap` 的无限循环；
Lean 则直接报错 `Fields missing: bimap, first, second`——互相引用的默认值解不出来，就不让你过。
:::

原书到这里只能口头说“双函子要满足函子定律”。在 Lean 里我们可以把定律写进一个类型类，就像核心库的 `LawfulFunctor` 那样：

```lean
class LawfulBifunctor (F : Type → Type → Type) [Bifunctor F] : Prop where
  /-- 保持恒等：bimap id id = id -/
  bimap_id : ∀ {a b : Type}, bimap (@id a) (@id b) = @id (F a b)
  /-- 保持复合：先 bimap f₁ g₁ 再 bimap f₂ g₂，等于一次 bimap (f₂ ∘ f₁) (g₂ ∘ g₁) -/
  bimap_comp : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : Type}
      (f₁ : a₁ → a₂) (f₂ : a₂ → a₃) (g₁ : b₁ → b₂) (g₂ : b₂ → b₃),
    bimap (f₂ ∘ f₁) (g₂ ∘ g₁) = (bimap f₂ g₂ ∘ bimap f₁ g₁ : F a₁ b₁ → F a₃ b₃)
  /-- first 与 bimap 一致 -/
  first_eq : ∀ {a b c : Type} (g : a → c), (first g : F a b → F c b) = bimap g id
  /-- second 与 bimap 一致 -/
  second_eq : ∀ {a b d : Type} (h : b → d), (second h : F a b → F a d) = bimap id h
```

`bimap_id` 和 `bimap_comp` 正是积范畴 $\mathcal{C} \times \mathcal{C} \to \mathcal{C}$ 上的函子定律：
积范畴的恒等态射是 `(id, id)`，积范畴的复合是逐分量复合。后两条则要求三个方法彼此一致。

有了这些定律，前面那句“两个映射未必可交换”就可以说得更精确：**只要双函子是守法的，`first` 和 `second` 就一定可交换**，
而且无论先做哪个，都等于 `bimap`。证明只是把定义展开，再用一次 `bimap_comp`：

```lean
theorem bimap_eq_first_second {F} [Bifunctor F] [LawfulBifunctor F] {a b c d : Type}
    (g : a → c) (h : b → d) :
    (bimap g h : F a b → F c d) = first g ∘ second h := by
  -- 把 first、second 都改写成 bimap，再把两次 bimap 合并成一次
  rw [LawfulBifunctor.first_eq, LawfulBifunctor.second_eq, ← LawfulBifunctor.bimap_comp]
  rfl  -- 剩下 bimap g h = bimap (g ∘ id) (id ∘ h)，两边按定义就相等

theorem first_second_comm {F} [Bifunctor F] [LawfulBifunctor F] {a b c d : Type}
    (g : a → c) (h : b → d) :
    (first g ∘ second h : F a b → F c d) = second h ∘ first g := by
  rw [LawfulBifunctor.first_eq, LawfulBifunctor.second_eq, LawfulBifunctor.first_eq,
    LawfulBifunctor.second_eq, ← LawfulBifunctor.bimap_comp, ← LawfulBifunctor.bimap_comp]
  rfl
```

画成图就是一个交换方块：从 `F a b` 到 `F c d`，先改右边再改左边，或者先改左边再改右边，又或者一步到位，结果都一样。

```diagram
FAB: (0, 0) "F\,a\,b"
FCB: (3, 0) "F\,c\,b"
FAD: (0, 2) "F\,a\,d"
FCD: (3, 2) "F\,c\,d"
fg: FAB -> FCB "\mathtt{first}\ g"
sh: FCB -> FCD "\mathtt{second}\ h"
sh2: FAB -> FAD "\mathtt{second}\ h" side=right
fg2: FAD -> FCD "\mathtt{first}\ g" side=right
bm: FAB -> FCD "\mathtt{bimap}\ g\ h" color=green pos=0.42
path "先 first 后 second": fg sh
path "先 second 后 first": sh2 fg2 color=brand
path "一步 bimap": bm color=green
caption: 守法的双函子中，first 与 second 可交换，且都等于 bimap。
```

::: warning 易错点：“分别是函子”不等于“联合是函子”
`first_second_comm` 的证明用到了 `bimap_comp`——也就是**联合**函子性。如果你只知道 `first` 满足函子定律、
`second` 也满足函子定律，那是推不出它俩可交换的。这正是前面提到的“预幺半范畴”的情形。
在 Lean 类型的范畴里，我们遇到的双函子都没有这个问题；但当你自己从 `first`/`second` 出发写实例时，
最好把 `LawfulBifunctor` 也证一遍，让编译器替你把关。
:::

::: tip Rust 视角：`Result<T, E>` 就是一个双函子
Rust 程序员每天都在用双函子，只是不这么叫它。`Result<T, E>` 有两个类型参数，而且两个参数上都有 `map`：

- `Result::map` 改 `Ok` 里的值，`Result::map_err` 改 `Err` 里的值——它们就是一个双函子的两个“单边 `fmap`”。
  （对应到 Lean 的 `Sum ε α`：习惯上把错误放在左边，于是 `map_err` 相当于 `first`，`map` 相当于 `second`。
  Rust 把 `T` 写在 `E` 前面，只是参数顺序不同，不影响结构。）
- `res.map(f).map_err(g)` 和 `res.map_err(g).map(f)` 结果总是一样——这就是上面证明的 `first_second_comm`。

Rust 标准库没有 `bimap`，因为 Rust 没法写出“对一切双参数类型构造器抽象”的 trait（缺少高阶类型，后面“Rust 中的函子”一节会细说）。
:::

## 积与余积双函子

双函子的一个重要例子是范畴积——由[泛构造](/part1/05-products-and-coproducts)定义的两个对象的积。
如果任意一对对象都有积，那么从这对对象到它们的积的映射就是双函子性的。这在一般情况下成立，在 Lean 中当然也成立。
下面是对子构造器——最简单的积类型 `Prod`——的 `Bifunctor` 实例：

```lean
instance : Bifunctor Prod where
  bimap f g p := (f p.1, g p.2)
```

没有多少选择余地：`bimap` 只是把第一个函数作用到对子的第一个分量上，把第二个函数作用到第二个分量上。
给定了类型，代码几乎是自己写出来的：

```lean no-check
bimap : (a → c) → (b → d) → a × b → c × d
```

（Lean 核心库其实早就有这个函数，叫 `Prod.map`。）这个双函子在对象上的作用，就是把两个类型配成对子类型，例如：

```lean
example : Prod Nat Bool = (Nat × Bool) := rfl
```

定律也都是按定义成立（`rfl`）——一个对被拆开、各分量被映射、再装回去，这个过程中什么都不会走样：

```lean
instance : LawfulBifunctor Prod where
  bimap_id := rfl
  bimap_comp _ _ _ _ := rfl
  first_eq _ := rfl
  second_eq _ := rfl

example : bimap (· + 1) toString (41, 7) = (42, "7") := rfl
```

根据对偶性，余积如果对范畴中每一对对象都有定义，那它也是一个双函子。在 Lean 中，体现这一点的是类型构造器 `Sum`
（即 `α ⊕ β`，相当于 Haskell 的 `Either`）作为 `Bifunctor` 的实例：

```lean
instance : Bifunctor Sum where
  bimap f g
    | .inl x => .inl (f x)
    | .inr y => .inr (g y)
```

这段代码同样是自己写出来的。不过这一回，定律需要**分情况**证明：一个 `Sum` 值要么是 `inl`，要么是 `inr`。

```lean
instance : LawfulBifunctor Sum where
  -- intro 引入隐式的类型参数，funext 把函数等式化为逐点等式，
  -- cases s 分成 inl / inr 两种情况，<;> rfl 对两种情况都用 rfl 收尾
  bimap_id := by intro a b; funext s; cases s <;> rfl
  bimap_comp _ _ _ _ := by funext s; cases s <;> rfl
  first_eq _ := rfl
  second_eq _ := rfl
```

::: tip Lean 深入：`funext`、`cases` 与 `<;>`
- `funext s`：要证两个函数相等，只需证它们在每个输入 `s` 上的输出相等（函数外延性）。
- `cases s`：`s : a ⊕ b` 只可能由 `inl` 或 `inr` 构造，于是把目标拆成两个子目标，各自处理。
- `t₁ <;> t₂`：先执行 `t₁`，然后把 `t₂` 应用到 `t₁` 产生的**每一个**子目标上。这里就是“两种情况都用 `rfl`”。
:::

我们还可以更进一步，按本书最正式的方式把积写成一个 `CFunctor`：从积范畴 $\mathbf{Type} \times \mathbf{Type}$
到 $\mathbf{Type}$ 的函子。积范畴里的一个态射是一对函数 `(f, g)`，它被映到 `Prod.map f g`：

```lean
def prodFunctor : CFunctor (Type × Type) Type where
  obj p := p.1 × p.2
  map fg := Prod.map fg.1 fg.2
  map_id _ := rfl
  map_comp _ _ := rfl

def sumFunctor : CFunctor (Type × Type) Type where
  obj p := p.1 ⊕ p.2
  map fg := Sum.map fg.1 fg.2
  map_id _ := by funext s; cases s <;> rfl
  map_comp _ _ := by funext s; cases s <;> rfl
```

这就是“双函子 = 从积范畴出发的函子”这句话在 Lean 里的字面意思。

下面这个小组件让你亲手操作双函子：选一个值，选两个函数，比较 `first`、`second` 的不同先后顺序与 `bimap`。

<div><Ch1_8Bimap /></div>

还记得我们讨论幺半范畴的时候吗？幺半范畴定义了一个作用在对象上的二元运算，外加一个单位对象。我提到过，
$\mathbf{Set}$ 关于笛卡尔积是一个幺半范畴，单元素集合是单位；它关于不交并也是一个幺半范畴，空集是单位。
我当时没有提的是：幺半范畴的要求之一，就是那个二元运算必须是一个双函子。这是一条非常重要的要求——
我们希望幺半积与范畴的结构相容，而范畴的结构是由态射定义的。我们离幺半范畴的完整定义又近了一步
（在抵达那里之前，我们还得先学习自然性）。

::: info 数学小课堂：幺半范畴的预告
回忆**幺半群**：一个集合，加上一个满足结合律的二元运算和一个单位元，比如 $(\mathbb{N}, +, 0)$、`(String, ++, "")`。

**幺半范畴**（monoidal category）把同一个想法“提升一层”：

| 幺半群 | 幺半范畴 |
|---|---|
| 元素 | 对象（比如类型） |
| 二元运算 $\cdot$ | 双函子 $\otimes$（比如 `×` 或 `⊕`） |
| 单位元 $e$ | 单位对象 $I$（比如 `Unit` 或 `Empty`） |
| $(x \cdot y) \cdot z = x \cdot (y \cdot z)$ | $(a \otimes b) \otimes c \cong a \otimes (b \otimes c)$ |

注意最后一行从“等于”变成了“同构”：`(a × b) × c` 和 `a × (b × c)` 并不是同一个类型，但可以无损地互相转换。
要把这些同构说清楚（它们必须“自然”），需要 [1.10 自然变换](/part1/10-natural-transformations) 的知识。
而“$\otimes$ 必须是双函子”这一条，正是本节的内容。
:::

## 函子性的代数数据类型

我们已经见过好几个带参数的数据类型，它们最后都被证明是函子——我们能为它们定义 `fmap`。
复杂的数据类型是由较简单的数据类型构造出来的。特别地，代数数据类型（ADT）是用**和**与**积**创造出来的。
我们刚刚看到，和与积都是有函子性的；我们也知道函子可以复合。所以，只要能证明 ADT 的基本积木是有函子性的，
我们就会知道带参数的 ADT 也都是有函子性的。

那么，带参数的代数数据类型的基本积木都有哪些呢？

首先，是那些不依赖于函子类型参数的部分，比如 `Option` 中的 `none`，或者 `List` 中的 `nil`。它们等价于 `Const` 函子。
记住，`Const` 函子忽略它的类型参数（实际上是**第二个**类型参数，那才是我们关心的那个；第一个则保持不变）。

```lean
/-- `Const c a` 里只装着一个 `c`，类型参数 `a` 只是个摆设。 -/
structure Const (c a : Type) where
  val : c

instance : Functor (Const c) where
  map _ x := ⟨x.val⟩      -- 函数 f 根本没地方用：没有 a 可以喂给它

instance : LawfulFunctor (Const c) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

其次，是那些只是把类型参数本身包起来的元素，比如 `Option` 中的 `some`。它们等价于恒等函子。
我之前提到过恒等函子——它是 $\mathbf{Cat}$ 中的恒等态射——但没有给出它的定义。下面就是：

```lean
/-- 最简单的容器：永远恰好装着一个 a。 -/
structure Identity (a : Type) where
  run : a

instance : Functor Identity where
  map f x := ⟨f x.run⟩

instance : LawfulFunctor Identity where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

你可以把 `Identity` 看成最简单的容器：它总是只存放一个（不可变的）`a` 类型的值。

::: tip Lean 深入：核心库里的 `Id`
Lean 核心库其实已经有恒等函子了，叫 `Id`：`def Id (α : Type u) : Type u := α`。它甚至是一个单子，
平时写 `Id.run do ...` 时就在用它。我们这里另起一个 `Identity`，是因为 `Id α` **就是** `α` 本身（定义上相等），
而本章想要一个“看得见包装”的版本，好和 `Const` 并排比较。两者是同构的。
:::

代数数据结构中的其他一切，都是用积与和从这两种原始积木构造出来的。

带着这些新知识，我们重新审视一下 `Option` 类型构造器（下面是它在 Lean 核心库中的定义）：

```lean no-check
inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α
```

它是两个类型的和，而我们现在知道和是有函子性的。第一部分 `none` 可以表示成作用在 `a` 上的 `Const Unit`
（`Const` 的第一个类型参数被设为单元类型——后面我们会看到 `Const` 更有意思的用法）。
第二部分不过是恒等函子的另一个名字。在同构的意义下，我们本可以这样定义 `Option`：

```lean
abbrev Maybe' (a : Type) := Sum (Const Unit a) (Identity a)
```

所以 `Option` 就是双函子 `Sum` 与两个函子 `Const Unit` 和 `Identity` 的复合。（`Const` 其实是一个双函子，
只是我们在这里总是部分应用它。）

我们已经看到，函子的复合是函子——不难说服自己，对双函子来说也是如此。我们只需要弄清楚，一个双函子与两个函子的复合
在态射上是怎样作用的。给定两个态射，我们只要用一个函子提升其中一个，用另一个函子提升另一个；
然后再用双函子提升得到的这一对被提升过的态射。

我们可以在 Lean 中表达这种复合。我们来定义一个数据类型，它的参数是：一个双函子 `bf`（它是一个类型变量，
代表一个接受两个类型作为参数的类型构造器）、两个函子 `fu` 和 `gu`（各自接受一个类型变量的类型构造器），
以及两个普通类型 `a` 和 `b`。我们把 `fu` 应用到 `a` 上，把 `gu` 应用到 `b` 上，然后再把 `bf` 应用到得到的两个类型上：

```lean
structure BiComp (bf : Type → Type → Type) (fu gu : Type → Type) (a b : Type) where
  run : bf (fu a) (gu b)
```

这就是对象（也就是类型）上的复合。注意在 Lean 里，我们把类型构造器应用到类型上，就像把函数应用到参数上一样，
语法完全相同——因为类型构造器**就是**函数，只不过它的输入输出是类型（`Type → Type → Type`）。

如果你有点晕了，试着把 `BiComp` 依次应用到 `Sum`、`Const Unit`、`Identity`、`a` 和 `b` 上。
你会还原出我们那个简陋版本的 `Maybe' b`（`a` 被忽略了）：

```lean
-- BiComp Sum (Const Unit) Identity a b 里装的，就是 Const Unit a ⊕ Identity b
example (a b : Type) (x : BiComp Sum (Const Unit) Identity a b) : Const Unit a ⊕ Identity b := x.run
```

`Const Unit a` 和 `Const Unit b` 里装的都只是一个 `()`，所以 `a` 是什么根本无关紧要——这就是“`a` 被忽略了”的意思。

新的数据类型 `BiComp` 是 `a` 与 `b` 上的双函子，但前提是 `bf` 本身是一个 `Bifunctor`，并且 `fu` 和 `gu` 都是 `Functor`。
编译器必须知道：会有一个 `bimap` 的定义可用于 `bf`，也会有 `fmap`（Lean 里叫 `Functor.map`，中缀写作 `<$>`）的定义可用于 `fu` 和 `gu`。
在 Haskell 中，这表达为实例声明中的前提条件：一组类约束，后面跟一个双箭头 `=>`。在 Lean 中，它写成实例声明里
方括号括起来的一串实例参数：

```lean
instance {bf fu gu} [Bifunctor bf] [Functor fu] [Functor gu] : Bifunctor (BiComp bf fu gu) where
  bimap f₁ f₂ x := ⟨bimap (Functor.map f₁) (Functor.map f₂) x.run⟩
```

`BiComp` 的 `bimap` 的实现，是借助 `bf` 的 `bimap` 以及 `fu` 和 `gu` 的两个 `map` 给出的。每当用到 `BiComp` 时，
编译器会自动推断出所有类型，并挑选出正确的重载函数。

::: tip Lean 深入：方括号里的实例参数
`[Bifunctor bf]` 是**实例隐式参数**：调用者不用手动传，Lean 会通过类型类解析自动找到一个实例填进去。
它相当于 Haskell 里 `=>` 左边的类约束，也相当于 Rust 里的 `where bf: Bifunctor` 约束。
:::

`bimap` 定义中的 `x.run` 的类型是：

```lean no-check
bf (fu a) (gu b)
```

真是够拗口的。外层的 `bimap` 突破外面的 `bf` 这一层，两个 `map` 则分别钻到 `fu` 和 `gu` 底下。如果 `f₁` 和 `f₂` 的类型是：

```lean no-check
f₁ : a → a'
f₂ : b → b'
```

那么最终结果的类型就是 `bf (fu a') (gu b')`：

```lean no-check
bimap : (fu a → fu a') → (gu b → gu b') → bf (fu a) (gu b) → bf (fu a') (gu b')
```

如果你喜欢拼图游戏，这类类型摆弄能给你带来好几个小时的乐趣。

原书说到这里就停了。在 Lean 中我们可以更进一步：**证明** `BiComp` 确实是守法的双函子——前提是 `bf` 守法、`fu` 和 `gu` 守法。
证明的思路就是上面那段话：外层用 `bf` 的定律，内层用 `fu`、`gu` 的定律。

::: details 证明：守法的积木复合出守法的双函子
```lean
instance {bf fu gu} [Bifunctor bf] [LawfulBifunctor bf] [Functor fu] [LawfulFunctor fu]
    [Functor gu] [LawfulFunctor gu] : LawfulBifunctor (BiComp bf fu gu) where
  bimap_id := by
    intro a b
    funext ⟨x⟩
    show BiComp.mk (bimap (Functor.map id) (Functor.map id) x) = _
    -- 内层：map id = id（这是 fu、gu 的函子定律 id_map）
    have h1 : (Functor.map id : fu a → fu a) = id := funext id_map
    have h2 : (Functor.map id : gu b → gu b) = id := funext id_map
    -- 外层：bimap id id = id（这是 bf 的双函子定律）
    rw [h1, h2, LawfulBifunctor.bimap_id]
    rfl
  bimap_comp {a₁ a₂ a₃ b₁ b₂ b₃} f₁ f₂ g₁ g₂ := by
    funext ⟨x⟩
    show BiComp.mk (bimap (Functor.map (f₂ ∘ f₁)) (Functor.map (g₂ ∘ g₁)) x) = _
    -- 内层：map (f₂ ∘ f₁) = map f₂ ∘ map f₁（函子定律 comp_map）
    have h1 : (Functor.map (f₂ ∘ f₁) : fu a₁ → fu a₃) = Functor.map f₂ ∘ Functor.map f₁ :=
      funext (comp_map f₁ f₂)
    have h2 : (Functor.map (g₂ ∘ g₁) : gu b₁ → gu b₃) = Functor.map g₂ ∘ Functor.map g₁ :=
      funext (comp_map g₁ g₂)
    -- 外层：bf 的 bimap_comp
    rw [h1, h2, LawfulBifunctor.bimap_comp]
    rfl
  first_eq _ := rfl
  second_eq _ := rfl
```
`have h : 命题 := 证明` 在证明中途引入一个中间结论，之后可以用 `rw [h]` 改写。`funext ⟨x⟩` 在引入变量的同时把结构体拆开。
:::

现在可以兑现前面的承诺：`BiComp Sum (Const Unit) Identity` 是一个双函子，它在第二个参数上的 `second`
正是 `Option` 的 `map`。我们没有为它写一行函子代码，函子性完全来自它的构造方式：

```lean
/-- 从 BiComp 的双函子结构中“白捡”一个 map -/
def maybeMap (f : b → b') : BiComp Sum (Const Unit) Identity a b → BiComp Sum (Const Unit) Identity a b' :=
  second f

def just (x : b) : BiComp Sum (Const Unit) Identity Unit b := ⟨.inr ⟨x⟩⟩
def nothing : BiComp Sum (Const Unit) Identity Unit b := ⟨.inl ⟨()⟩⟩

example : (maybeMap (· * 2) (just 21)).run = .inr ⟨42⟩ := rfl
example : (maybeMap (· * 2) (nothing : BiComp Sum (Const Unit) Identity Unit Nat)).run = .inl ⟨()⟩ := rfl
```

所以事实证明，我们根本不必证明 `Option` 是一个函子——这个事实源自它的构造方式：它是两个有函子性的原始积木之和。

敏锐的读者可能会问：如果为代数数据类型推导 `Functor` 实例的过程如此机械，难道不能把它自动化，交给编译器去做吗？
确实可以，而且确实有人这么做了。在 Haskell 中，你需要在源文件顶部加上一行 `{-# LANGUAGE DeriveFunctor #-}`，
打开一个特定的语言扩展，然后在数据结构的定义后面加上 `deriving Functor`，比如
`data Maybe a = Nothing | Just a deriving Functor`，相应的 `fmap` 就会替你实现好。

代数数据结构的这种规整性，使得我们不仅能派生 `Functor` 的实例，还能派生其他好几个类型类的实例，
包括我之前提到过的 `Eq` 类型类（Lean 中的 `BEq`/`DecidableEq`）。还可以选择教编译器为你自己的类型类派生实例，
不过那就更高级一点了。但思路是一样的：你为基本积木以及和与积提供行为，剩下的让编译器自己去推算。

::: tip Lean 深入：Lean 里的 `deriving`
Lean 4 核心库同样支持 `deriving`，但内置的派生处理器只有 `Repr`、`BEq`、`DecidableEq`（相当于 Haskell 的 `Eq`）、
`Hashable`、`Ord`、`Inhabited`、`Nonempty` 等，**没有 `Functor`**。（Mathlib 提供了 `Functor`、`Traversable`
等的派生处理器；Lean 也允许你用元编程为自己的类型类写派生处理器——正是上面说的“更高级”的做法。）

所以在只用核心库时，我们像本节这样**手写** `Functor` 实例，并顺手证明 `LawfulFunctor`。好消息是，
手写的规则完全就是本节的“积木法则”：

- 遇到不含类型参数的字段（`Const`），原样保留；
- 遇到类型参数本身（`Identity`），把函数作用上去；
- 遇到递归出现的自身，递归调用 `map`；
- 和类型逐个构造器处理，积类型逐个字段处理。

下一节的 `Tree` 就是一个按这个规则手写的例子。
:::

```lean
inductive Color where
  | red | green | blue
  deriving Repr, BEq, DecidableEq

example : (Color.red == Color.red) = true := rfl
example : Color.red ≠ Color.blue := by decide
```

## Rust 中的函子

> 原书本节题为“C++ 中的函子”，讲的是 C++ 程序员如何为模板化的数据结构手写 `fmap`。
> 我们把它改写成 Rust 版本——你会发现 Rust 遇到的障碍和 C++ 惊人地相似。

如果你是 Rust 程序员，那么在实现函子这件事上，你显然只能自力更生了。不过，你应该能在 Rust 中认出某几种代数数据结构。
如果这样的数据结构被做成了泛型，你应该能很快为它实现 `fmap`。

我们来看一个树形数据结构。在 Lean 中，我们会把它定义成一个递归的和类型：

```lean
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  deriving Repr
```

前面提到过，在 C++ 中实现和类型的一种办法是借助类层次结构；在 Rust 中，与之对应的是 trait 对象（`Box<dyn Trait>`）。
在面向对象的语言里，很自然的做法是把 `fmap` 实现为基类 `Functor` 的一个虚函数，然后在所有子类中覆写它。
可惜这是不可能的，因为 `fmap` 是一个模板：它不仅以所作用的对象的类型（`this` 指针）为参数，
还以被应用到它身上的那个函数的返回类型为参数。C++ 中的虚函数不能被模板化。

Rust 有一模一样的限制，只是换了个说法：**带泛型参数的方法会让 trait 失去 dyn 兼容性**（以前叫“对象安全”）。
你不能写一个 `trait Tree<T> { fn map<U>(&self, f: ...) -> Box<dyn Tree<U>>; }` 再拿 `Box<dyn Tree<T>>` 去用它——
虚表里没法为无穷多个 `U` 各放一个函数指针。所以，我们会把 `fmap` 实现为一个泛型自由函数，
并用动态转型（C++ 的 `dynamic_cast`，Rust 的 `Any::downcast_ref`）来代替模式匹配。

在 C++ 里，基类必须至少定义一个虚函数才能支持动态转型，所以原书把析构函数做成了虚函数（这在任何情况下都是个好主意）。
在 Rust 里，“基类”是一个 trait，它唯一的方法 `as_any` 把自己交给 `std::any::Any`，好让我们事后查验它的具体类型。
`Leaf` 不过是乔装打扮的 `Identity` 函子；`Node` 是一个积类型。

实现 `fmap` 时，我们利用了 `Tree` 类型上的动态分派。`Leaf` 的情形套用 `Identity` 版本的 `fmap`，
`Node` 的情形则被当作一个双函子与两份 `Tree` 函子的复合来处理。作为 Rust 程序员，你大概不习惯用这种方式分析代码，
但这是一次很好的范畴论思维练习。

```rust
use std::any::Any;

// “基类”：唯一的方法用来支持动态转型（相当于 C++ 版本中虚析构函数的作用）
pub trait Tree<T> {
    fn as_any(&self) -> &dyn Any;
}

// Leaf：乔装打扮的 Identity 函子
pub struct Leaf<T> {
    pub label: T,
}

// Node：积类型
pub struct Node<T> {
    pub left: Box<dyn Tree<T>>,
    pub right: Box<dyn Tree<T>>,
}

impl<T: 'static> Tree<T> for Leaf<T> {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl<T: 'static> Tree<T> for Node<T> {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub fn fmap<A: 'static, B: 'static>(f: &dyn Fn(&A) -> B, t: &dyn Tree<A>) -> Option<Box<dyn Tree<B>>> {
    if let Some(pl) = t.as_any().downcast_ref::<Leaf<A>>() {
        return Some(Box::new(Leaf { label: f(&pl.label) }));
    }
    if let Some(pn) = t.as_any().downcast_ref::<Node<A>>() {
        return Some(Box::new(Node {
            left: fmap(f, pn.left.as_ref())?,
            right: fmap(f, pn.right.as_ref())?,
        }));
    }
    None // 相当于 C++ 版本最后的 return nullptr
}
```

为简单起见，原书的 C++ 版本决定忽略内存与资源管理问题，不过在生产代码中，你大概会使用智能指针
（`unique_ptr` 或 `shared_ptr`，取决于你的策略）。Rust 的 `Box` 就是那个智能指针，所有权系统替我们保证了不会泄漏：
新树的节点归新树所有，用完后自动释放。

当然，上面这套“类层次 + 动态转型”在 Rust 里纯属自讨苦吃。Rust 有真正的和类型 `enum`，模式匹配也是现成的，
同样的积木分析可以写得干净得多：

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Tree<T> {
    Leaf(T),                          // Identity 函子
    Node(Box<Tree<T>>, Box<Tree<T>>), // 积：双函子 (,) 与两份 Tree 的复合
}

impl<T> Tree<T> {
    pub fn map<U>(self, f: &impl Fn(T) -> U) -> Tree<U> {
        match self {
            Tree::Leaf(x) => Tree::Leaf(f(x)),
            Tree::Node(l, r) => Tree::Node(Box::new(l.map(f)), Box::new(r.map(f))),
        }
    }
}

pub fn demo() -> Tree<String> {
    let t = Tree::Node(Box::new(Tree::Leaf(1)), Box::new(Tree::Leaf(2)));
    t.map(&|n: i32| format!("#{n}"))
}
```

和 Lean 的实现对比一下：

```lean
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf a => leaf (f a)
  | node l r => node (l.map f) (r.map f)

instance : Functor Tree where
  map := Tree.map

#eval (Nat.succ <$> Tree.node (.leaf 1) (.leaf 2) : Tree Nat)
-- Tree.node (Tree.leaf 2) (Tree.leaf 3)
```

在 Haskell 中，这个实现可以由编译器自动派生。在 Lean 中我们手写了它，那就顺手把函子定律也证了。
树是递归的，所以要用**归纳法**：

```lean
instance : LawfulFunctor Tree where
  map_const := rfl
  id_map t := by
    induction t with
    | leaf a => rfl                      -- 叶子：map id (leaf a) = leaf (id a) = leaf a
    | node l r ihl ihr =>                -- 节点：假设对两棵子树已经成立（归纳假设 ihl、ihr）
      simp only [Functor.map, Tree.map] at *
      rw [ihl, ihr]
  comp_map f g t := by
    induction t with
    | leaf a => rfl
    | node l r ihl ihr =>
      simp only [Functor.map, Tree.map] at *
      rw [ihl, ihr]
```

::: info 数学小课堂：结构归纳法
要证明“对所有树 `t`，某性质成立”，归纳法说只需证两件事：

1. **基础情形**：对每一片叶子 `leaf a` 成立；
2. **归纳步骤**：如果对子树 `l` 和 `r` 成立（这叫**归纳假设**），那么对 `node l r` 也成立。

因为每棵树都是从叶子开始、经过有限次 `node` 搭起来的，这两步就像多米诺骨牌一样覆盖了所有的树。
这和你在中学学过的数学归纳法（证 $n=0$，再从 $n$ 推 $n+1$）是同一回事——自然数不过是一种特别“瘦”的树。
Lean 的 `induction t with` 会自动生成这两类目标，并把归纳假设交给你（这里命名为 `ihl`、`ihr`）。
:::

::: tip Rust 视角：为什么 Rust 只能为具体类型写 `map`
`Option::map`、`Result::map`、`Iterator::map`、`Vec` 的 `into_iter().map(..).collect()`……Rust 里到处是 `map`，
但它们是**各自独立**的方法，没有一个统一的 `Functor` trait。原因是 Rust 缺少**高阶类型**（higher-kinded types）：
在 Lean 里我们可以写 `class Functor (f : Type → Type)`，让 `f` 本身成为参数，`f` 可以是 `Option`、`List`、`Tree`；
而在 Rust 中，`Option` 不带参数时根本不是一个能写进泛型的东西——你只能写 `Option<T>`。

用泛型关联类型（GAT）可以模拟一下：

```rust
pub trait Functor {
    type Elem;
    type Mapped<B>;
    fn fmap<B>(self, f: impl FnMut(Self::Elem) -> B) -> Self::Mapped<B>;
}

impl<A> Functor for Option<A> {
    type Elem = A;
    type Mapped<B> = Option<B>;
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Option<B> {
        self.map(f)
    }
}

// 但没有任何东西阻止你“撒谎”：Mapped<B> 可以是完全无关的类型
pub struct Liar<A>(pub A);
impl<A> Functor for Liar<A> {
    type Elem = A;
    type Mapped<B> = Vec<String>;
    fn fmap<B>(self, _f: impl FnMut(A) -> B) -> Vec<String> {
        vec![]
    }
}
```

`Liar` 的 `fmap` 把 `Liar<A>` 变成了 `Vec<String>`——这根本不是函子，可编译器无从拒绝，因为 trait 没法表达
“`Mapped<B>` 必须是**同一个**类型构造器作用在 `B` 上”。至于函子定律，Rust 的类型系统更是完全表达不了。
对比 Lean：`Functor f` 中的 `f` 被固定为同一个类型构造器，`LawfulFunctor f` 还要求你交出定律的证明。
:::

## Writer 函子

我答应过要回到[前面讲过的 Kleisli 范畴](/part1/04-kleisli-categories)。那个范畴里的态射，
是返回 `Writer` 数据结构的“修饰”函数：

```lean
def Writer (α : Type) := α × String
```

我说过，这种修饰和自函子有某种关系。确实，`Writer` 类型构造器在 `a` 上是函子性的。
我们甚至不必为它专门实现 `map`，因为它只是一个简单的积类型——`Prod` 的 `second` 就是它的 `map`。

但 Kleisli 范畴和函子之间——一般地说——是什么关系呢？Kleisli 范畴既然是范畴，就定义了复合与恒等。
提醒一下，复合由“鱼”运算符给出：

```lean
def fish (m₁ : α → Writer β) (m₂ : β → Writer γ) : α → Writer γ := fun x =>
  let (y, s₁) := m₁ x
  let (z, s₂) := m₂ y
  (z, s₁ ++ s₂)

infixr:55 " >=> " => fish
```

恒等态射则由一个名叫 `return` 的函数给出（`return` 在 Lean 中是关键字，我们叫它 `ret`）：

```lean
def ret (x : α) : Writer α := (x, "")
```

事实证明，只要你盯着这两个函数的类型看得足够久（我是说，**真的**足够久），就能找到一种把它们组合起来的办法，
得到一个类型签名恰好适合充当 `map` 的函数。就像这样：

```lean
def Writer.fmap (f : α → β) : Writer α → Writer β :=
  id >=> (fun x => ret (f x))
```

这里鱼运算符组合了两个函数：一个是熟悉的 `id`，另一个是 lambda——它把 `f` 作用到参数上，再对结果施以 `ret`。
最难想通的大概是 `id` 的用法。鱼运算符的参数不是应该“吃普通类型、吐修饰类型”吗？其实未必。
没有人规定 `α → Writer β` 中的 `α` 必须是“普通”类型。它是类型变量，可以是任何类型，
特别地，它也可以是一个修饰过的类型，比如 `Writer β`。

于是 `id` 接收一个 `Writer α`，原样交出这个 `Writer α`。鱼运算符把其中的 `α` 值“钓”出来，作为 `x` 传给 lambda。
在那里，`f` 把它变成 `β`，`ret` 再给它加上修饰，成为 `Writer β`。全部拼起来，我们得到一个吃 `Writer α`、
吐 `Writer β` 的函数——正是 `map` 应该产出的东西。

在 Lean 里，我们可以把这段口头推理换成证明：这个从鱼和 `ret` 里“钓”出来的 `fmap`，恰好就是“只改第一个分量、日志原样保留”：

```lean
theorem Writer.fmap_eq (f : α → β) (a : α) (s : String) :
    Writer.fmap f (a, s) = (f a, s) := by
  -- 展开后得到 (f a, s ++ "")，再用 s ++ "" = s
  show (f a, s ++ "") = (f a, s)
  rw [String.append_empty]
```

顺带证明它满足函子定律：

```lean
theorem Writer.fmap_id (w : Writer α) : Writer.fmap id w = w := by
  obtain ⟨a, s⟩ := w           -- 把 w 拆成 (a, s)
  rw [Writer.fmap_eq]; rfl

theorem Writer.fmap_comp (f : α → β) (g : β → γ) (w : Writer α) :
    Writer.fmap (g ∘ f) w = Writer.fmap g (Writer.fmap f w) := by
  obtain ⟨a, s⟩ := w
  rw [Writer.fmap_eq, Writer.fmap_eq, Writer.fmap_eq]; rfl
```

注意这个论证非常一般：你可以把 `Writer` 换成任何类型构造器。只要它支持鱼运算符和 `return`，
你就能定义出 `map`。所以 Kleisli 范畴中的修饰总是函子。（不过反过来，并不是每个函子都能产生 Kleisli 范畴。）

在 Lean 里，“任何支持鱼和 `return` 的类型构造器”可以直接写成一个结构，`fmap` 的构造只用写一次：

```lean
structure KleisliOps (m : Type → Type) where
  fish : {α β γ : Type} → (α → m β) → (β → m γ) → (α → m γ)
  ret : {α : Type} → α → m α

def KleisliOps.fmap {m : Type → Type} (k : KleisliOps m) (f : α → β) : m α → m β :=
  k.fish id (fun x => k.ret (f x))

def writerOps : KleisliOps Writer := ⟨fish, ret⟩

example : writerOps.fmap (· + 1) ((1, "log") : Writer Nat) = (2, "log") := by
  show (2, "log" ++ "") = (2, "log"); rfl
```

你也许想知道：我们刚定义的 `fmap`，和编译器用 `deriving Functor` 替我们派生的那个 `fmap`，是不是同一个？
有意思的是，**是**。这源于 Haskell 实现多态函数的方式，叫**参数多态**（parametric polymorphism），
它是所谓“**免费定理**”（theorems for free）的来源。其中一条免费定理说：如果某个类型构造器有一个保持恒等的 `fmap` 实现，
那么这个实现必定是唯一的。

::: tip Lean 深入：免费定理在 Lean 里“免费”吗？
参数多态的直觉是：一个类型为 `∀ α, List α → List α` 的函数**看不见** `α` 的值是什么，所以只能挪动、复制、丢弃元素，
而不能凭空捏造或检查它们。由此能推出很多“免费”的等式。

Lean 的多态函数在运行时同样是参数化的，但这条原理**不能在 Lean 内部被证明**：参数性是关于“所有可能的程序”的元定理，
而不是某个具体命题。（Lean 甚至允许一些破坏参数性的公理，例如经典逻辑里的选择公理。）
所以在 Lean 中，我们不靠“免费定理”，而是像上面那样，对具体的 `fmap` 实打实地证明它等于我们期望的那个函数。
:::

## 协变与逆变函子

回顾完 writer 函子，我们再回到 reader 函子。它基于部分应用的函数箭头类型构造器：

```lean no-check
(r → ·)      -- 固定参数类型 r，变化结果类型
```

我们可以把它改写成一个类型别名：

```lean
def Reader (r a : Type) := r → a
```

正如我们之前看到的，它的 `Functor` 实例是这样的——`map` 就是函数复合，在 `g` 的结果上再接一个 `f`：

```lean
instance : Functor (Reader r) where
  map f g := f ∘ g
```

但就像积类型构造器或者 `Sum` 类型构造器一样，函数类型构造器也吃两个类型参数。
积和 `Sum` 在两个参数上都是函子性的——它们是双函子。那函数类型构造器也是双函子吗？

我们试试让它在第一个参数上具有函子性。先来一个类型别名——就像 `Reader`，只是参数顺序反过来：

```lean
def Op (r a : Type) := a → r
```

这一回我们固定返回类型 `r`，变化参数类型 `a`。看看能不能凑出类型来实现 `map`，它应该有如下签名：

```lean no-check
map : (a → b) → (a → r) → (b → r)
```

手上只有两个函数，都吃 `a`，一个吐 `b`，一个吐 `r`——根本不可能造出一个吃 `b`、吐 `r` 的函数！
不信可以在 Lean 里试试：你手上有 `f : a → b`、`g : a → r` 和一个 `y : b`，要交出一个 `r`。
可是唯一能产出 `r` 的 `g` 要的是 `a`，而你没有任何办法从 `b` 得到 `a`。

```lean no-check
-- 写不出来：没有任何项能填进这个洞
def badMap (f : a → b) (g : a → r) : b → r := fun y => g ?_
```

要是能把第一个函数反过来，让它吃 `b` 吐 `a`，事情就不一样了。我们没法把任意函数反转，但我们可以去对偶范畴。

简单复习一下：每个范畴 $\mathcal{C}$ 都有一个对偶范畴 $\mathcal{C}^{op}$。它的对象和 $\mathcal{C}$ 相同，
但所有箭头都反了过来。在本书的公共前导里它是这样定义的（`Op C` 就是 `C` 本身，只是 `Hom a b` 被定义为原范畴中的 `Hom b a`）：

```lean no-check
def Op (C : Type u) : Type u := C

instance opCategory (C : Type u) [Category.{u, v} C] : Category.{u, v} (Op C) where
  Hom a b := @Category.Hom C _ b a          -- 箭头反向
  id a := @Category.id C _ a
  comp g f := @Category.comp C _ _ _ _ f g  -- 复合顺序也随之反向
  -- 三条定律由原范畴的定律直接得到（略）
```

考虑一个从 $\mathcal{C}^{op}$ 到另一个范畴 $\mathcal{D}$ 的函子：

$$F : \mathcal{C}^{op} \to \mathcal{D}$$

这样的函子把 $\mathcal{C}^{op}$ 中的态射 $f^{op} : a \to b$ 映到 $\mathcal{D}$ 中的态射 $F f^{op} : F a \to F b$。
但 $f^{op}$ 暗地里对应着原范畴 $\mathcal{C}$ 中的某个态射 $f : b \to a$。注意方向反了。

现在，$F$ 是个正常的函子；但基于 $F$ 我们还能定义另一个映射，它**不是**函子——叫它 $G$ 吧。它是从 $\mathcal{C}$
到 $\mathcal{D}$ 的映射。它对对象的映射和 $F$ 一样，但映射态射时会把态射反过来：它拿到 $\mathcal{C}$ 中的态射 $f : b \to a$，
先把它映到对偶态射 $f^{op} : a \to b$，再用函子 $F$ 作用其上，得到 $F f^{op} : F a \to F b$。

```diagram
b: (0, 0) "b"
a: (2, 0) "a"
a2: (0, 1.6) "a"
b2: (2, 1.6) "b"
Fa: (0, 3.2) "G\,a = F\,a"
Fb: (2, 3.2) "G\,b = F\,b"
f: b -> a "f" color=brand
fop: a2 -> b2 "f^{op}" color=orange
Ff: Fa -> Fb "F f^{op} = G f" color=green
caption: 上：C 中的 f : b → a；中：C^op 中的 f^op : a → b；下：D 中的 G f : G a → G b。G 把 f 的方向“翻”了过来。
```

既然 $F a$ 就是 $G a$，$F b$ 就是 $G b$，整个过程可以描述为：

$$G f : (b \to a) \to (G a \to G b)$$

这是一个“拧了一下”的函子。以这种方式把态射方向反过来的范畴间映射，叫作**逆变函子**（contravariant functor）。
注意，逆变函子不过是从对偶范畴出发的一个普通函子。顺便说一句，普通的函子——也就是我们一直在研究的那种——叫作**协变函子**（covariant functor）。

![逆变函子](/img/1.8/contravariant.jpg "逆变函子：C 中的箭头 f : b → a 被映成 D 中方向相反的箭头 G f : G a → G b。")

下面是定义逆变函子（准确地说，是逆变**自**函子）的类型类：

```lean
class Contravariant (f : Type → Type) where
  contramap : (b → a) → f a → f b
```

我们的类型构造器 `Op` 是它的一个实例：

```lean
instance : Contravariant (Op r) where
  -- 类型：(b → a) → Op r a → Op r b
  contramap f g := g ∘ f
```

注意，函数 `f` 把自己插到了 `Op` 的内容——函数 `g`——的**前面**（也就是 `∘` 的右边）。

如果你注意到它只是参数顺序翻转了的函数复合运算符，`Op` 的 `contramap` 定义还能写得更简洁。
有一个专门翻转参数的函数，叫 `flip`（Lean 核心库自带）：

```lean no-check
def flip (f : α → β → φ) : β → α → φ := fun b a => f a b
```

有了它，我们得到：

```lean
example : (Contravariant.contramap : (b → a) → Op r a → Op r b) = flip (· ∘ ·) := rfl
```

`rfl` 说明这两者在定义上就是同一个函数。

逆变函子的定律和协变函子一样有两条，只是复合的顺序反过来——这正是“从对偶范畴出发的函子”的意思：

```lean
class LawfulContravariant (f : Type → Type) [Contravariant f] : Prop where
  contramap_id : ∀ {a : Type}, Contravariant.contramap (@id a) = @id (f a)
  -- 注意右边的顺序：先 contramap g，再 contramap h
  contramap_comp : ∀ {a b c : Type} (g : b → a) (h : c → b),
    Contravariant.contramap (g ∘ h) =
      (Contravariant.contramap h ∘ Contravariant.contramap g : f a → f c)

instance : LawfulContravariant (Op r) where
  contramap_id := rfl
  contramap_comp _ _ := rfl
```

最后，用本书的 `CFunctor` 把“逆变函子 = 从对偶范畴出发的普通函子”这句话**字面地**写出来：
`(· → r)` 是一个从 $\mathbf{Type}^{op}$ 到 $\mathbf{Type}$ 的（协变！）函子。在 $\mathbf{Type}^{op}$ 中，
从 `a` 到 `b` 的箭头就是一个普通函数 `b → a`：

```lean
def opFunctor (r : Type) : CFunctor (CTFP.Op Type) Type where
  obj a := a → r
  map f g := g ∘ f        -- f : b → a（Type^op 中的 a ⟶ b），g : a → r
  map_id _ := rfl
  map_comp _ _ := rfl
```

两条函子定律依旧是 `rfl`。“拧一下”的部分完全被对偶范畴吸收了。

下面这个组件把两种方向放在一起比较。选一个 $f : a \to b$，然后分别播放协变和逆变的情形，看看被提升后的箭头指向哪边：

<div><Ch1_8Variance /></div>

::: tip Rust 视角：Rust 里也有协变与逆变
Rust 的类型系统在**子类型**（主要是生命周期）上就有协变/逆变的概念，Rust 参考手册里有一张“型变表”：

- `Vec<T>`、`Box<T>`、`Option<T>`、`fn() -> T` 对 `T` **协变**：`&'static str` 可以当成 `&'a str` 用，
  那么 `Vec<&'static str>` 也可以当成 `Vec<&'a str>` 用——方向一致；
- `fn(T)` 对 `T` **逆变**：一个能接受**任何** `&'a str` 的函数，当然能在只需要接受 `&'static str` 的地方使用——方向反了；
- `fn(T) -> U` 对 `T` 逆变、对 `U` 协变——这正是下一节要讲的剖函子的形状。

道理和本节完全一样：容器里“产出” `T`，就随 `T` 同向变化；函数“消费” `T`，就逆向变化。
:::

## 剖函子

我们已经看到，函数箭头运算符在第一个参数上逆变，在第二个参数上协变。这样的怪兽有名字吗？
原来，如果目标范畴是 $\mathbf{Set}$，这种怪兽就叫**剖函子**（profunctor）。由于逆变函子等价于从对偶范畴出发的协变函子，
剖函子定义为：

$$\mathcal{C}^{op} \times \mathcal{D} \to \mathbf{Set}$$

既然在一阶近似下 Lean 的类型就是集合，我们就把 `Profunctor` 这个名字用在一个双参数的类型构造器 `p` 上：
它在第一个参数上逆函子性，在第二个参数上函子性。下面是对应的类型类，仿照 Haskell 的 `Data.Profunctor` 库：

```lean
class Profunctor (p : Type → Type → Type) where
  dimap : (a → b) → (c → d) → p b c → p a d := fun f g => lmap f ∘ rmap g
  lmap : (a → b) → p b c → p a c := fun f => dimap f id
  rmap : (b → c) → p a b → p a c := fun g => dimap id g
```

三个函数都有默认实现。和 `Bifunctor` 一样，声明 `Profunctor` 实例时，你可以选择实现 `dimap` 并接受 `lmap` 和 `rmap` 的默认实现，
或者实现 `lmap` 和 `rmap` 并接受 `dimap` 的默认实现。

![dimap](/img/1.8/dimap.jpg "dimap：在 p b c 的输入端前面接上 f : a → b，在输出端后面接上 g : c → d，得到 p a d。")

现在我们可以宣布，函数箭头运算符是 `Profunctor` 的一个实例：

```lean
instance : Profunctor (fun a b => a → b) where
  dimap ab cd bc := cd ∘ bc ∘ ab
  lmap := flip (· ∘ ·)
  rmap := (· ∘ ·)

-- 先加一，再乘二，再转成字符串：dimap 把一个函数“夹”在两个函数中间
example : Profunctor.dimap (p := fun a b => a → b) (· + 1) toString (· * 2) 3 = "8" := rfl
```

::: tip Lean 深入：为什么要写 `(p := fun a b => a → b)`
Haskell 有一个专门的名字 `(->)` 表示“函数箭头这个类型构造器”。Lean 没有，所以我们用 lambda `fun a b => a → b` 表示它。
问题是，当 Lean 看到一个函数 `Nat → Nat` 时，它没法反推出“这是 `?p Nat Nat`，而 `?p` 是 `fun a b => a → b`”——
这种高阶合一问题一般没有唯一解（`?p` 也可以是 `fun _ _ => Nat → Nat`！）。所以我们用命名参数 `(p := ...)` 显式告诉它。
:::

照例，把定律写成类型类并证明。和双函子一样，有恒等律和复合律，只是第一个参数上的复合顺序是反的：

```lean
class LawfulProfunctor (p : Type → Type → Type) [Profunctor p] : Prop where
  dimap_id : ∀ {a b : Type}, Profunctor.dimap (@id a) (@id b) = @id (p a b)
  dimap_comp : ∀ {a a' b c d d' : Type} (f₁ : a → b) (f₂ : a' → a) (g₁ : c → d) (g₂ : d → d'),
    Profunctor.dimap (f₁ ∘ f₂) (g₂ ∘ g₁) =
      (Profunctor.dimap f₂ g₂ ∘ Profunctor.dimap f₁ g₁ : p b c → p a' d')
  lmap_eq : ∀ {a b c : Type} (f : a → b), (Profunctor.lmap f : p b c → p a c) = Profunctor.dimap f id
  rmap_eq : ∀ {a b c : Type} (g : b → c), (Profunctor.rmap g : p a b → p a c) = Profunctor.dimap id g

instance : LawfulProfunctor (fun a b => a → b) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl
  lmap_eq _ := rfl
  rmap_eq _ := rfl
```

函数箭头的四条定律全都是 `rfl`——它们归根结底都是函数复合的结合律和单位律，而这些在 Lean 中按定义成立。

剖函子在 Haskell 的 lens 库中有用武之地。我们在讲端与余端时还会再见到它们。

## Hom 函子

上面这些例子，其实是一个更一般的命题的影子：把一对对象 $a$ 和 $b$ 映到它们之间的态射集合——hom-集 $\mathcal{C}(a, b)$——
的那个映射，是一个函子。它是从积范畴 $\mathcal{C}^{op} \times \mathcal{C}$ 到集合范畴 $\mathbf{Set}$ 的函子。

我们来定义它在态射上的作用。$\mathcal{C}^{op} \times \mathcal{C}$ 中的一个态射，是 $\mathcal{C}$ 中的一对态射：

$$f : a' \to a \qquad g : b \to b'$$

这一对态射被提升之后，必须是从集合 $\mathcal{C}(a, b)$ 到集合 $\mathcal{C}(a', b')$ 的一个态射（一个函数）。
只要从 $\mathcal{C}(a, b)$ 中任取一个元素 $h$（它是一个从 $a$ 到 $b$ 的态射），把它映到

$$g \circ h \circ f$$

就行了——这是 $\mathcal{C}(a', b')$ 中的一个元素。

```diagram
a': (0, 0) "a'"
a: (2, 0) "a"
b: (4, 0) "b"
b': (6, 0) "b'"
f: a' -> a "f" color=orange
h: a -> b "h"
g: b -> b' "g" color=brand
ghf: a' -> b' "g \circ h \circ f" bend=-52 side=right color=green
path "f，然后 h，然后 g": f h g
path "提升后的箭头 g∘h∘f": ghf color=green
caption: hom 函子在态射上的作用：在 h 的前面接上 f（逆变的一端），在后面接上 g（协变的一端）。
```

可以看出，hom 函子是剖函子的一个特例。

在 Lean 中，我们可以对**任意**范畴 `C` 写出这个函子，并证明它的函子定律。定律的证明只用到范畴自身的单位律和结合律：

```lean
theorem hom_id_lemma {C : Type u} [Category.{u, v} C] {a b : C} (h : a ⟶ b) :
    𝟙 b ⊚ (h ⊚ 𝟙 a) = h := by
  rw [Category.comp_id, Category.id_comp]

theorem hom_comp_lemma {C : Type u} [Category.{u, v} C] {a a' a'' b b' b'' : C}
    (f₁ : a' ⟶ a) (g₁ : a'' ⟶ a') (f₂ : b ⟶ b') (g₂ : b' ⟶ b'') (h : a ⟶ b) :
    (g₂ ⊚ f₂) ⊚ (h ⊚ (f₁ ⊚ g₁)) = g₂ ⊚ ((f₂ ⊚ (h ⊚ f₁)) ⊚ g₁) := by
  simp only [Category.assoc]  -- 全部重新加括号，两边就一样了

/-- hom 函子 C(-, =) : Cᵒᵖ × C → Type -/
def homFunctor (C : Type u) [Category.{u, v} C] : CFunctor (CTFP.Op C × C) (Type v) where
  obj p := @Category.Hom C _ p.1 p.2
  -- 一个态射是一对 (f, g)，f 在 Cᵒᵖ 中（即 C 中反向的箭头），g 在 C 中
  map fg := fun h => @Category.comp C _ _ _ _ fg.2 (@Category.comp C _ _ _ _ h fg.1)
  map_id _ := funext fun h => hom_id_lemma (C := C) h
  map_comp {p q r} f g := funext fun h =>
    @hom_comp_lemma C _ p.1 q.1 r.1 p.2 q.2 r.2 f.1 g.1 f.2 g.2 h
```

::: tip Lean 深入：`@` 与显式写出实例
`@Category.comp C _ ...` 中的 `@` 表示“把所有隐式参数都显式写出来”。这里之所以要这么啰嗦，是因为 `p.1` 的类型是 `CTFP.Op C`
而不是 `C`：虽然它们定义上相同，但如果让 Lean 自己推断，它可能会用 `Op C` 上的（反向的）范畴实例去复合，结果就乱套了。
显式写出 `C`，就锁定了“在原范畴里复合”。这类细节在纸面数学中通常被一笔带过，而证明助手会逼你把它说清楚。
:::

把 `C` 取成 `Type`，hom 函子就是我们的老朋友函数箭头 `a → b`，而 `map (f, g) h = g ∘ h ∘ f` 正是上一节的 `dimap f g h`。

## 挑战

1. 证明数据类型

   ```lean no-check
   structure Pair (a b : Type) where
     fst : a
     snd : b
   ```

   是一个双函子。附加题：实现 `Bifunctor` 的全部三个方法，并用等式推理证明：在能用默认实现的地方，这些定义与默认实现是相容的。

2. 证明标准的 `Option` 与下面这个“脱糖”版本同构：

   ```lean no-check
   abbrev Maybe' (a : Type) := Sum (Const Unit a) (Identity a)
   ```

   提示：在两种实现之间各定义一个映射。附加题：用等式推理证明它们互为逆映射。

3. 我们再试一个数据结构。我管它叫 `PreList`，因为它是 `List` 的前身。它用类型参数 `b` 取代了递归：

   ```lean no-check
   inductive PreList (a b : Type) where
     | nil : PreList a b
     | cons : a → b → PreList a b
   ```

   把 `PreList` 递归地作用到它自身上，就能恢复我们之前的 `List`（讲不动点时我们会看到怎么做）。
   证明 `PreList` 是 `Bifunctor` 的实例。

4. 证明下面这些数据类型定义了 `a` 和 `b` 上的双函子：

   ```lean no-check
   structure K2 (c a b : Type) where val : c
   structure Fst (a b : Type) where val : a
   structure Snd (a b : Type) where val : b
   ```

   附加题：拿你的答案对照 Conor McBride 的论文 [Clowns to the Left of me, Jokers to the Right](http://strictlypositive.org/CJ.pdf)。

5. 在 Lean 之外的另一门语言中定义一个双函子。为该语言中的泛型对实现 `bimap`。

6. C++ 的 `std::map<Key, T>`（对应 Rust 的 `BTreeMap<K, V>` / `HashMap<K, V>`）在两个模板参数 `Key` 和 `T` 上，
   应该被视为双函子还是剖函子？你会如何重新设计这个数据类型，使它成为那样的东西？

::: details 参考答案 1：`Pair` 是双函子
三个方法都自己实现，然后逐一证明它们与默认实现相容（也就是 `LawfulBifunctor` 中的 `first_eq`、`second_eq`，
外加“`bimap` 等于默认的 `first g ∘ second h`”）：

```lean
structure Pair (a b : Type) where
  fst : a
  snd : b

instance : Bifunctor Pair where
  bimap g h p := ⟨g p.fst, h p.snd⟩
  first g p := ⟨g p.fst, p.snd⟩
  second h p := ⟨p.fst, h p.snd⟩

instance : LawfulBifunctor Pair where
  bimap_id := rfl
  bimap_comp _ _ _ _ := rfl
  -- first g = bimap g id：
  --   first g ⟨x, y⟩ = ⟨g x, y⟩ = ⟨g x, id y⟩ = bimap g id ⟨x, y⟩
  first_eq _ := rfl
  -- second h = bimap id h：同理
  second_eq _ := rfl

-- bimap 与默认实现 first g ∘ second h 相容：
--   (first g ∘ second h) ⟨x, y⟩ = first g ⟨x, h y⟩ = ⟨g x, h y⟩ = bimap g h ⟨x, y⟩
theorem Pair.bimap_default (g : a → c) (h : b → d) :
    (bimap g h : Pair a b → Pair c d) = first g ∘ second h := rfl
```

每一步“等式推理”都只是展开定义，所以 Lean 用一个 `rfl` 就全部验证了。注释里写的就是手工推导的过程。
:::

::: details 参考答案 2：`Option a ≅ Maybe' a`
```lean
def toMaybe' : Option a → Maybe' a
  | none => .inl ⟨()⟩
  | some x => .inr ⟨x⟩

def fromMaybe' : Maybe' a → Option a
  | .inl _ => none
  | .inr ⟨x⟩ => some x

theorem from_to (o : Option a) : fromMaybe' (toMaybe' o) = o := by
  cases o <;> rfl

theorem to_from (m : Maybe' a) : toMaybe' (fromMaybe' m) = m := by
  -- inl 的情形里装的是 ⟨()⟩，而 Unit 只有一个值，所以必然还原成同一个东西
  rcases m with ⟨⟨⟩⟩ | ⟨x⟩ <;> rfl
```

`rcases` 是“递归版的 `cases`”：一个图案 `⟨⟨⟩⟩ | ⟨x⟩` 同时拆开了 `Sum` 的两种情形、`Const` 结构体和其中的 `Unit`。
注意 `to_from` 的证明关键在于 `Unit` 只有一个元素：若 `Const` 的第一个参数换成 `Bool`，这个同构就不成立了。

更进一步，这个同构还和 `map` 相容（它是一个“自然”同构，[1.10 章](/part1/10-natural-transformations)会正式定义）：

```lean
instance : Functor Maybe' where
  map f := Bifunctor.bimap (Functor.map f) (Functor.map f)

theorem toMaybe'_natural (f : a → b) (o : Option a) :
    toMaybe' (f <$> o) = f <$> toMaybe' o := by
  cases o <;> rfl
```
:::

::: details 参考答案 3：`PreList` 是双函子
```lean
inductive PreList (a b : Type) where
  | nil : PreList a b
  | cons : a → b → PreList a b

instance : Bifunctor PreList where
  bimap f g
    | .nil => .nil
    | .cons x y => .cons (f x) (g y)

instance : LawfulBifunctor PreList where
  bimap_id := by intro a b; funext l; cases l <;> rfl
  bimap_comp _ _ _ _ := by funext l; cases l <;> rfl
  first_eq _ := rfl
  second_eq _ := rfl
```

用积木的眼光看：`PreList a b ≅ Const Unit ⊕ (a × b)`——一个常函子与积双函子的和。所以它的双函子性也可以直接由本章的构造推出。
:::

::: details 参考答案 4：`K2`、`Fst`、`Snd`
```lean
structure K2 (c a b : Type) where
  val : c
structure Fst (a b : Type) where
  val : a
structure Snd (a b : Type) where
  val : b

instance : Bifunctor (K2 c) where
  bimap _ _ x := ⟨x.val⟩            -- 两个函数都用不上
instance : Bifunctor Fst where
  bimap f _ x := ⟨f x.val⟩          -- 只用得上第一个函数
instance : Bifunctor Snd where
  bimap _ g x := ⟨g x.val⟩          -- 只用得上第二个函数

instance : LawfulBifunctor (K2 c) where
  bimap_id := rfl
  bimap_comp _ _ _ _ := rfl
  first_eq _ := rfl
  second_eq _ := rfl
instance : LawfulBifunctor Fst where
  bimap_id := rfl
  bimap_comp _ _ _ _ := rfl
  first_eq _ := rfl
  second_eq _ := rfl
instance : LawfulBifunctor Snd where
  bimap_id := rfl
  bimap_comp _ _ _ _ := rfl
  first_eq _ := rfl
  second_eq _ := rfl
```

在 McBride 的论文里，`K2` 叫作常量双函子（Haskell 中写作 `K₂`），`Fst` 和 `Snd` 是两个投影双函子（分别只“看”左边或右边的参数）。
它们与双函子的和、积一起，构成了描述“左边是小丑（已处理的元素）、右边是小丑牌（待处理的元素）”这类结构的积木。
:::

::: details 参考答案 5：Rust 中的双函子
Rust 中可以为具体的泛型对实现 `bimap`。`first`/`second` 也可以顺手给出：

```rust
#[derive(Debug, Clone, PartialEq)]
pub struct Pair<A, B>(pub A, pub B);

impl<A, B> Pair<A, B> {
    pub fn bimap<C, D>(self, f: impl FnOnce(A) -> C, g: impl FnOnce(B) -> D) -> Pair<C, D> {
        Pair(f(self.0), g(self.1))
    }
    pub fn first<C>(self, f: impl FnOnce(A) -> C) -> Pair<C, B> {
        self.bimap(f, |b| b)
    }
    pub fn second<D>(self, g: impl FnOnce(B) -> D) -> Pair<A, D> {
        self.bimap(|a| a, g)
    }
}

pub fn demo() -> bool {
    let p = Pair(20, "hi");
    let q = p.clone().bimap(|n| n + 22, |s: &str| s.len());
    let r = p.first(|n| n + 22).second(|s: &str| s.len());
    q == r && q == Pair(42, 2)
}
```

如果想要一个“对所有双函子通用”的 trait，就又撞上了高阶类型的墙；用 GAT 能写，但同样阻止不了实现者“撒谎”：

```rust
pub trait Bifunctor {
    type L;
    type R;
    type Out<C, D>;
    fn bimap<C, D>(self, f: impl FnOnce(Self::L) -> C, g: impl FnOnce(Self::R) -> D) -> Self::Out<C, D>;
}

impl<A, B> Bifunctor for Result<A, B> {
    type L = A;
    type R = B;
    type Out<C, D> = Result<C, D>;
    fn bimap<C, D>(self, f: impl FnOnce(A) -> C, g: impl FnOnce(B) -> D) -> Result<C, D> {
        self.map(f).map_err(g)
    }
}
```
:::

::: details 参考答案 6：`std::map` / `BTreeMap` 是什么？
**值参数 `T`（Rust 的 `V`）**：映射是**协变**的，可以对每个值应用 `f : V → W`，得到 `BTreeMap<K, W>`，且满足函子定律。
所以 `BTreeMap<K, ·>` 是函子。

**键参数 `Key`（Rust 的 `K`）**：这里就麻烦了。

- 想**协变**地映射键（`f : K → K'`）？如果 `f` 不是单射，两个不同的键可能被映到同一个新键，其中一个值就丢了；
  而且新键类型还得满足 `Ord`（或 `Hash + Eq`）。`map id` 没问题，但 `map (g ∘ f)` 和 `map g ∘ map f` 在冲突时可能保留不同的值，
  并且这个操作根本不对所有类型都有定义——所以它不是函子。
- 想**逆变**地映射键？`BTreeMap` 是一份有限的数据，而不是一个函数，没法“在查找之前先把键变换一下”。

所以 `std::map` 原样既不是双函子也不是剖函子。但如果把它看成它**所表示的东西**——一个偏函数 `K → Option<V>`（查找操作）——
它就是剖函子了：在键上逆变（先把查询的键变换一下再去查），在值上协变（查到之后再变换结果）。

重新设计：把映射表**表示为它的查找函数**。

```rust
pub struct Lookup<K, V>(pub Box<dyn Fn(&K) -> Option<V>>);

impl<K: 'static, V: 'static> Lookup<K, V> {
    /// dimap：键上逆变（f: K2 → K），值上协变（g: V → V2）
    pub fn dimap<K2: 'static, V2: 'static>(
        self,
        f: impl Fn(&K2) -> K + 'static,
        g: impl Fn(V) -> V2 + 'static,
    ) -> Lookup<K2, V2> {
        let inner = self.0;
        Lookup(Box::new(move |k2: &K2| inner(&f(k2)).map(&g)))
    }
}

pub fn from_map(m: std::collections::BTreeMap<String, i32>) -> Lookup<String, i32> {
    Lookup(Box::new(move |k: &String| m.get(k).copied()))
}
```

同样的设计在 Lean 里是一个剖函子实例，定律照例按定义成立：

```lean
def Lookup (k v : Type) := k → Option v

instance : Profunctor Lookup where
  dimap f g m := fun k => g <$> m (f k)

def table : Lookup String Nat := fun k => if k = "one" then some 1 else none

-- 先把 Nat 键转成字符串查表，查到后把结果加 100
example : Profunctor.dimap (p := Lookup) (fun (n : Nat) => if n = 1 then "one" else "?")
    (· + 100) table 1 = some 101 := rfl
```

（`dimap_id` 需要 `Option` 的 `id <$> o = o`，`dimap_comp` 需要 `Option` 的 `comp_map`——也就是说，`Lookup` 的剖函子定律
恰好继承自 `Option` 的函子定律。）
:::

## 本章小结

- **双函子**是两个参数的函子，等价于从积范畴 $\mathcal{C} \times \mathcal{D}$ 出发的函子；积范畴的态射是态射对，逐分量复合。
- Lean 中的 `Bifunctor` 有 `bimap`、`first`、`second` 三个方法，默认实现互相引用；`LawfulBifunctor` 把定律写进类型，
  由此可以**证明** `first` 与 `second` 可交换。仅仅“分别是函子”并不保证这一点（预幺半范畴）。
- **积**（`Prod`）与**余积**（`Sum`）都是双函子；幺半范畴要求它的张量积是双函子。
- 代数数据类型由 `Const`、`Identity` 两块积木经和、积搭成，所以天然具有函子性；`Option ≅ Const Unit ⊕ Identity`。
  Lean 核心库没有 `deriving Functor`，我们按积木法则手写 `map`，并用归纳法证明 `LawfulFunctor`。
- Rust 缺少高阶类型，只能为具体类型分别写 `map`；用 GAT 模拟的 `Functor` trait 无法约束“同一个类型构造器”，更无法表达定律。
- Kleisli 范畴中的修饰总是函子：`fmap f = id >=> (ret ∘ f)`，我们在 Lean 中证明了它就是 `Writer` 的自然 `map`。
- **逆变函子**把箭头反向，它就是从对偶范畴出发的普通函子；`(· → r)` 是逆变的，`contramap = flip (· ∘ ·)`。
- **剖函子** $\mathcal{C}^{op} \times \mathcal{D} \to \mathbf{Set}$：第一个参数逆变、第二个协变，函数箭头是典型例子，`dimap f g h = g ∘ h ∘ f`。
- **hom 函子** $\mathcal{C}(-, =) : \mathcal{C}^{op} \times \mathcal{C} \to \mathbf{Set}$ 是剖函子的特例，我们对任意范畴证明了它的函子定律。
