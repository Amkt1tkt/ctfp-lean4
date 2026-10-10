# 3.3 自由/遗忘伴随

伴随最有威力的用途之一，是构造“自由”的东西。**自由函子**（free functor）的定义很干脆：它就是某个**遗忘函子**（forgetful functor）的左伴随。
而遗忘函子通常朴素得近乎无聊——它做的唯一一件事，就是把某些结构“忘掉”。

为什么会有东西可忘？因为许多有趣的范畴是搭在集合之上的。范畴论里的对象把这些集合抽象掉了：对象没有内部结构，没有“元素”。
但它们往往还保留着对集合的记忆——意思是，存在一个从这个范畴 $\mathcal{C}$ 到 $\mathbf{Set}$ 的映射，也就是一个函子。
$\mathcal{C}$ 中某个对象所对应的那个集合，叫作它的**底层集合**（underlying set）。

幺半群就是这样一种有底层集合（元素的集合）的对象。存在一个从幺半群范畴 $\mathbf{Mon}$ 到集合范畴的遗忘函子 $U$：它把每个幺半群映到它的底层集合，
把每个幺半群态射（同态）映到底层集合之间的函数——仅仅是“把它当成普通函数来看”。

我喜欢把 $\mathbf{Mon}$ 想象成一个“双重人格”的家伙。一方面，它是一堆配备了乘法和单位元的集合；另一方面，它又是一个范畴，
里面的对象毫无特征，所有结构都编码在对象之间的态射里。每一个保持乘法和单位元的集合函数，都对应 $\mathbf{Mon}$ 中的一个态射。

有两点要记在心里：

- 可能有许多不同的幺半群对应到**同一个**集合；
- 幺半群态射的数量**少于**（至多等于）它们底层集合之间函数的数量。

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
```

先用 Lean 把这些东西写下来。核心库里没有 `Monoid`，我们在自己的命名空间里定义一个（[2.3 自由幺半群](/part2/03-free-monoids) 中见过类似的定义）。
和 Haskell 的 `Monoid` 类型类不同，Lean 版本把三条定律也放进了类里——实例必须带着证明才能成立：

```lean
namespace Free

class Monoid (m : Type) where
  one : m
  mul : m → m → m
  one_mul : ∀ x : m, mul one x = x
  mul_one : ∀ x : m, mul x one = x
  mul_assoc : ∀ x y z : m, mul (mul x y) z = mul x (mul y z)

infixl:70 " ⋆ " => Monoid.mul
notation "𝟏" => Monoid.one

open Monoid

-- 列表在拼接下构成幺半群
instance (α : Type) : Monoid (List α) where
  one := []
  mul := (· ++ ·)
  one_mul := List.nil_append
  mul_one := List.append_nil
  mul_assoc := List.append_assoc

-- 自然数在加法下构成幺半群
instance : Monoid Nat where
  one := 0
  mul := (· + ·)
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero
  mul_assoc := Nat.add_assoc
```

幺半群同态是“保持单位元和乘法”的函数。在 Lean 里，它是一个结构体：一个函数 `toFun`，外加两份证明。

```lean
structure MonoidHom (M N : Type) [Monoid M] [Monoid N] where
  toFun : M → N
  map_one : toFun 𝟏 = 𝟏
  map_mul : ∀ x y, toFun (x ⋆ y) = toFun x ⋆ toFun y

-- 让同态可以像函数一样直接作用：h x 而不是 h.toFun x
instance {M N : Type} [Monoid M] [Monoid N] :
    CoeFun (MonoidHom M N) (fun _ => M → N) where
  coe h := h.toFun
```

::: tip Lean 深入：`CoeFun`
`CoeFun` 是一个“强制转换”类型类：一旦为 `MonoidHom M N` 提供实例，你就可以把 `h : MonoidHom M N` 直接当函数写 `h x`，
Lean 会自动插入 `h.toFun`。这就是“遗忘函子”在语法层面的样子——把一个同态当普通函数用，正是“忘掉它保持结构这件事”。
:::

两个同态什么时候相等？结构体相等要求**每个字段**都相等。`toFun` 字段相等需要 `funext`；而两个证明字段是命题的证明，
由证明无关性自动相等。所以只要底层函数逐点相等，两个同态就相等。这条**外延性引理**（ext 引理）以后会反复用到：

```lean
@[ext] theorem MonoidHom.ext {M N : Type} [Monoid M] [Monoid N]
    {f g : MonoidHom M N}
    (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g    -- 把两个同态拆成各自的字段
  congr               -- 归结为逐个字段相等；证明字段由证明无关性自动解决
  funext x            -- 剩下的 toFun 字段：两个函数逐点相等
  exact h x
```

::: tip Lean 深入：`@[ext]` 与 `congr`
`congr` 把形如 `C a₁ a₂ … = C b₁ b₂ …` 的目标拆成 `a₁ = b₁`、`a₂ = b₂`…… 对于命题类型的字段，它会自动用证明无关性解决。
`@[ext]` 属性把这条定理登记为 `MonoidHom` 的外延性引理，以后在目标 `f = g`（`f g : MonoidHom M N`）上写 `ext x` 就会自动调用它。
:::

现在可以把 $\mathbf{Mon}$ 写成一个真正的范畴，并写出遗忘函子 $U$。我们把“一个类型连同它的幺半群结构”打包成一个对象：

```lean
def MonoidHom.id' (M : Type) [Monoid M] : MonoidHom M M :=
  ⟨fun x => x, rfl, fun _ _ => rfl⟩

def MonoidHom.comp' {M N P : Type} [Monoid M] [Monoid N] [Monoid P]
    (g : MonoidHom N P) (f : MonoidHom M N) : MonoidHom M P where
  toFun x := g (f x)
  map_one := by show g.toFun (f.toFun 𝟏) = 𝟏; rw [f.map_one, g.map_one]
  map_mul x y := by show g.toFun (f.toFun (x ⋆ y)) = _; rw [f.map_mul, g.map_mul]

/-- 范畴 Mon 的对象：一个类型，连同它上面的幺半群结构 -/
structure MonCat where
  carrier : Type
  [inst : Monoid carrier]

attribute [instance] MonCat.inst

instance : Category MonCat where
  Hom M N := MonoidHom M.carrier N.carrier
  id M := MonoidHom.id' M.carrier
  comp g f := MonoidHom.comp' g f
  -- 三条定律：两边的同态在定义上就相同，默认的 `by intros; rfl` 即可

/-- 遗忘函子 U : Mon → Type：幺半群 ↦ 底层类型，同态 ↦ 底层函数 -/
def forget : CFunctor MonCat Type where
  obj M := M.carrier
  map f := f.toFun
  map_id _ := rfl
  map_comp _ _ := rfl
```

::: info 数学小课堂：同一个集合，不同的幺半群
集合 $\mathbb{N}$ 上至少有两个常见的幺半群：$(\mathbb{N}, +, 0)$ 和 $(\mathbb{N}, \times, 1)$。遗忘函子 $U$ 把它们**都**送到同一个集合 $\mathbb{N}$——
这就是“多个幺半群对应同一个集合”。

再看态射的个数。从 $(\mathbb{N}, +, 0)$ 到它自己的同态 $h$，必须满足 $h(0) = 0$ 且 $h(x + y) = h(x) + h(y)$；这样的 $h$ 完全由 $h(1)$ 决定
（$h(n) = n \cdot h(1)$），所以同态与自然数一一对应。可是从 $\mathbb{N}$ 到 $\mathbb{N}$ 的**函数**多得多（比如 $n \mapsto n^2$ 就不是同态）。
这就是“态射比底层函数少”。
:::

与遗忘函子 $U$ 互为伴随的左边那位，就是**自由函子** $F$：它从一组生成元出发，构造出由它们生成的自由幺半群。这个伴随正是
我们在 [自由幺半群](/part2/03-free-monoids) 一章里讲过的泛构造，换了一种说法而已。

![遗忘函子](/img/3.3/forgetful.jpg "幺半群 m1 和 m2 有相同的底层集合。m2 与 m3 的底层集合之间的函数，比它们之间的幺半群态射更多。")

用 hom-集来写，这个伴随是：

$$\mathbf{Mon}(F x, m) \cong \mathbf{Set}(x, U m)$$

这个同构（对 $x$ 和 $m$ 都是自然的）告诉我们两件事：

- 从 $x$ 生成的自由幺半群 $F x$ 到任意幺半群 $m$ 的每一个同态，都唯一地对应一个函数：它把生成元集合 $x$ 嵌入 $m$ 的底层集合。这个函数属于 $\mathbf{Set}(x, U m)$。
- 反过来，每一个把 $x$ 嵌入某个 $m$ 的底层集合的函数，都唯一地对应一个从 $x$ 生成的自由幺半群到 $m$ 的幺半群态射。（这就是我们在泛构造里叫作 $h$ 的那个态射。）

![自由/遗忘伴随](/img/3.3/freemonadjunction.jpg "自由/遗忘伴随：左边 Mon 中从 F x 到 m 的同态，与右边 Set 中从 x 到 U m 的函数一一对应。")

直觉上，$F x$ 是以 $x$ 为基础能搭出来的“最大的”幺半群。如果我们能看到幺半群的内部，就会发现 $\mathbf{Mon}(F x, m)$ 中的任何态射，都是把这个自由幺半群
**嵌入**到另一个幺半群 $m$ 中——嵌入时可能会把某些元素“认同”成同一个。特别地，它把 $F x$ 的生成元（也就是 $x$ 的元素）嵌入 $m$。
伴随告诉我们：右边 $\mathbf{Set}(x, U m)$ 中那个“如何嵌入 $x$”的函数，唯一地决定了左边幺半群之间的嵌入；反之亦然。

在 Haskell 中，列表这种数据结构就是自由幺半群——不过要打一些折扣（参见 [Dan Doel 的博文](http://comonad.com/reader/2015/free-monoids-in-haskell/)：
惰性求值允许无限列表和 ⊥，它们会破坏“自由”）。在 Lean 中，这些折扣都不存在：`List α` 是严格的、有限的归纳类型，
它**就是**由 `α` 生成的自由幺半群，我们马上就能证明这一点。

列表类型 `List a` 是以类型 `a` 为生成元集合的自由幺半群。例如 `List Char` 里有单位元——空列表 `[]`——以及
`['a']`、`['b']` 这样的单元素列表，它们是这个自由幺半群的生成元。其余的元素都是对它们反复做“乘法”得到的。在这里，
两个列表的乘积就是把一个拼接到另一个后面。拼接满足结合律，也满足单位律（存在中性元，就是空列表）。由 `Char` 生成的自由幺半群，
无非是所有由 `Char` 中字符组成的字符串的集合。在 Haskell 里，它就叫 `String`：`type String = [Char]`（`type` 定义一个类型同义词——给已有类型起个新名字）。

::: tip Lean 深入：Lean 的 `String` 不是 `List Char`
在 Lean 4 中，`String` 为了效率被实现成 UTF-8 字节数组，并**不是** `List Char` 的别名。但它们之间有一对互逆的转换
`String.toList` 和 `List.asString`，而且字符串拼接与列表拼接相容：

```lean
#guard "ab".toList ++ "c".toList == "abc".toList
#guard ['a', 'b'].asString ++ "c" == "abc"
```

如果你真的想要一个类型同义词，Lean 的写法是 `abbrev MyString := List Char`。
:::

现在来证明本章的核心定理：**对任意类型 `α` 和任意幺半群 `M`，从 `List α` 到 `M` 的同态，与从 `α` 到 `M` 的函数一一对应**。

从右往左的方向需要我们从一个函数 `f : α → M` 造出一个同态。办法只有一个：把列表中的每个生成元用 `f` 送进 `M`，再用 `M` 的乘法乘起来。
这就是 `foldMap`：

```lean
/-- 把列表“解释”进幺半群 M：[x₁, x₂, …, xₙ] ↦ f x₁ ⋆ (f x₂ ⋆ (… ⋆ (f xₙ ⋆ 𝟏))) -/
def foldMap {α M : Type} [Monoid M] (f : α → M) : List α → M
  | [] => 𝟏
  | x :: xs => f x ⋆ foldMap f xs

/-- foldMap 把拼接变成乘法——它是同态的关键 -/
theorem foldMap_append {α M : Type} [Monoid M] (f : α → M) (xs ys : List α) :
    foldMap f (xs ++ ys) = foldMap f xs ⋆ foldMap f ys := by
  induction xs with
  | nil => exact (one_mul _).symm      -- [] ++ ys = ys，而 𝟏 ⋆ m = m
  | cons x xs ih =>                    -- 归纳假设 ih 针对较短的 xs
    show f x ⋆ foldMap f (xs ++ ys) = (f x ⋆ foldMap f xs) ⋆ foldMap f ys
    rw [ih, mul_assoc]                 -- 用 ih 改写，再用结合律重新加括号

/-- 由生成元函数 f 诱导的唯一同态（泛构造中的 h） -/
def lift {α M : Type} [Monoid M] (f : α → M) : MonoidHom (List α) M where
  toFun := foldMap f
  map_one := rfl
  map_mul := foldMap_append f
```

::: info 数学小课堂：对列表做归纳
要证明一个关于**所有**列表的命题 $P(xs)$，只需做两件事：

1. **起点**：证明 $P([\,])$；
2. **归纳步**：假设 $P(xs)$ 已经成立（归纳假设），证明 $P(x :: xs)$。

因为每个列表都是从 `[]` 出发，一次在前面加一个元素造出来的，这两步就像多米诺骨牌：第一块倒下，并且每块都会推倒下一块，于是全部倒下。
Lean 的 `induction xs with | nil => … | cons x xs ih => …` 正是这两步，`ih` 就是归纳假设。
:::

我们需要一个“同构”的结构体来表达一一对应（核心库没有 `Equiv`），然后就可以陈述并证明自由/遗忘伴随了：

```lean
structure Iso (α β : Type) where
  to : α → β
  inv : β → α
  inv_to : ∀ x, inv (to x) = x
  to_inv : ∀ y, to (inv y) = y

infix:25 " ≅ " => Iso

/-- 自由/遗忘伴随：Mon(List α, M) ≅ Set(α, U M) -/
def freeAdj (α M : Type) [Monoid M] : MonoidHom (List α) M ≅ (α → M) where
  -- 同态 ↦ 它在生成元（单元素列表）上的取值
  to h := fun x => h [x]
  -- 函数 ↦ 它诱导的同态
  inv f := lift f
  -- 先 lift 再限制到生成元：f x ⋆ 𝟏 = f x
  to_inv f := by
    funext x
    exact mul_one (f x)
  -- 先限制到生成元再 lift：得到原来的同态。需要 ext 与列表归纳
  inv_to h := by
    ext xs
    induction xs with
    | nil => exact h.map_one.symm                 -- 同态把 [] 送到 𝟏
    | cons x xs ih =>
      -- x :: xs 就是 [x] ⋆ xs，而 h 保持乘法
      show h.toFun [x] ⋆ foldMap (fun x => h.toFun [x]) xs = h.toFun ([x] ⋆ xs)
      rw [h.map_mul]
      exact congrArg (h.toFun [x] ⋆ ·) ih
```

这段证明值得慢慢读一遍，它把伴随的两句话都兑现了：

- `to_inv` 说的是：从一个生成元函数 `f` 出发，造出同态 `lift f`，再看它在生成元上的取值，得到的正是 `f`。也就是说，**同态被它在生成元上的取值完全记住**。
- `inv_to` 说的是：任何同态 `h`，都等于“由它在生成元上的取值重新 `lift` 出来的同态”。也就是说，**同态没有任何额外的自由度**——
  一旦生成元的去向定了，其余元素的去向都被“保持乘法”逼死了。证明正是沿着这个直觉走的：`x :: xs = [x] ++ xs`，所以 `h (x :: xs) = h [x] ⋆ h xs`，再对 `xs` 归纳。

::: tip Lean 深入：`congrArg`
`congrArg f h` 从 `h : a = b` 得到 `f a = f b`——“等量代入函数”。这里 `f` 是 `(h.toFun [x] ⋆ ·)`，也就是“左边乘上 `h [x]`”。
:::

一个伴随不仅要求是一一对应，还要求这个对应是**自然**的。两个方向的自然性都只需 `rfl`：

```lean
/-- 把生成元函数 g : α → β 提升成同态 List α → List β（这就是 F g） -/
def listMapHom {α β : Type} (g : α → β) : MonoidHom (List α) (List β) where
  toFun := List.map g
  map_one := rfl
  map_mul _ _ := List.map_append

/-- 对 M 自然：后接一个同态 k，等于在生成元函数后面接上 U k -/
theorem freeAdj_natural_m {α M N : Type} [Monoid M] [Monoid N]
    (k : MonoidHom M N) (h : MonoidHom (List α) M) :
    (freeAdj α N).to (k.comp' h) = k ∘ (freeAdj α M).to h := rfl

/-- 对 α 自然：前接 F g = List.map g，等于在生成元函数前面接上 g -/
theorem freeAdj_natural_x {α β M : Type} [Monoid M]
    (g : α → β) (h : MonoidHom (List β) M) :
    (freeAdj α M).to (h.comp' (listMapHom g))
      = (freeAdj β M).to h ∘ g := rfl
```

最后，用范畴的语言把它说完整：自由函子 $F$ 把类型 `α` 送到幺半群 `List α`，把函数 `g` 送到同态 `List.map g`；
而伴随就是 $\mathbf{Mon}(F\,\alpha, M) \cong \mathbf{Type}(\alpha, U M)$：

```lean
/-- 自由函子 F : Type → Mon -/
def free : CFunctor Type MonCat where
  obj α := ⟨List α⟩
  map g := listMapHom g
  map_id α := MonoidHom.ext fun (xs : List α) => List.map_id xs
  map_comp {α _ _} f g := MonoidHom.ext fun (xs : List α) => by
    show List.map (fun x => g (f x)) xs = List.map g (List.map f xs)
    simp

/-- F ⊣ U，用 CTFP 的范畴记号写出来 -/
def freeForget (α : Type) (M : MonCat) :
    (free.obj α ⟶ M) ≅ (α ⟶ forget.obj M) :=
  freeAdj α M.carrier
```

::: tip Rust 视角
在 Rust 里，`Vec<T>` 加上 `extend`（或迭代器的 `chain`）就是 `T` 生成的自由幺半群。而 `lift f` 就是

```rust
fn lift<T, M>(
    xs: &[T],
    f: impl Fn(&T) -> M,
    one: M,
    mul: impl Fn(M, M) -> M,
) -> M {
    xs.iter().rev().fold(one, |acc, x| mul(f(x), acc))
}
```

`Iterator::sum`、`Iterator::product`、`String: FromIterator<&str>` 都是它的特例：同一个“列表”，选不同的幺半群去解释它。
:::

另一个有趣的例子，是只由**一个**生成元构造的自由幺半群：单元类型的列表 `List Unit`。它的元素是 `[]`、`[()]`、`[(), ()]`，等等。
每个这样的列表都可以用一个自然数来描述——它的长度。除此之外，列表里没有编码任何别的信息。把两个这样的列表拼接起来，
得到的新列表的长度是两者长度之和。很容易看出，`List Unit` 同构于自然数的加法幺半群（含零）。下面是一对互逆的函数，它们见证了这个同构：

```lean
def toNat : List Unit → Nat := List.length
def toLst (n : Nat) : List Unit := List.replicate n ()

theorem toNat_toLst (n : Nat) : toNat (toLst n) = n :=
  List.length_replicate

theorem toLst_toNat (xs : List Unit) : toLst (toNat xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    -- x : Unit 只能是 ()
    show () :: toLst (toNat xs) = x :: xs
    rw [ih]

-- 不只是集合的同构：length 还是一个幺半群同态（拼接 ↦ 加法）
def lengthHom : MonoidHom (List Unit) Nat where
  toFun := toNat
  map_one := rfl
  map_mul _ _ := List.length_append
```

`List.replicate n x` 创建一个长度为 `n`、每一项都是 `x` 的列表——这里是 `()`。（原书为了简单用了 `Int` 而不是 `Natural`；
Lean 的 `Nat` 恰好就是我们想要的自然数，不需要妥协。）

## 一些直觉

下面是一些“比划着说”的论证。这类论证远远谈不上严格，但有助于形成直觉。

要获得对自由/遗忘伴随的直觉，记住这一点会很有帮助：函子和函数本质上都是**有损**的。函子可能把多个对象和态射压成一个，
函数可能把集合中的多个元素归拢到一起。而且，它们的像可能只覆盖其陪域的一部分。

$\mathbf{Set}$ 中一个“普通”的 hom-集，里面装着一整条光谱的函数：一端是损失最少的（比如单射，甚至同构），另一端是常函数——
它把整个定义域压成一个元素（如果陪域里有元素的话）。

我倾向于把任意范畴中的态射也想成是有损的。这只是一种心智模型，但很有用，尤其是在思考伴随的时候——特别是其中一个范畴是 $\mathbf{Set}$ 的伴随。

严格地说，我们只能谈论可逆的态射（同构）和不可逆的态射。可以把后一种想成是有损的。另外还有单态射和满态射的概念，
它们分别推广了单射（不压缩）和满射（覆盖整个陪域）的想法；但一个态射完全可能既是单态射又是满态射，却仍然不可逆。

::: info 数学小课堂：单射、满射、双射
- **单射**（injective）：不同的输入给出不同的输出，“不把两个元素压成一个”。例：`fun n : Nat => 2 * n`。
- **满射**（surjective）：陪域里每个元素都被取到，“覆盖整个陪域”。例：`fun n : Nat => n / 2`。
- **双射**（bijective）：既单又满，此时函数可逆。

在 $\mathbf{Set}$ 中，既单又满就等于可逆。但在一般范畴里，单态射 + 满态射未必是同构。经典例子是幺半群范畴里的包含同态
$(\mathbb{N}, +) \hookrightarrow (\mathbb{Z}, +)$：它既是单态射又是满态射，却没有逆（$-1$ 没有原像）。
:::

在自由 ⊣ 遗忘伴随中，左边是约束较多的范畴 $\mathcal{C}$，右边是约束较少的范畴 $\mathcal{D}$。$\mathcal{C}$ 中的态射“更少”，因为它们必须保持某些额外的结构。
在 $\mathbf{Mon}$ 的情形，它们必须保持乘法和单位元。$\mathcal{D}$ 中的态射不必保持那么多结构，所以“更多”。

当我们把遗忘函子 $U$ 作用于 $\mathcal{C}$ 中的对象 $c$ 时，我们把它想成是“揭示”了 $c$ 的“内部结构”。事实上，如果 $\mathcal{D}$ 是 $\mathbf{Set}$，
我们就把 $U$ 看作是在**定义** $c$ 的内部结构——它的底层集合。（在一般范畴里，除了通过对象与其他对象的联系，我们没法谈论对象的“内部”；
但这里我们只是比划比划。）

如果用 $U$ 映射两个对象 $c'$ 和 $c$，我们预期，一般来说 hom-集 $\mathcal{C}(c', c)$ 的像只覆盖 $\mathcal{D}(U c', U c)$ 的一个子集。
因为 $\mathcal{C}(c', c)$ 中的态射必须保持额外的结构，而 $\mathcal{D}(U c', U c)$ 中的态射不必。

![遗忘态射](/img/3.3/forgettingmorphisms.jpg "遗忘函子把 C(c′, c) 映进 D(U c′, U c)，通常只覆盖其中一部分。")

但既然伴随被定义为特定 hom-集之间的**同构**，我们在挑选 $c'$ 时就必须非常挑剔。在伴随中，$c'$ 不是从 $\mathcal{C}$ 中随便哪里挑出来的，
而是从自由函子 $F$ 的像（想必小得多）中挑出来的：

$$\mathcal{C}(F d, c) \cong \mathcal{D}(d, U c)$$

因此，$F$ 的像必须由这样的对象组成：从它们出发，有大量的态射通向任意的 $c$。事实上，从 $F d$ 到 $c$ 的保持结构的态射，
必须和从 $d$ 到 $U c$ 的不保持结构的态射一样多。这意味着 $F$ 的像必须由本质上“没有结构”的对象组成（这样态射就没有什么结构需要保持）。
这种“没有结构”的对象叫作**自由对象**（free objects）。

![自由函子的像](/img/3.3/freeimage.jpg "自由函子 F 的像：从 F d 出发的保持结构的态射，与从 d 到 U c 的普通函数一样多。")

在幺半群的例子里，自由幺半群除了单位律和结合律所产生的结构之外，没有任何别的结构。除此之外，所有的乘法都会产生全新的元素。

在自由幺半群里，$2 * 3$ 不是 $6$——它是一个新的元素 $[2, 3]$。因为 $[2, 3]$ 和 $6$ 之间没有被认同，从这个自由幺半群到任何别的幺半群 $m$ 的态射，
都可以把它们分别映到不同的地方。但同样可以把 $[2, 3]$ 和 $6$（它们的乘积）映到 $m$ 的同一个元素。或者，在加法幺半群里，
把 $[2, 3]$ 和 $5$（它们的和）认同起来，等等。不同的认同方式，给出不同的幺半群。

自己动手试试：用列表 A = `[2, 3]`、B = `[6]`，在不同的目标幺半群之间切换，看看哪些幺半群会把它们“认同”成同一个元素。

<Ch3_3FreeMonoidEval />

这引出了另一个有趣的直觉：自由幺半群并不执行幺半群运算，而是把传给运算的参数**积攒**起来。它不去把 $2$ 和 $3$ 乘起来，而是把 $2$ 和 $3$
记在一个列表里。这种做法的好处是，我们不必事先指定要用哪种幺半群运算。我们可以一直积攒参数，到最后才对结果施加某个运算。
到那时我们才来选用哪个运算：可以把数加起来，也可以乘起来，或者做模 2 加法，等等。自由幺半群把表达式的**构建**与表达式的**求值**分离开来。
我们在讲代数时还会再见到这个想法。

```lean
-- 同一个“未求值的表达式” [2, 3, 5]，用不同的幺半群去解释
-- 用加法解释
example : lift (M := Nat) (fun n => n) [2, 3, 5] = 10 := rfl

namespace Mul
-- 换一个实例：乘法幺半群（放进命名空间，避免和上面的加法实例冲突）
def mulMonoid : Monoid Nat where
  one := 1
  mul := (· * ·)
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  mul_assoc := Nat.mul_assoc

-- 用乘法解释
example : @lift Nat Nat mulMonoid (fun n => n) [2, 3, 5] = 30 := rfl
example : @lift Nat Nat mulMonoid (fun n => n) [2, 3]
        = @lift Nat Nat mulMonoid (fun n => n) [6] := rfl
end Mul

-- 而在自由幺半群里，[2, 3] 和 [6] 是不同的元素
example : ([2, 3] : List Nat) ≠ [6] := by decide
```

::: tip Lean 深入：显式传入实例
同一个类型 `Nat` 上可以有多个 `Monoid` 结构，但实例搜索一次只会找到一个（这里是我们注册的加法实例）。
需要别的结构时，可以用 `@lift Nat Nat mulMonoid …` 显式传入：`@` 关闭所有隐式参数，让你按顺序亲手填写，包括方括号里的实例参数。
这再次说明：**集合**（`Nat`）和**幺半群**（`Nat` 连同一种运算）是两回事——遗忘函子忘掉的，恰恰是后者多出来的那部分。
:::

这个直觉也可以推广到别的、更精巧的自由构造。例如，我们可以先把整棵表达式树积攒下来，再去求值。这种做法的好处是，
我们可以在求值之前变换这些树，让求值更快或更省内存。比如在实现矩阵运算时就会这么做：如果急切地求值，就会为了存放中间结果而分配大量临时数组。

::: tip 补充：表达式树也是一种自由构造
下面这个 `Expr` 就是“由变量生成的、带一个二元运算和一个常量的自由代数”（它比自由幺半群还要“自由”：连结合律都没有被认同）。
`eval` 在最后一刻才选定运算；`simplify` 则在求值前改写树（这里只是去掉乘以 1 的冗余）：

```lean
inductive Expr (α : Type) where
  | var : α → Expr α
  | one : Expr α
  | mul : Expr α → Expr α → Expr α

def Expr.eval {α M : Type} [Monoid M] (f : α → M) : Expr α → M
  | .var a => f a
  | .one => 𝟏
  | .mul e₁ e₂ => e₁.eval f ⋆ e₂.eval f

def Expr.simplify {α : Type} : Expr α → Expr α
  | .mul e₁ e₂ =>
    match e₁.simplify, e₂.simplify with
    | .one, e => e
    | e, .one => e
    | e₁', e₂' => .mul e₁' e₂'
  | e => e

example : (Expr.mul (.var 2) (.mul .one (.var 3))).eval (M := Nat) id = 5 := rfl
example :
    (Expr.mul (.var 2) (.mul .one (.var 3))).simplify.eval (M := Nat) id = 5 := rfl
```
:::

## 挑战

1. 考虑以单元素集合为生成元构造的自由幺半群。证明：从这个自由幺半群到任意幺半群 $m$ 的态射，与从单元素集合到 $m$ 的底层集合的函数之间，
   存在一一对应。

::: details 参考答案
这是自由/遗忘伴随在 $x = \mathrm{Unit}$ 时的特例，所以直接把 `freeAdj` 用在 `Unit` 上即可。进一步，“从单元素集合出发的函数”又与
$m$ 的元素一一对应，于是从 `List Unit`（也就是 $(\mathbb{N}, +, 0)$）出发的同态，完全由“$[()]$（也就是 $1$）被送到哪个元素”决定：

```lean
/-- 从单元素集合出发的函数 ≅ 一个元素 -/
def unitPoints (M : Type) : (Unit → M) ≅ M where
  to f := f ()
  inv m := fun _ => m
  inv_to _ := rfl
  to_inv _ := rfl

/-- 挑战的答案：Mon(List Unit, M) ≅ Set(Unit, U M) -/
def challenge (M : Type) [Monoid M] : MonoidHom (List Unit) M ≅ (Unit → M) :=
  freeAdj Unit M

/-- 更进一步：Mon(List Unit, M) ≅ U M，同态由 h [()] 唯一确定 -/
def challenge' (M : Type) [Monoid M] : MonoidHom (List Unit) M ≅ M where
  to h := h [()]
  inv m := lift (fun _ => m)
  inv_to h := (freeAdj Unit M).inv_to h
  to_inv m := mul_one m

-- 例：把 [()] 送到 3 的那个从 List Unit 到 (Nat, +, 0) 的同态，就是“乘以 3”
example : ((challenge' Nat).inv 3) [(), (), (), ()] = 12 := rfl
```

注意 `challenge'.inv_to` 直接借用了 `freeAdj` 的证明：两者底层的函数在定义上一模一样，Lean 能看出来。
最后那个例子说明，从自由幺半群 `List Unit ≅ ℕ` 到 $(\mathbb{N}, +, 0)$ 的同态，恰好是 $n \mapsto k \cdot n$，每个 $k$ 一个——
正如“数学小课堂”里说的那样。
:::

```lean hidden
end Free
```

## 本章小结

- **遗忘函子** $U$ 忘掉结构，只留下底层集合；**自由函子** $F$ 是它的左伴随：$\mathbf{Mon}(F x, m) \cong \mathbf{Set}(x, U m)$。
- 多个幺半群可以共享同一个底层集合；同态比底层函数少，因为它们要保持乘法和单位元。
- `List α` 就是 `α` 生成的自由幺半群。在 Lean 中这没有任何折扣（没有惰性、没有 ⊥、没有无限列表）。
- 核心定理 `freeAdj`：同态 `List α → M` 与函数 `α → M` 一一对应。一个方向是“限制到生成元”，另一个方向是 `lift f = foldMap f`；
  证明互逆需要 `funext`、列表归纳和同态的 `ext` 引理。两侧的自然性都是 `rfl`。
- `List Unit ≅ ℕ`（长度 / `replicate`），而且这是幺半群同构。
- 直觉：自由对象“没有多余的结构”，所以从它出发的保持结构的态射，和从生成元出发的普通函数一样多。
- 自由幺半群不计算，只积攒参数；同态在最后才选定运算，并可能把不同的元素“认同”起来。这把表达式的构建与求值分离开——表达式树、矩阵运算优化都用到这个思想。
