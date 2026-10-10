# 1.7 函子

冒着像一张卡了针的唱片一样反复念叨的风险，我还是要这样说函子：函子是一个非常简单、却非常强大的想法。
范畴论里满是这种简单而强大的想法。

**函子**（functor）是范畴之间的映射。给定两个范畴 $\mathcal{C}$ 和 $\mathcal{D}$，函子 $F$ 把 $\mathcal{C}$ 中的对象映到 $\mathcal{D}$ 中的对象——
它是对象上的一个函数。如果 $a$ 是 $\mathcal{C}$ 中的对象，我们把它在 $\mathcal{D}$ 中的像写作 $F a$（不加括号）。
但范畴不只是对象——它是对象，加上连接对象的态射。函子也要映射态射——它也是态射上的一个函数。
不过它不能随心所欲地映射态射——它必须**保持连接**。所以，如果 $\mathcal{C}$ 中的态射 $f$ 把对象 $a$ 连到对象 $b$：

$$f :: a \to b$$

那么 $f$ 在 $\mathcal{D}$ 中的像 $F f$ 就要把 $a$ 的像连到 $b$ 的像：

$$F f :: F a \to F b$$

（这里混用了数学记号和编程记号，希望到现在你已经看得惯了。把函子作用在对象或态射上时，我不加括号。
顺带一提，这和 Lean 的函数应用写法完全一致：`F a` 就是“把 `F` 作用在 `a` 上”。）

![函子 F 把范畴 C 中的 f : a → b 映成范畴 D 中的 F f : F a → F b](/img/1.7/functor.jpg "函子把 C 中的箭头 f : a → b 带到 D 中，成为箭头 F f : F a → F b。虚线表示对象被映到哪里。")

如你所见，函子保持了范畴的结构：在一个范畴里连在一起的东西，在另一个范畴里也连在一起。
但范畴的结构还不止于此：还有态射的复合。如果 $h$ 是 $f$ 和 $g$ 的复合：

$$h = g \circ f$$

我们希望它在 $F$ 下的像，是 $f$ 和 $g$ 的像的复合：

$$F h = F g \circ F f$$

![函子保持复合](/img/1.7/functorcompos.jpg "函子保持复合：先复合再映射，与先映射再复合，结果相同。")

用交换图来画，就是下面这样。下面一行在 $\mathcal{C}$ 里，上面一行是它在 $\mathcal{D}$ 里的像。
点按钮比较上面一行的两条路：先走 $F f$ 再走 $F g$，与直接走 $F(g \circ f)$，必须是同一个态射。

```diagram
padT: (1.6, -0.45) ""
padB: (1.6, 2.35) ""
Fa: (0, 0) "F a"
Fb: (1.6, 0) "F b"
Fc: (3.2, 0) "F c"
a: (0, 1.8) "a"
b: (1.6, 1.8) "b"
c: (3.2, 1.8) "c"
f: a -> b "f"
g: b -> c "g"
h: a -> c "g \circ f" bend=-40 side=right
Ff: Fa -> Fb "F f"
Fg: Fb -> Fc "F g"
Fh: Fa -> Fc "F(g \circ f)" bend=40
ma: a -> Fa "" dashed color=gray
mb: b -> Fb "" dashed color=gray
mc: c -> Fc "" dashed color=gray
path "F g ∘ F f": Ff Fg
path "F (g ∘ f)": Fh color=green
caption: 函子保持复合：在 D 中，F g ∘ F f 与 F(g ∘ f) 是同一个箭头。灰色虚线表示 F 在对象上的作用。
```

最后，我们要求 $\mathcal{C}$ 中所有的恒等态射都被映成 $\mathcal{D}$ 中的恒等态射：

$$F\, \mathrm{id}_a = \mathrm{id}_{F a}$$

这里 $\mathrm{id}_a$ 是对象 $a$ 上的恒等态射，$\mathrm{id}_{F a}$ 是 $F a$ 上的恒等态射。

![函子保持恒等态射](/img/1.7/functorid.jpg "函子保持恒等：a 上的恒等箭头被映成 F a 上的恒等箭头。")

注意，这些条件使得函子比普通函数要受限得多。函子必须保持范畴的结构。
如果你把范畴想象成一组被态射之网连在一起的对象，那么函子不允许在这张网上撕开任何口子。
它可以把对象压在一起，可以把多个态射粘成一个，但它绝不能把东西拆开。
这种“不许撕裂”的约束，类似于你可能在微积分里见过的连续性条件。在这个意义上，函子是“连续的”
（尽管函子还有一个更严格的连续性概念）。

与函数一样，函子既可以“坍缩”，也可以“嵌入”。当源范畴比目标范畴小得多的时候，嵌入的一面更为突出。
在极端情况下，源范畴可以是平凡的单例范畴——只有一个对象和一个态射（恒等态射）的范畴。
从单例范畴到任何其他范畴的函子，就只是在那个范畴里**选出一个对象**。这与“从单元素集合出发的态射在目标集合里选出一个元素”完全类似。

坍缩得最彻底的函子叫作**常函子** $\Delta_c$。它把源范畴里的每一个对象都映到目标范畴里选定的同一个对象 $c$，
并把源范畴里的每一个态射都映成恒等态射 $\mathrm{id}_c$。它就像一个黑洞，把一切都压缩进一个奇点。
等讨论极限与余极限的时候，我们会更多地见到这个函子。

下面这个小实验能让你亲手摸一摸“函子是范畴之间的映射”这句话。
左边是一个小范畴 $\mathcal{C}$（三个对象、两个箭头和它们的复合，再加上恒等箭头），右边是目标范畴 $\mathcal{D}$。
点击任何一个对象或箭头，看它被映到哪里（或者在右边点一下，看它的原像是谁）；
然后用“检验复合”“检验恒等”两个按钮，看看函子定律是不是成立。
特别留意“坍缩”和“常函子”：多个东西被压到一起是允许的。再看看最后一个“撕裂”的映射，它为什么**不是**函子。

<div><Ch1_7FunctorMap /></div>

::: info 数学小课堂：映射要“保持结构”
数学里处处是“保持结构的映射”，函子只是其中最一般的一种。几个你可能见过的例子：

- 函数 $f(x) = 2^x$ 把加法变成乘法：$2^{x+y} = 2^x \cdot 2^y$，并把 $0$ 映成 $1$。它“保持”了幺半群 $(\mathbb{R}, +, 0)$ 到 $(\mathbb{R}_{>0}, \cdot, 1)$ 的结构。
- 字符串长度 `len` 把拼接变成加法：`len (s ++ t) = len s + len t`，并把空串映成 0。

函子是同一个思想在范畴上的版本：**复合**变成复合，**恒等**变成恒等。
如果你还记得一个幺半群就是只有一个对象的范畴（第 1.3 章），那么上面两个例子其实就是函子！
（单个对象被映到单个对象；每个元素是一个箭头；“保持复合”就是 $f(x + y) = f(x) \cdot f(y)$。）
:::

## 补充：用 Lean 写下函子的定义

这是本书第一次正式遇到函子，所以我们把全书公共前导 `Prelude.lean` 里的函子定义拿出来，逐行看一遍。
它建立在第 1.3 章引入的 `CTFP.Category` 之上（记号 `a ⟶ b` 是从 `a` 到 `b` 的态射类型，`g ⊚ f` 是“`g` 在 `f` 之后”，`𝟙 a` 是恒等态射）。
那部分定义我们在本章开头悄悄引入了（读者看不到，但“在线运行”时会带上）。

```lean hidden
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

namespace CTFP

/-- 范畴：对象 + 态射 + 复合 + 恒等，满足单位律与结合律。 -/
class Category (Obj : Type u) where
  /-- 从 `a` 到 `b` 的态射所组成的类型（hom-set）。 -/
  Hom : Obj → Obj → Type v
  /-- 每个对象上的恒等态射。 -/
  id : (a : Obj) → Hom a a
  /-- 复合：`comp g f` 表示先 `f` 后 `g`。 -/
  comp : {a b c : Obj} → Hom b c → Hom a b → Hom a c
  id_comp : ∀ {a b : Obj} (f : Hom a b), comp (id b) f = f := by intros; rfl
  comp_id : ∀ {a b : Obj} (f : Hom a b), comp f (id a) = f := by intros; rfl
  assoc : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp h (comp g f) = comp (comp h g) f := by intros; rfl

infixr:10 " ⟶ " => Category.Hom
infixr:80 " ⊚ " => Category.comp
notation "𝟙" => Category.id

open Category

/-- 类型与函数构成的范畴 **Type**（原书中的 **Set**/**Hask**）。三条定律都是 `rfl`。 -/
instance typeCategory : Category (Type u) where
  Hom a b := a → b
  id _ := fun x => x
  comp g f := fun x => g (f x)

end CTFP
```

```lean
namespace CTFP

/-- 范畴之间的函子：把对象映到对象、态射映到态射，并保持恒等与复合。 -/
structure CFunctor (C : Type u₁) [Category.{u₁, v₁} C] (D : Type u₂) [Category.{u₂, v₂} D] where
  obj : C → D
  map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id : ∀ (a : C), map (𝟙 a) = 𝟙 (obj a)
  map_comp : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c), map (g ⊚ f) = map g ⊚ map f

end CTFP

open CTFP
```

逐行来看：

- `structure CFunctor (C : Type u₁) [Category.{u₁, v₁} C] (D : Type u₂) [Category.{u₂, v₂} D]`：
  函子是一个结构体，它有两个参数 `C` 和 `D`——源范畴和目标范畴的**对象类型**。
  方括号 `[Category C]` 是**实例参数**：它要求 `C` 上已经有一个范畴结构（态射、复合、恒等），并让 Lean 自动去找。
  这和 Rust 的 `struct CFunctor<C: Category, D: Category>` 是一个意思。
  名字里的 `C` 前缀是为了和 Lean 自带的、只作用于类型的 `Functor` 类区分开（下文马上会讲后者）。
- `obj : C → D`：**对象上的映射**。原书写作 $F a$，在 Lean 里是 `F.obj a`。
- `map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)`：**态射上的映射**。注意它的类型——这正是“保持连接”：
  一个从 `a` 到 `b` 的态射，必须被映成从 `obj a` 到 `obj b` 的态射。你**写不出**一个把 `f : a ⟶ b` 映到别处的 `map`，
  因为类型检查过不了。`{a b : C}` 是隐式参数，调用 `F.map f` 时 Lean 会从 `f` 的类型里读出 `a` 和 `b`。
- `map_id : ∀ (a : C), map (𝟙 a) = 𝟙 (obj a)`：**保持恒等**，即 $F\,\mathrm{id}_a = \mathrm{id}_{F a}$。
- `map_comp : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c), map (g ⊚ f) = map g ⊚ map f`：**保持复合**，即 $F(g \circ f) = F g \circ F f$。

最后两个字段是**证明**。和第 1.6 章的 `TypeIso` 一样：要造出一个 `CFunctor` 的值，你必须同时交出这两条定律的证明。
原书只能说“函子必须保持复合”，Lean 则让“不保持复合的东西”根本无法被称为函子。

::: tip Lean 深入：宇宙（universe）与 `Category.{u₁, v₁}`
`Type u₁`、`Category.{u₁, v₁}` 里的 `u₁`、`v₁` 是**宇宙层级**（universe level）。为什么要有它们？

在 Lean 里，`Nat : Type`，而 `Type` 本身也是个东西，它的类型是 `Type 1`；`Type 1 : Type 2`，依此类推。
`Type` 就是 `Type 0`。之所以不能有 `Type : Type`，原因和“所有集合的集合”导致悖论一样（我们在本章末尾讲 $\mathbf{Cat}$ 时还会碰到它）。

范畴的对象可能住在某一层宇宙（`u₁`），态射可能住在另一层（`v₁`）。比如范畴 **Type** 的对象是类型，
它们组成的 `Type` 本身住在 `Type 1` 里。为了让同一个定义对所有这些情况都适用，`CFunctor` 对宇宙层级做了泛化。
`Category.{u₁, v₁} C` 中的花括号是在**显式指定**宇宙参数：对象在 `u₁` 层，态射在 `v₁` 层。

本书的大部分代码只用 `Type`（即 `Type 0`），你可以暂时把这些 `u`、`v` 当作“编译器需要的簿记”，读的时候跳过。
:::

有了定义，就可以构造函子了。最简单的是**恒等函子**：什么都不动。两条定律都是 `rfl`——按定义两边就相同：

```lean
def CFunctor.id (C : Type u₁) [Category.{u₁, v₁} C] : CFunctor C C where
  obj a := a
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl
```

**常函子** $\Delta_c$ 把一切都压到对象 `c` 上，把每个箭头都变成 `𝟙 c`。
保持恒等是平凡的；保持复合要求 `𝟙 c = 𝟙 c ⊚ 𝟙 c`，这正是范畴的左单位律 `id_comp`（倒过来用，所以加了 `.symm`）：

```lean
def constFunctor (C : Type u₁) [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    (c : D) : CFunctor C D where
  obj _ := c
  map _ := 𝟙 c
  map_id _ := rfl
  map_comp _ _ := (Category.id_comp _).symm
```

再来看**单例范畴**：只有一个对象（我们用 `Unit` 的唯一值 `()` 充当），只有一个箭头（同样用 `()` 充当）。
三条范畴定律全都由默认的 `rfl` 自动完成：

```lean
instance unitCat : Category Unit where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
```

从单例范畴出发的函子，就是在目标范畴里“选一个对象”：

```lean
def selectObj {D : Type u₂} [Category.{u₂, v₂} D] (d : D) : CFunctor Unit D where
  obj _ := d
  map _ := 𝟙 d
  map_id _ := rfl
  map_comp _ _ := (Category.id_comp _).symm

-- 在范畴 Type 中选出对象 Nat
example : (selectObj (Nat : Type)).obj () = Nat := rfl
```

## 编程中的函子

让我们回到地面上，谈谈编程。我们有类型与函数的范畴。我们可以谈论把这个范畴映到它自身的函子——这样的函子叫作**自函子**（endofunctor）。
那么，类型范畴里的自函子是什么呢？首先，它把类型映到类型。我们其实已经见过这样的映射，只是可能没意识到它们就是这个。
我说的是那些由其他类型参数化的类型定义。来看几个例子。

### Maybe 函子

`Maybe` 的定义是一个从类型 `α` 到类型 `Maybe α` 的映射。Lean 里它就是 `Option`，
不过为了从零讲起、并且和原书的名字保持一致，我们自己定义一个：

```lean
inductive Maybe (α : Type) where
  | nothing : Maybe α
  | just    : α → Maybe α
deriving Repr, BEq

open Maybe
```

这里有一个重要的细节：`Maybe` 本身不是类型，而是一个**类型构造子**（type constructor）。
你必须给它一个类型参数，比如 `Int` 或 `Bool`，才能把它变成一个类型。不带任何参数的 `Maybe` 表示的是一个类型上的函数。
在 Lean 里，这一点写得明明白白：

```lean
#check (Maybe : Type → Type)
```

但是，能把 `Maybe` 变成一个函子吗？（从现在起，当我在编程的语境中谈论函子时，几乎总是指自函子。）
函子不仅是对象（这里是类型）的映射，还是态射（这里是函数）的映射。对于任何从 `α` 到 `β` 的函数

```lean no-check
f : α → β
```

我们想造出一个从 `Maybe α` 到 `Maybe β` 的函数。要定义这样的函数，需要考虑两种情况，分别对应 `Maybe` 的两个构造子。
`nothing` 的情况很简单：原样返回 `nothing`。如果参数是 `just`，就把函数 `f` 作用到它的内容上。所以 `f` 在 `Maybe` 下的像就是这个函数：

```lean
section
variable {α β : Type} (f : α → β)

def f' : Maybe α → Maybe β
  | nothing => nothing
  | just x  => just (f x)

end
```

（顺带一提，Lean 和 Haskell 一样允许在变量名里使用撇号，在这种场合非常方便。
`variable` 声明了在这个 `section` 里自动加到每个定义前面的参数，所以 `f'` 的完整类型其实是 `(α → β) → Maybe α → Maybe β`。）

在 Haskell 里，函子的态射映射部分被实现为一个叫作 `fmap` 的高阶函数。对 `Maybe` 来说，它的签名是：

```lean no-check
fmap : (α → β) → (Maybe α → Maybe β)
```

![fmap f 把 f : a → b 提升为 Maybe a → Maybe b](/img/1.7/functormaybe.jpg "fmap 把下面的 f : a → b “提升”成上面的 fmap f : Maybe a → Maybe b。")

我们常说 `fmap` **提升**（lift）了一个函数。被提升的函数作用在 `Maybe` 值上。和往常一样，由于柯里化，这个签名有两种理解方式：
一个单参数函数——参数本身是一个函数 `(α → β)`——返回一个函数 `(Maybe α → Maybe β)`；
或者一个返回 `Maybe β` 的双参数函数：

```lean no-check
fmap : (α → β) → Maybe α → Maybe β
```

（在 Lean 里，`→` 是右结合的，所以这两个签名**是同一个类型**——括号加不加都一样。）

根据前面的讨论，`Maybe` 的 `fmap` 实现如下：

```lean
def fmap {α β : Type} : (α → β) → Maybe α → Maybe β
  | _, nothing => nothing
  | f, just x  => just (f x)
```

要证明类型构造子 `Maybe` 与函数 `fmap` 一起构成一个函子，就得证明 `fmap` 保持恒等和复合。
这些被称为“函子定律”，但它们说的不过是：范畴的结构被保持了。

### 等式推理

为了证明函子定律，我将使用**等式推理**（equational reasoning），这是 Haskell 中一种常见的证明技巧。
它利用了这样一个事实：Haskell 的函数是用等式定义的——左边等于右边。你总是可以用一边替换另一边（必要时重命名变量以避免冲突）。
你可以把它想成内联一个函数，或者反过来，把一个表达式重构成一个函数。以恒等函数为例：

```lean no-check
def id (x : α) : α := x
```

举个例子，如果你在某个表达式里看到 `id y`，就可以把它换成 `y`（内联）。
更一般地，如果你看到 `id` 作用在某个表达式上，比如 `id (y + 2)`，就可以把它替换成表达式本身 `(y + 2)`。
而且这种替换是双向的：你可以把任何表达式 `e` 替换成 `id e`（重构）。
如果函数是用模式匹配定义的，你可以独立地使用其中每一条子定义。例如，根据上面 `fmap` 的定义，
你可以把 `fmap f nothing` 替换成 `nothing`，反之亦然。来看看实践中是怎么做的。先从保持恒等开始：

```lean no-check
fmap id = id
```

有两种情况需要考虑：`nothing` 和 `just`。原书在这里用 Haskell 伪代码一步步把左边变成右边；
而在 Lean 里，这样的推导可以**原封不动地**写成 `calc` 证明，并由编译器逐步检查。下面是第一种情况：

```lean
theorem fmap_id_nothing {α : Type} : fmap id (nothing : Maybe α) = id nothing :=
  calc fmap id nothing
      = nothing    := by rfl   -- fmap 的定义
    _ = id nothing := by rfl   -- id 的定义（反着用）
```

::: tip Lean 深入：`calc` 就是写在纸上的等式链
`calc a = b := 证明₁` 后面每一行 `_ = c := 证明₂` 的意思是“上一行的右边等于 `c`，理由是证明₂”。
Lean 把这些等式用传递性串起来，得到 `a = c`。每一步的理由都会被单独检查——你不能偷偷跳步。
这里每一步的理由都是 `rfl`（“按定义两边相同”），因为每一步都只是展开或折回某个定义。
这和原书 `= { definition of fmap }` 的写法一一对应，只不过原书的注释是写给人看的，而 Lean 的 `rfl` 是写给机器检查的。
:::

注意在最后一步里，我把 `id` 的定义**倒过来**用了：把表达式 `nothing` 替换成 `id nothing`。
实践中，这类证明往往是“蜡烛两头烧”：从两边同时往中间推，直到碰到同一个表达式为止——这里是 `nothing`。第二种情况也很简单：

```lean
theorem fmap_id_just {α : Type} (x : α) : fmap id (just x) = id (just x) :=
  calc fmap id (just x)
      = just (id x)  := by rfl   -- fmap 的定义
    _ = just x       := by rfl   -- id 的定义
    _ = id (just x)  := by rfl   -- id 的定义（反着用）
```

把两种情况合起来，就得到完整的恒等律：

```lean
theorem fmap_id {α : Type} : ∀ m : Maybe α, fmap id m = id m
  | nothing => fmap_id_nothing
  | just x  => fmap_id_just x
```

（用模式匹配来证明“对所有 `m`”，就是在分情况讨论：`m` 要么是 `nothing`，要么是 `just x`。这和用模式匹配定义函数一模一样——
在 Lean 里，证明就是程序。）

接下来证明 `fmap` 保持复合：

```lean no-check
fmap (g ∘ f) = fmap g ∘ fmap f
```

先是 `nothing` 的情况，然后是 `just` 的情况：

```lean
theorem fmap_comp {α β γ : Type} (f : α → β) (g : β → γ) :
    ∀ m : Maybe α, fmap (g ∘ f) m = (fmap g ∘ fmap f) m
  | nothing =>
    calc fmap (g ∘ f) nothing
        = nothing                     := by rfl   -- fmap 的定义
      _ = fmap g nothing              := by rfl   -- fmap 的定义（反着用）
      _ = fmap g (fmap f nothing)     := by rfl   -- fmap 的定义（反着用）
  | just x =>
    calc fmap (g ∘ f) (just x)
        = just ((g ∘ f) x)            := by rfl   -- fmap 的定义
      _ = just (g (f x))              := by rfl   -- 复合的定义
      _ = fmap g (just (f x))         := by rfl   -- fmap 的定义（反着用）
      _ = fmap g (fmap f (just x))    := by rfl   -- fmap 的定义（反着用）
      _ = (fmap g ∘ fmap f) (just x)  := by rfl   -- 复合的定义（反着用）
```

::: details 偷懒的写法：让 `cases` 和 `rfl` 一口气做完
上面的 `calc` 是为了让你看清每一步。其实每一步都只是“按定义计算”，Lean 可以一口气算完：

```lean
example {α : Type} (m : Maybe α) : fmap id m = m := by
  cases m <;> rfl

example {α β γ : Type} (f : α → β) (g : β → γ) (m : Maybe α) :
    fmap (g ∘ f) m = fmap g (fmap f m) := by
  cases m <;> rfl
```

`cases m` 把目标拆成 `m = nothing` 和 `m = just x` 两种情况；`<;>` 表示“对每个新目标都执行后面的 tactic”。
:::

值得强调的是，等式推理对 C++ 风格的、带副作用的“函数”是行不通的。原书举了一个 C++ 的例子，我们用 Rust 重写一遍：

```rust
use std::cell::Cell;

thread_local! {
    static C: Cell<i32> = Cell::new(0);
}

fn counter() -> i32 {
    C.with(|c| {
        let v = c.get();
        c.set(v + 1);
        v
    })
}

fn square(x: i32) -> i32 {
    x * x
}

pub fn demo() -> i32 {
    square(counter()) // counter() 只被调用一次
}
```

用等式推理，你可以把 `square` 内联，得到：

```rust no-check
counter() * counter()
```

这显然不是一个合法的变换，它不会得到同样的结果：`counter()` 被调用了两次，返回的是两个不同的数。
尽管如此，如果你把 `square` 实现成一个**宏**，编译器就真的会这样“等式推理”，后果不堪设想：

```rust
macro_rules! square {
    ($x:expr) => {
        $x * $x
    };
}

fn counter() -> i32 {
    0
}

pub fn oops() -> i32 {
    square!(counter()) // 展开成 counter() * counter()：调用了两次！
}
```

（Rust 的 `macro_rules!` 是卫生宏，比 C 的预处理宏安全得多，但“表达式被原样复制”这件事是一样的。）

::: tip Lean 深入：为什么在 Lean 里等式推理永远成立
Lean 的普通函数**没有副作用**：`def counter : Int := ...` 每次求值都得到同一个值，像 `counter` 那样的东西根本写不出来。
需要副作用时，函数的类型会诚实地写成 `IO Int`，而 `IO Int` 不是 `Int`——你不能把它直接塞给 `square`。
所以在 Lean 里，“用定义替换”永远是合法的。这也是 `rfl`、`simp`、`calc` 能放心地展开定义的根本原因。
:::

### Rust 的 `Option`

函子在 Haskell 里很容易表达，但只要一门语言支持泛型编程和高阶函数，就可以在其中定义函子。
原书接下来讨论了 C++ 中与 `Maybe` 对应的模板类型 `optional`：用一个布尔标签 `_isValid` 记录有没有值，再存一个值 `_v`。
在 Rust 里，对应物就是标准库的 `Option<T>`——而且它是个货真价实的和类型。为了从零写起，我们先定义一个自己的：

```rust
pub enum Optional<T> {
    Nothing,
    Just(T),
}
```

这个类型提供了函子定义的一部分：类型的映射。它把任意类型 `T` 映成一个新类型 `Optional<T>`。
我们来定义它在函数上的作用。原书的 C++ 版本是一个高阶函数，接受一个函数作为参数，并返回一个函数。Rust 里可以写成：

```rust
pub enum Optional<T> {
    Nothing,
    Just(T),
}

pub fn fmap<A, B>(f: impl Fn(A) -> B) -> impl Fn(Optional<A>) -> Optional<B> {
    move |opt| match opt {
        Optional::Nothing => Optional::Nothing,
        Optional::Just(x) => Optional::Just(f(x)),
    }
}
```

这是它的非柯里化版本：

```rust
pub enum Optional<T> {
    Nothing,
    Just(T),
}

pub fn fmap<A, B>(f: impl Fn(A) -> B, opt: Optional<A>) -> Optional<B> {
    match opt {
        Optional::Nothing => Optional::Nothing,
        Optional::Just(x) => Optional::Just(f(x)),
    }
}
```

还可以把 `fmap` 做成 `Optional` 的一个方法——Rust 标准库正是这么做的：`Option::map`。

```rust
pub fn demo() -> Option<usize> {
    Some("energy").map(|s| s.len()) // Some(6)
}
```

选择太多，反而让“抽象出函子这一模式”在 C++ 里成了难题。函子应该是一个可以继承的接口吗（可惜 C++ 不能有模板虚函数）？
应该是柯里化的还是非柯里化的自由模板函数？编译器能正确推断出缺失的类型吗，还是必须显式写出来？
设想输入函数 `f` 把 `int` 变成 `bool`，编译器要怎样推断出 `auto g = fmap(f);` 中 `g` 的类型，
尤其是将来如果有多个函子都重载了 `fmap`？（我们很快会看到更多函子。）

Rust 面临着同样的选择题，而且多了一道坎：**Rust 没有函数重载**。你没法同时为 `Optional` 和 `Vec` 定义两个都叫 `fmap` 的自由函数。
于是标准库干脆给每个类型各起一套方法：`Option::map`、`Result::map`、`Iterator::map`……每一个都“是函子”，
但语言里没有一个统一的名字能把它们串起来。我们稍后会看到这背后的原因。

### 类型类

那么 Haskell 是怎么把函子抽象出来的呢？它用的是**类型类**（type class）机制。Lean 也一样。
类型类定义了一族支持某个公共接口的类型。例如，支持相等比较的对象所组成的类，可以这样定义
（Lean 核心库里的对应物叫 `BEq`，运算符是 `==`；为了避免冲突，这里我们自己定义一个 `MyEq`）：

```lean
class MyEq (α : Type) where
  eq : α → α → Bool

infix:50 " === " => MyEq.eq
```

这个定义说的是：如果类型 `α` 支持一个运算 `eq`，它接受两个 `α` 类型的参数并返回 `Bool`，那么 `α` 就属于类 `MyEq`。
如果你想告诉 Lean 某个特定的类型属于 `MyEq`，就必须把它声明为这个类的一个**实例**（instance），并提供 `eq` 的实现。
例如，给定一个二维点 `Point` 的定义（两个 `Float` 的积类型）：

```lean
inductive Point where
  | pt : Float → Float → Point
```

就可以定义点的相等：

```lean
instance : MyEq Point where
  eq
    | .pt x y, .pt x' y' => x == x' && y == y'

#guard Point.pt 1 2 === Point.pt 1 2
#guard !(Point.pt 1 2 === Point.pt 1 3)
```

这里我对两个参数同时做了模式匹配：`.pt x y` 和 `.pt x' y'`。函数体跟在 `=>` 后面。
一旦 `Point` 被声明为 `MyEq` 的实例，就可以直接用 `===` 比较两个点了。
注意，与 C++ 或 Java 不同，定义 `Point` 的时候你不需要指明 `MyEq` 类（或接口）——可以以后在客户代码里再声明。

::: tip Rust 视角：类型类 ≈ trait
Lean 的 `class` / `instance` 几乎就是 Rust 的 `trait` / `impl`：`class MyEq (α : Type)` 对应 `trait MyEq`，
`instance : MyEq Point` 对应 `impl MyEq for Point`。“定义类型时不必声明它实现了哪些接口”这一点也和 Rust 一样。
不同之处在于，Rust 有**孤儿规则**（orphan rule）：只有当 trait 或类型至少有一个是你自己 crate 里的，你才能写 `impl`。
Lean 没有这个限制——你可以给别人的类型实现别人的类型类（代价是需要自己留意实例冲突）。
:::

类型类也是 Haskell 重载函数（和运算符）的唯一机制。我们需要它来为不同的函子重载 `fmap`。
不过有一个麻烦：函子不是被定义为一个类型，而是被定义为类型的映射，一个类型构造子。
我们需要的类型类，不再像 `MyEq` 那样是一族类型，而是一族**类型构造子**。
幸运的是，Haskell 和 Lean 的类型类对类型构造子和对类型一样适用。下面就是 `Functor` 类的定义
（放进命名空间 `MyDefs`，以免和 Lean 自带的 `Functor` 冲突）：

```lean
namespace MyDefs

class Functor (f : Type → Type) where
  fmap : {α β : Type} → (α → β) → f α → f β

end MyDefs
```

它规定：如果存在一个具有上述类型签名的函数 `fmap`，那么 `f` 就是一个 `Functor`。
这里的 `f` 是一个类型变量，和类型变量 `α`、`β` 类似。在 Haskell 里，编译器会根据它的用法——作用在其他类型上，比如 `f a` 和 `f b`——
推断出它代表的是类型构造子而不是类型。Lean 则要求我们直接写出来：`(f : Type → Type)`，一目了然。
相应地，声明 `Functor` 的实例时，必须给它一个类型构造子，比如 `Maybe`：

```lean
instance : MyDefs.Functor Maybe where
  fmap
    | _, nothing => nothing
    | f, just x  => just (f x)
```

顺便说一句，Haskell 的 `Functor` 类及其对包括 `Maybe` 在内的许多简单数据类型的实例，都是标准 Prelude 库的一部分。
Lean 也一样：核心库里就有 `Functor` 类，以及 `Option`、`List`、`Except`、`IO` 等的实例。

## 补充：Lean 自带的 `Functor` 与 `LawfulFunctor`

Lean 核心库的 `Functor` 类长这样（只展示）：

```lean no-check
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)
```

- 方法叫 `map` 而不是 `fmap`，并配有中缀记号 `<$>`：`f <$> x` 就是 `Functor.map f x`。
- `mapConst` 是一个带默认实现的辅助方法（“把容器里的每个值都换成同一个常量”），一般不用管它。

我们来为自己的 `Maybe` 声明一个 Lean 标准的 `Functor` 实例：

```lean
instance : Functor Maybe where
  map f
    | nothing => nothing
    | just x  => just (f x)

#guard ((· + 1) <$> just 41) == just 42
#guard ((· + 1) <$> (nothing : Maybe Nat)) == nothing
```

（`(· + 1)` 是 `fun x => x + 1` 的简写，`·` 用 `\.` 输入。）

到这里为止，Lean 和 Haskell 一样：`Functor` 类只要求你给出 `map`，**并不检查**它是否满足函子定律。
在 Haskell 里，函子定律只能写在文档注释里，靠程序员自觉遵守。Lean 则更进一步：核心库里还有一个类型类 `LawfulFunctor`，
它的字段就是函子定律本身（只展示）：

```lean no-check
class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  map_const : (Functor.mapConst : α → f β → f α) = Functor.map ∘ Function.const β
  id_map    : ∀ (x : f α), id <$> x = x                                   -- 保持恒等
  comp_map  : ∀ (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x  -- 保持复合
```

注意 `: Prop`——`LawfulFunctor` 的实例不是数据，而是**证明**。要声明 `Maybe` 是一个“守法的”函子，就得把证明交出来：

```lean
instance : LawfulFunctor Maybe where
  map_const := rfl                              -- 我们用的是默认的 mapConst，按定义成立
  id_map x := by cases x <;> rfl                -- 保持恒等：分两种情况，按定义计算
  comp_map f g x := by cases x <;> rfl          -- 保持复合：同上
```

从此以后，任何对“所有守法函子”成立的定理（比如核心库里的 `Functor.map_map`）都可以直接用在 `Maybe` 上。
这正是本书反复强调的：**定律不再是口头约定，而是类型检查的一部分**。

::: warning 易错点：`Functor` 与 `CFunctor` 是两个层次的东西
- `CTFP.CFunctor C D` 是**数学意义上**的函子：任意两个范畴之间，包含对象映射、态射映射和两条定律。
- Lean 的 `Functor f`（加上 `LawfulFunctor f`）是**编程意义上**的函子：只针对类型范畴到自身的自函子。
  `f : Type → Type` 是对象映射，`map` 是态射映射，`LawfulFunctor` 的字段是定律。

后者是前者的特例。任何守法的 `Functor` 都能打包成一个 `CFunctor (Type) (Type)`，见下面的折叠框。
:::

::: details 把 Lean 的守法函子打包成范畴论意义上的 `CFunctor`
```lean
def toCFunctor (F : Type → Type) [Functor F] [LawfulFunctor F] : CFunctor Type Type where
  obj := F
  map {α β} (f : α → β) := (Functor.map f : F α → F β)
  map_id α := by
    funext (x : F α)
    exact id_map x
  map_comp {α β γ} f g := by
    funext (x : F α)
    exact comp_map f g x

-- Maybe 就是范畴 Type 上的一个自函子
def maybeCFunctor : CFunctor Type Type := toCFunctor Maybe
```

`funext` 是**函数外延性**：要证明两个函数相等，只需证明它们对每个输入 `x` 给出相同的输出。
`(x : F α)` 这个类型标注是为了让 Lean 把 `x` 看成 `F α` 而不是 `CFunctor` 内部某个展开后的类型（见 STYLE 中提到的坑）。
:::

### Rust 中的函子

能在 C++ 里用同样的办法吗？类型构造子对应于模板类，比如 `optional`，所以照此类推，我们会用一个**模板模板参数**（template template parameter）`F`
来参数化 `fmap`。原书接着指出，C++ 禁止对函数模板做偏特化，所以最后只能退回到函数重载——
那个通用的、以 `F` 为参数的 `fmap` 定义完全被架空了。

Rust 的处境类似，而且更直接：Rust 根本没有**高阶类型**（higher-kinded types，HKT）。
在 Rust 里，`Option` 不能单独出现——它必须是 `Option<T>`。你写不出“一个以 `Option` 本身为参数的 trait”：

```rust no-check
// 不是合法的 Rust：类型参数 F 不能本身再带参数
trait Functor<F<_>> {
    fn fmap<A, B>(f: impl Fn(A) -> B, fa: F<A>) -> F<B>;
}
```

Rust 社区的常见变通办法是借助**泛型关联类型**（GAT），让 trait 挂在 `Option<A>` 这样的**具体类型**上，
再用关联类型 `Mapped<B>` 来表示“把元素换成 `B` 之后的类型”：

```rust
pub trait Functor {
    type Elem;
    type Mapped<B>: Functor<Elem = B>;
    fn fmap<B>(self, f: impl FnMut(Self::Elem) -> B) -> Self::Mapped<B>;
}

impl<A> Functor for Option<A> {
    type Elem = A;
    type Mapped<B> = Option<B>;
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Option<B> {
        self.map(f)
    }
}

impl<A> Functor for Vec<A> {
    type Elem = A;
    type Mapped<B> = Vec<B>;
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Vec<B> {
        self.into_iter().map(f).collect()
    }
}

// 但没有任何东西阻止你写出这种“函子”：Weird<A> 映射之后变成了 Vec<B>！
pub struct Weird<A>(Option<A>);

impl<A> Functor for Weird<A> {
    type Elem = A;
    type Mapped<B> = Vec<B>;
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Vec<B> {
        self.0.into_iter().map(f).collect()
    }
}
```

这能用，但只是一个近似：类型系统无法保证 `Mapped<B>` 和 `Self` 是“同一个类型构造子作用在不同参数上”，最后那个 `Weird` 就是反例。
至于函子定律，Rust 更是无从表达。

::: tip 这是 Lean 胜出的地方
对比一下 Lean：`class Functor (f : Type u → Type v)` 的参数 `f` **就是**类型构造子本身——Lean 有完整的高阶类型（实际上，类型就是普通的值，
`Type → Type` 就是普通的函数类型）。所以 `map : (α → β) → f α → f β` 的结果类型被**强制**是同一个 `f`，`Weird` 那样的东西写不出来。
再加上 `LawfulFunctor`，连定律都被类型检查了。Haskell 做到了前一半，Lean 两半都做到了。
:::

### List 函子

为了获得一些关于函子在编程中扮演什么角色的直觉，我们需要看更多的例子。任何由另一个类型参数化的类型，都是函子的候选者。
泛型容器由它所存储的元素类型参数化，所以我们来看一个非常简单的容器——列表：

```lean
inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α
```

我们有类型构造子 `MyList`，它是一个从任意类型 `α` 到类型 `MyList α` 的映射。
要证明 `MyList` 是一个函子，就必须定义函数的提升：给定一个函数 `α → β`，定义一个函数 `MyList α → MyList β`：

```lean no-check
fmap : (α → β) → (MyList α → MyList β)
```

作用在 `MyList α` 上的函数必须考虑两种情况，对应于列表的两个构造子。`nil` 的情况是平凡的——直接返回 `nil`——对一个空列表你也做不了什么。
`cons` 的情况有点微妙，因为它涉及递归。所以我们退后一步，想想我们到底要做什么。
我们有一个 `α` 的列表，一个把 `α` 变成 `β` 的函数 `f`，我们想生成一个 `β` 的列表。
显然的做法是用 `f` 把列表的每个元素从 `α` 变成 `β`。可是一个（非空）列表被定义为头和尾的 `cons`，具体怎么做呢？
我们把 `f` 作用到头上，把提升后的（被 `fmap` 过的）`f` 作用到尾上。这是一个递归定义，因为我们在用“提升后的 `f`”来定义“提升后的 `f`”：

```lean no-check
fmap f (cons x t) = cons (f x) (fmap f t)
```

注意，在右边，`fmap f` 作用在一个比我们正在定义的列表更短的列表上——它作用在尾巴上。
我们不断递归到越来越短的列表，所以必然最终会到达空列表 `nil`。而正如前面决定的，`fmap f` 作用在 `nil` 上返回 `nil`，递归就此终止。
为了得到最终结果，我们用构造子 `cons` 把新的头 `(f x)` 和新的尾 `(fmap f t)` 组合起来。
把这一切放在一起，就是列表函子的实例声明：

```lean
def MyList.map {α β : Type} (f : α → β) : MyList α → MyList β
  | nil      => nil
  | cons x t => cons (f x) (MyList.map f t)

instance : Functor MyList where
  map := MyList.map
```

::: tip Lean 深入：结构递归与终止性检查
原书用文字论证了“递归一定会终止，因为尾巴更短”。Lean 会**自动检查**这件事：`MyList.map f t` 中的 `t` 是 `cons x t` 的直接子项，
这叫**结构递归**（structural recursion），Lean 认得出它一定终止。如果你不小心写成 `MyList.map f (cons x t)`，Lean 会拒绝编译，
报告它无法证明终止。这不是吹毛求疵：在 Lean 里，一个不终止的“函数”可以被用来“证明”任何命题，所以 Lean 必须确保所有普通函数都是**全函数**。
（真需要不终止的程序时，可以用 `partial def`，但它就不能出现在证明里了。）
:::

`MyList` 满足函子定律的证明，留作本章挑战 4（要用到归纳法）。Lean 自带的 `List` 当然早已是 `Functor` 和 `LawfulFunctor` 的实例了：

```lean
#guard (· ^ 2) <$> [1, 2, 3, 4] == [1, 4, 9, 16]
```

如果你更习惯 C++，可以考虑 `std::vector`，它大概可以算是最通用的 C++ 容器。原书给出的 `fmap` 实现不过是 `std::transform` 的一层薄包装。
Rust 里对应的是迭代器：

```rust
pub fn fmap<A, B>(f: impl Fn(A) -> B, v: Vec<A>) -> Vec<B> {
    v.into_iter().map(f).collect()
}

pub fn demo() -> Vec<i32> {
    let v = vec![1, 2, 3, 4];
    let w = fmap(|i| i * i, v);
    println!("{:?}", w); // [1, 4, 9, 16]
    w
}
```

大多数 C++ 容器之所以是函子，是因为它们实现了可以传给 `std::transform` 的迭代器，而 `std::transform` 是 `fmap` 一个更原始的“表亲”。
可惜，函子的简洁性被淹没在迭代器和临时变量的常见杂乱之中。原书在这里高兴地提到，当时新提出的 C++ ranges 库让 range 的函子本性显露得多了。

::: tip Rust 视角：`Iterator::map` 就是函子的 `map`
Rust 的迭代器天生就是“ranges 风格”的：`iter.map(f)` 返回一个新的迭代器，它**惰性地**把 `f` 作用到每个元素上。
你可以验证函子定律在 Rust 里的样子：`it.map(|x| x)` 和 `it` 产生相同的元素（恒等）；
`it.map(f).map(g)` 和 `it.map(|x| g(f(x)))` 产生相同的元素（复合）。
后者恰好是一个重要的优化：两次 `map` 可以融合成一次遍历——在 Rust 里这是迭代器的惰性自动带来的，
在 Lean/Haskell 里，它是函子的复合律保证的“一定可以这样重写”。
:::

### Reader 函子

现在你也许已经形成了一些直觉——比如，函子是某种容器。下面让我给你看一个乍看之下截然不同的例子。
考虑这样一个映射：把类型 `α` 映到“返回 `α` 的函数”的类型。我们还没有深入讨论过函数类型——完整的范畴论处理还在后面——
但作为程序员，我们对它们已经有一定的理解。

在 Haskell 里，函数类型由箭头类型构造子 `(->)` 构造，它接受两个类型：参数类型和结果类型。你已经见过它的中缀形式 `a -> b`，
但加上括号后，它同样可以用前缀形式写作 `(->) a b`。和普通函数一样，多参数的类型函数也可以部分应用。
所以当我们只给箭头提供一个类型参数时，它还在等待另一个。这就是为什么 `(->) a` 是一个类型构造子：
它还需要一个类型 `b` 才能产生完整的类型 `a -> b`。照现在的样子，它定义了一整族由 `a` 参数化的类型构造子。

Lean 里的 `→` 不是一个可以单独拿出来部分应用的运算符（它是依值函数类型 `(x : α) → β x` 的特例，属于语言的内建语法）。
但没关系：Lean 的类型就是值，我们可以直接写出“部分应用”的结果——一个从类型到类型的 lambda：

```lean
#check (fun β => Nat → β : Type → Type)
#check ((Nat → ·) : Type → Type)          -- `·` 写法：同一个东西
```

来看看这是否也是一族函子。同时处理两个类型参数可能有点乱，所以我们重命名一下：把参数类型叫作 `ρ`（希腊字母 rho，r 的意思），
结果类型叫作 `α`，与我们之前的函子定义保持一致。于是我们的类型构造子把任意类型 `α` 映成类型 `ρ → α`。
要证明它是函子，我们要把函数 `α → β` 提升成一个接受 `ρ → α`、返回 `ρ → β` 的函数。
这些正是类型构造子 `(ρ → ·)` 分别作用在 `α` 和 `β` 上所形成的类型。下面是 `fmap` 在这种情况下的类型签名：

```lean no-check
fmap : (α → β) → (ρ → α) → (ρ → β)
```

我们需要解开这样一个谜题：给定一个函数 `f : α → β` 和一个函数 `g : ρ → α`，造出一个函数 `ρ → β`。
复合这两个函数的方式只有一种，而得到的结果恰好就是我们要的。

在 Lean 里，直接给 lambda `fun α => ρ → α` 声明类型类实例是不可靠的（Lean 的实例搜索不擅长匹配 lambda），
而核心库也确实没有为它提供 `Functor` 实例。所以我们先给它起个名字：

```lean
def Reader (ρ : Type) (α : Type) : Type := ρ → α
```

下面就是我们的 `fmap` 实现：

```lean
instance (ρ : Type) : Functor (Reader ρ) where
  map f g := f ∘ g
```

它就是能用！如果你喜欢简洁的记法，这个定义还可以进一步化简：注意到复合可以写成前缀形式，`f ∘ g` 就是 `Function.comp f g`；
再省略参数，就得到两个函数之间的直接等式——`map` 就是 `Function.comp`：

```lean
namespace Version2

instance readerFunctor (ρ : Type) : Functor (Reader ρ) where
  map := Function.comp

end Version2
```

类型构造子 `(ρ → ·)` 与上面这个 `map` 实现的组合，就叫作 **reader 函子**。

::: tip Rust 视角：reader 函子就是闭包的后处理
在 Rust 里，“提升”一个函数到 reader 函子，就是“给一个闭包接上后处理”：

```rust
pub fn fmap<R, A, B>(f: impl Fn(A) -> B, g: impl Fn(R) -> A) -> impl Fn(R) -> B {
    move |r| f(g(r))
}

pub fn demo() -> usize {
    let len_of_greeting = fmap(|s: String| s.len(), |name: &str| format!("Hello, {name}!"));
    len_of_greeting("Lean") // 12
}
```

“reader”这个名字来自它的一种常见用法：`ρ` 是某个“环境”（比如配置），`ρ → α` 是“读取环境、算出一个 `α`”的计算。
后面讲单子时我们会再见到它（Lean 里叫 `ReaderT` / `ReaderM`）。
:::

## 函子作为容器

我们已经看过一些编程语言中函子的例子，它们定义了通用的容器，或者至少是包含若干个其参数类型的值的对象。
Reader 函子似乎是个异类，因为我们不会把函数当作数据。但我们已经见过，纯函数可以被记忆化，函数的执行可以变成查表。表就是数据。
反过来，由于 Haskell 的惰性，一个传统的容器，比如列表，实际上可能是用函数实现的。例如，考虑一个自然数的无限列表，在 Haskell 里可以紧凑地写成 `[1..]`。

显然，这样一个无限列表不可能存在内存里。Haskell 编译器把它实现成一个按需生成整数的函数。
Haskell 实际上模糊了数据与代码之间的界限。列表可以被看作函数，而函数可以被看作把参数映到结果的表。

::: warning 易错点：Lean 是严格求值的，没有“无限列表”
Lean 的 `List` 一定是有限的（回忆第 1.6 章：`inductive` 取的是方程的最小解），而且 Lean 严格求值，所以 `[1..]` 这种东西在 Lean 里不存在。
那 Lean 怎么表示“所有自然数组成的无限序列”呢？最自然的办法恰好就是……一个函数 `Nat → Nat`：第 `n` 个元素是 `n + 1`。
而 `Nat → α` 正是 `Reader Nat α`！原书说“列表可以被看作函数”，在 Lean 里这是**字面上的**做法：

```lean
def nats : Reader Nat Nat := fun n => n + 1     -- 1, 2, 3, ...

-- 对“无限列表”做 map，就是 reader 函子的 map
#guard ((· * 10) <$> nats) 0 == 10
#guard ((· * 10) <$> nats) 4 == 50
```

“容器”和“函数”在这里合二为一。（Lean 中惰性计算的工具是 `Thunk`，必要时也可以用它搭出惰性流，但核心库没有现成的无限列表。）
:::

后一种看法——函数即表——在函数定义域有限且不太大时，甚至可以很实用。然而，把 `strlen` 实现成查表就不现实了，因为不同的字符串有无穷多个。
作为程序员，我们不喜欢无穷；但在范畴论里，你要学会把无穷当早餐吃。不管是所有字符串的集合，还是宇宙过去、现在、将来所有可能状态的集合——我们都能对付！

所以，我喜欢把函子对象（由自函子生成的类型的一个值）看作包含着一个或多个它所参数化的那个类型的值，即使这些值实际上并不在那里。
函子的一个例子是 C++ 的 `std::future`，它可能在某个时刻包含一个值，但并不保证一定会；如果你想访问它，可能得阻塞等待另一个线程执行完毕。
（Lean 里对应的是 `Task`，Rust 里是 `Future`。）另一个例子是 Haskell 的 `IO` 对象，它可能包含用户的输入，
或者包含屏幕上显示着“Hello World!”的未来版本的宇宙。

```lean
-- Task 是一个函子：可以把函数“送进”一个尚未完成的计算里
#guard (Task.map (· + 1) (Task.pure 41)).get == 42

-- IO 也是一个函子：对“将来会读到的值”做变换，并不需要现在就拿到它
def shout (read : IO String) : IO String := (· ++ "!") <$> read
```

按照这种解释，函子对象是某种可能包含一个或多个其参数类型的值的东西。或者它可能包含生成这些值的“配方”。
我们完全不关心能不能访问这些值——那完全是可选的，超出了函子的范围。我们感兴趣的只是能用函数来操纵这些值。
如果这些值能被访问，那我们就应该能看到操纵的结果；如果不能，我们关心的就只是这些操纵能正确地复合，并且用恒等函数操纵不会改变任何东西。

为了向你展示我们有多么不在乎能否访问函子对象内部的值，下面这个类型构造子完全忽略了它的参数 `α`：

```lean
structure Const (γ : Type) (α : Type) where
  val : γ
```

`Const` 类型构造子接受两个类型 `γ` 和 `α`。就像对箭头构造子做的那样，我们将部分应用它来构造一个函子。
数据构造子（Lean 里是 `Const.mk`）只接受一个类型为 `γ` 的值，与 `α` 毫无关系。这个类型构造子的 `fmap` 类型是：

```lean no-check
fmap : (α → β) → Const γ α → Const γ β
```

由于这个函子忽略了它的类型参数，`fmap` 的实现也可以自由地忽略它的函数参数——这个函数根本没东西可作用：

```lean
instance (γ : Type) : Functor (Const γ) where
  map _ c := ⟨c.val⟩
```

原书说，这在 C++ 里可能更清楚一点（“我从没想过自己会说出这句话！”），因为 C++ 在类型参数（编译时）和值（运行时）之间有更强的区分。
Rust 也是如此——而且 Rust 甚至**强制**你承认那个没用到的类型参数：

```rust
use std::marker::PhantomData;

pub struct Const<C, A> {
    v: C,
    _phantom: PhantomData<A>, // Rust 不允许未使用的类型参数，必须用 PhantomData 占位
}

pub fn fmap<C, A, B>(_f: impl Fn(A) -> B, c: Const<C, A>) -> Const<C, B> {
    Const { v: c.v, _phantom: PhantomData }
}
```

`fmap` 同样忽略了函数参数，本质上只是把 `Const` 参数“重新铸造”一下类型，值保持不变。

尽管看起来古怪，`Const` 函子在许多构造中扮演着重要角色。在范畴论里，它是我之前提到的 $\Delta_c$ 函子的一个特例——黑洞的自函子版本。
今后我们还会更多地见到它。

::: details 守法证明：Reader 与 Const
两者的定律都是“按定义成立”。Reader 的情形就是函数复合的单位律与结合律；Const 的情形是因为 `map` 根本不碰任何东西：

```lean
instance (ρ : Type) : LawfulFunctor (Reader ρ) where
  map_const := rfl
  id_map _ := rfl          -- id ∘ g = g
  comp_map _ _ _ := rfl    -- (h ∘ g) ∘ k = h ∘ (g ∘ k)

instance (γ : Type) : LawfulFunctor (Const γ) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```
:::

## 函子的复合

不难让你自己相信，范畴之间的函子可以复合，就像集合之间的函数可以复合一样。两个函子的复合作用在对象上时，
就是它们各自对象映射的复合；作用在态射上时也类似。跳过两个函子之后，恒等态射仍然是恒等态射，态射的复合仍然是态射的复合。
真的没什么大不了的。用 Lean 写出来，两条定律各用一次 `simp` 就证完了——它把 `F` 和 `G` 各自的定律依次用上：

```lean
def CFunctor.comp {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    {E : Type u₃} [Category.{u₃, v₃} E] (G : CFunctor D E) (F : CFunctor C D) : CFunctor C E where
  obj a := G.obj (F.obj a)
  map f := G.map (F.map f)
  map_id a := by simp [F.map_id, G.map_id]       -- G (F id) = G id = id
  map_comp f g := by simp [F.map_comp, G.map_comp] -- G (F (g∘f)) = G (F g ∘ F f) = G (F g) ∘ G (F f)
```

```diagram
padB: (1.8, 0.75) ""
C: (0, 0) "\mathcal{C}"
D: (1.8, 0) "\mathcal{D}"
E: (3.6, 0) "\mathcal{E}"
F: C -> D "F"
G: D -> E "G"
GF: C -> E "G \circ F" bend=-45 side=right
path "先 F 再 G": F G
path "直接 G ∘ F": GF color=green
caption: 函子可以复合：G ∘ F 先用 F 把 C 带到 D，再用 G 把 D 带到 E。
```

特别地，自函子很容易复合。还记得函数 `maybeTail` 吗？我用 Lean 内建的列表重写一遍：

```lean
def maybeTail {α : Type} : List α → Option (List α)
  | []      => none
  | _ :: xs => some xs
```

（我们以前叫作 `nil` 的空列表构造子换成了一对空方括号 `[]`，`cons` 构造子换成了中缀运算符 `::`。）

`maybeTail` 的结果的类型，是两个函子 `Option` 和 `List` 复合后作用在 `α` 上。这两个函子各自配备了自己版本的 `map`，
但如果我们想把某个函数 `f` 作用到复合体的内容——一个“可能存在的列表”——上呢？我们得穿过两层函子。
用 `map` 可以穿过外层的 `Option`。但我们不能直接把 `f` 送进 `Option` 里，因为 `f` 不能作用在列表上。我们得把 `(map f)` 送进去，作用在里层的列表上。
例如，来看看怎样把一个“可能存在的整数列表”的元素都平方：

```lean
def square (x : Int) : Int := x * x

def mis : Option (List Int) := some [1, 2, 3]

def mis2 := Functor.map (Functor.map square) mis

#guard mis2 == some [1, 4, 9]
```

编译器分析了类型之后会推断出：外层的 `map` 应该用 `Option` 实例的实现，里层的则用列表函子的实现。
（用 `<$>` 记号可以写成 `(square <$> ·) <$> mis`。）也许不那么一目了然的是，上面的代码可以改写成：

```lean
def mis3 := (Functor.map ∘ Functor.map) square mis

#guard mis3 == some [1, 4, 9]
```

但请记住，`map` 可以被看作一个只有一个参数的函数：

```lean no-check
Functor.map : (α → β) → (f α → f β)
```

在我们的例子中，`(Functor.map ∘ Functor.map)` 里的第二个 `map` 接受的参数是：

```lean no-check
square : Int → Int
```

返回一个这样类型的函数：

```lean no-check
List Int → List Int
```

然后第一个 `map` 接受这个函数，返回一个函数：

```lean no-check
Option (List Int) → Option (List Int)
```

最后，这个函数被作用在 `mis` 上。所以，两个函子的复合是一个函子，它的 `map` 是对应的两个 `map` 的复合。

::: details 补充：在 Lean 里把“复合函子”做成一个守法的 `Functor`
我们可以给“`F` 套 `G`”起个名字，并证明：只要 `F` 和 `G` 都守法，复合起来也守法。
证明的核心一步是把内层的定律从“对每个 `y` 成立”提升为“两个函数相等”（`funext`），然后用 `rw` 改写外层：

```lean
def Comp (F G : Type → Type) (α : Type) : Type := F (G α)

instance {F G : Type → Type} [Functor F] [Functor G] : Functor (Comp F G) where
  map {α β} (f : α → β) (x : F (G α)) := (Functor.map (Functor.map f : G α → G β) x : F (G β))

instance {F G : Type → Type} [Functor F] [Functor G] [LawfulFunctor F] [LawfulFunctor G] :
    LawfulFunctor (Comp F G) where
  map_const := rfl
  id_map {α} (x : F (G α)) := by
    show Functor.map (Functor.map id : G α → G α) x = x
    have h : (Functor.map id : G α → G α) = id := funext id_map   -- 内层：map id = id
    rw [h, id_map]                                               -- 外层：map id x = x
  comp_map {α β γ} f g (x : F (G α)) := by
    show Functor.map (Functor.map (g ∘ f) : G α → G γ) x
      = Functor.map (Functor.map g : G β → G γ) (Functor.map (Functor.map f : G α → G β) x)
    have h : (Functor.map (g ∘ f) : G α → G γ) = Functor.map g ∘ Functor.map f :=
      funext (comp_map f g)                                      -- 内层：map (g∘f) = map g ∘ map f
    rw [h, comp_map]                                             -- 外层：同一条定律再用一次

-- 现在一个 map 就能穿透两层
def mis4 : Comp Option List Int := some [1, 2, 3]
def mis5 : Comp Option List Int := square <$> mis4
example : (mis5 : Option (List Int)) = some [1, 4, 9] := rfl
```

`have h : … := …` 在证明中途引入一个辅助事实；`rw [h, id_map]` 先用 `h` 改写目标，再用 `id_map`。
`show` 把目标换成一个定义上相等、但写得更明白的形式，好让 `rw` 找得到要改写的地方。
:::

回到范畴论：很明显，函子的复合满足结合律（对象的映射满足结合律，态射的映射也满足结合律）。
而且每个范畴里都有一个平凡的恒等函子：它把每个对象映到自身，把每个态射映到自身。
所以函子具有与某个范畴中的态射完全相同的性质。但那会是哪个范畴呢？它得是一个以范畴为对象、以函子为态射的范畴。一个范畴的范畴。

但一个包含**所有**范畴的范畴必须把自己也包含进去，我们就会陷入与“所有集合的集合”不可能存在同样的悖论。
不过，存在一个所有**小**范畴组成的范畴，叫作 $\mathbf{Cat}$（它本身是大的，所以不能是自己的成员）。
小范畴是指其对象构成一个集合、而不是比集合更大的东西的范畴。请注意，在范畴论里，即使是不可数的无穷集合，也被认为是“小”的。
我之所以提到这些，是因为我觉得这非常奇妙：我们能在许多个抽象层次上认出同样的结构反复出现。以后我们会看到，函子也构成范畴。

::: tip Lean 深入：$\mathbf{Cat}$ 与宇宙层级
“小”和“大”在 Lean 里有一个精确的对应物：**宇宙层级**。我们把“一个对象在 `Type u`、态射在 `Type v` 的范畴”打包成一个结构体 `Cat.{u, v}`，
它的对象是范畴，态射是 `CFunctor`：

```lean
structure Cat where
  Obj : Type u
  [inst : Category.{u, v} Obj]

attribute [instance] Cat.inst

instance catCategory : Category Cat.{u, v} where
  Hom C D := CFunctor C.Obj D.Obj
  id C := CFunctor.id C.Obj
  comp G F := CFunctor.comp G F
  -- 三条定律都由默认的 `rfl` 自动完成！
```

（`[inst : Category Obj]` 让结构体记住对象类型上的范畴结构，`attribute [instance] Cat.inst` 让 Lean 在需要时自动取出它。）

三条范畴定律之所以是 `rfl`，是因为 Lean 的两条“定义性等式”：结构体的 eta 规则（一个结构体等于把它的字段重新装回去），
和**证明无关性**（同一个命题的任意两个证明被视为相等）。所以 `CFunctor.comp F (CFunctor.id C)` 与 `F` 的 `obj`、`map` 按定义相同，
而 `map_id`、`map_comp` 字段是证明，自动相等。

现在看宇宙：`Cat.{u, v}` 本身住在哪里？

```lean
#check (Cat.{0, 0} : Type 1)
```

所有“对象在 `Type 0`”的小范畴组成的 $\mathbf{Cat}$，自己的对象在 `Type 1`——它高了一层，所以它不是自己的一个对象。
这正是原书说的“$\mathbf{Cat}$ 是大的，所以它不能是自己的成员”。Lean 的宇宙层级让这个悖论从根本上无法出现。
:::

## 挑战

1. 能否通过定义下面这个忽略了两个参数的 `fmap`，把类型构造子 `Maybe` 变成一个函子？（提示：检查函子定律。）

   ```lean no-check
   fmap _ _ = nothing
   ```

2. 证明 reader 函子满足函子定律。提示：真的很简单。
3. 用你第二喜欢的语言实现 reader 函子（第一喜欢的当然是 Lean 了）。
4. 证明列表函子满足函子定律。假设这些定律对你所作用的列表的尾部成立（换句话说，使用**归纳法**）。

::: details 参考答案
**1.** 不能。它满足复合律（两边都是 `nothing`），但违反了恒等律：`fmap id (just 1)` 应该等于 `just 1`，它却给出了 `nothing`。
在 Lean 里，我们可以证明“恒等律不成立”——只需一个反例：

```lean
def badFmap {α β : Type} (_ : α → β) (_ : Maybe α) : Maybe β := nothing

-- 复合律碰巧成立：两边都是 nothing
theorem badFmap_comp {α β γ : Type} (f : α → β) (g : β → γ) (m : Maybe α) :
    badFmap (g ∘ f) m = badFmap g (badFmap f m) := rfl

-- 恒等律不成立
theorem badFmap_not_id : ¬ (∀ m : Maybe Nat, badFmap id m = m) := by
  intro h                          -- 假设恒等律对所有 m 都成立……
  have h1 := h (just 1)            -- ……那么对 just 1 也成立：nothing = just 1
  cases h1                         -- 但 nothing 和 just 1 是不同的构造子，矛盾
```

`¬ P` 读作“非 P”，它的定义是 `P → False`：要证明它，就假设 `P`（`intro h`），然后推出矛盾。
最后的 `cases h1` 利用了“不同构造子构造出的值一定不相等”这一事实：等式 `nothing = just 1` 没有任何可能的情况，于是目标自动完成。

所以这个“函子”把每个箭头都映成了同一个箭头，把 `Maybe α` 里的结构撕坏了。
（对比常函子 $\Delta_c$：它把一切映成**恒等**箭头，所以是合法的。`badFmap` 把一切映成“全部变成 `nothing`”，这不是恒等箭头。）

**2.** reader 函子的 `map` 就是函数复合，两条定律分别就是复合的单位律与结合律。用 `calc` 写出等式推理：

```lean
theorem reader_id {ρ α : Type} (g : Reader ρ α) : id <$> g = g := by
  funext r                        -- 两个函数相等：只需对每个输入 r 都相等
  calc (id <$> g) r
      = id (g r) := rfl           -- reader 的 map 是复合
    _ = g r      := rfl           -- id 的定义

theorem reader_comp {ρ α β γ : Type} (f : α → β) (h : β → γ) (g : Reader ρ α) :
    (h ∘ f) <$> g = h <$> (f <$> g) := by
  funext r
  calc ((h ∘ f) <$> g) r
      = (h ∘ f) (g r)        := rfl   -- reader 的 map 是复合
    _ = h (f (g r))          := rfl   -- 复合的定义
    _ = (h <$> (f <$> g)) r  := rfl   -- 复合的定义与 map 的定义（反着用两次）
```

（我们在前面“守法证明”的折叠框里也已经声明了 `LawfulFunctor (Reader ρ)` 的实例。）

**3.** Rust 版本见上文“Rust 视角：reader 函子就是闭包的后处理”。这里再给一个用 trait 对象、可以存进数据结构的版本：

```rust
pub struct Reader<'a, R, A> {
    run: Box<dyn Fn(R) -> A + 'a>,
}

impl<'a, R: 'a, A: 'a> Reader<'a, R, A> {
    pub fn new(f: impl Fn(R) -> A + 'a) -> Self {
        Reader { run: Box::new(f) }
    }
    pub fn map<B: 'a>(self, f: impl Fn(A) -> B + 'a) -> Reader<'a, R, B> {
        Reader::new(move |r| f((self.run)(r)))
    }
    pub fn run(&self, r: R) -> A {
        (self.run)(r)
    }
}

pub fn demo() -> usize {
    let greet = Reader::new(|name: &str| format!("Hello, {name}!"));
    greet.map(|s| s.len()).run("Lean") // 12
}
```

**4.** 对列表做**归纳**：先证明定律对空列表成立（基础情形），再假设它对尾巴 `t` 成立（归纳假设 `ih`），证明它对 `cons x t` 也成立。

```lean
theorem MyList.map_id {α : Type} (xs : MyList α) : MyList.map id xs = xs := by
  induction xs with
  | nil => rfl                                   -- 基础情形：map id nil = nil
  | cons x t ih =>                               -- ih : MyList.map id t = t
    calc MyList.map id (MyList.cons x t)
        = MyList.cons (id x) (MyList.map id t) := rfl    -- map 的定义
      _ = MyList.cons x (MyList.map id t)      := rfl    -- id 的定义
      _ = MyList.cons x t                      := by rw [ih]  -- 归纳假设

theorem MyList.map_comp {α β γ : Type} (f : α → β) (g : β → γ) (xs : MyList α) :
    MyList.map (g ∘ f) xs = MyList.map g (MyList.map f xs) := by
  induction xs with
  | nil => rfl
  | cons x t ih =>                               -- ih : map (g ∘ f) t = map g (map f t)
    calc MyList.map (g ∘ f) (MyList.cons x t)
        = MyList.cons (g (f x)) (MyList.map (g ∘ f) t)          := rfl          -- map 的定义
      _ = MyList.cons (g (f x)) (MyList.map g (MyList.map f t)) := by rw [ih]   -- 归纳假设
      _ = MyList.map g (MyList.map f (MyList.cons x t))         := rfl          -- map 的定义（反着用两次）

instance : LawfulFunctor MyList where
  map_const := rfl
  id_map := MyList.map_id
  comp_map := MyList.map_comp
```

`induction xs with` 和 `cases` 很像，也是按构造子分情况，但在递归的那个情况（`cons x t`）里额外送给你一个**归纳假设** `ih`：
“定律对 `t` 已经成立”。`rw [ih]` 用这个等式把目标里的 `MyList.map id t` 改写成 `t`。
:::

::: info 数学小课堂：数学归纳法
你也许在高中见过“多米诺骨牌”式的数学归纳法：要证明某个命题对所有自然数 $n$ 成立，只需证明

1. 它对 $0$ 成立（推倒第一块骨牌）；
2. 如果它对 $n$ 成立，那么它对 $n+1$ 也成立（每一块倒下都会推倒下一块）。

列表上的归纳是同一回事，只不过“自然数”换成了“列表”：每个列表要么是 `nil`（第一块骨牌），要么是 `cons x t`，它比 `t` 多一个元素（下一块骨牌）。
所以只要证明命题对 `nil` 成立，并且“对 `t` 成立 ⇒ 对 `cons x t` 成立”，它就对所有列表成立。
自然数 `Nat` 本身在 Lean 里也是这样定义的：`inductive Nat | zero | succ (n : Nat)`——它就是一个“元素类型为 `Unit`”的列表！
:::

## 本章小结

- **函子**是范畴之间的映射：把对象映到对象（`obj`），把态射映到态射（`map`），并且**保持恒等**与**保持复合**。
- 在 Lean 里，`CTFP.CFunctor` 把这两条定律写成结构体的字段；不交出证明就造不出函子。
- 函子可以坍缩（把多个对象、箭头压到一起），可以嵌入，但不能“撕裂”。从单例范畴出发的函子选出一个对象；常函子 $\Delta_c$ 把一切压进一个黑洞。
- 编程中的函子是类型范畴上的**自函子**：一个类型构造子 `f : Type → Type`，加上把 `α → β` 提升为 `f α → f β` 的 `map`（`<$>`）。
- 我们为 `Maybe`/`Option`、`List`、reader（`ρ → ·`）、`Const γ` 定义了 `Functor` 实例，并用等式推理（`calc`）、分情况（`cases`）和归纳（`induction`）证明了函子定律。
- Lean 的 `LawfulFunctor` 把函子定律放进类型类——Haskell 只能口头约定，Rust 因为没有高阶类型连 `Functor` trait 本身都写不出来。
- 等式推理之所以可靠，是因为纯函数没有副作用；带副作用的函数（或展开表达式的宏）会让它失效。
- 函子可以看作“容器”，但更准确地说，它是“可以在里面用函数做变换的东西”，值不一定真的在里面（reader、`Task`、`IO`、`Const`）。
- 函子可以复合，复合函子的 `map` 是各自 `map` 的复合。范畴与函子构成范畴 $\mathbf{Cat}$；在 Lean 里，它的宇宙层级比它的成员高一层，悖论由此避免。
