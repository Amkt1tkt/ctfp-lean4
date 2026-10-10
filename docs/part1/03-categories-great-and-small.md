# 1.3 大大小小的范畴

想真正体会范畴是什么，最好的办法是多看例子。范畴形形色色、大小不一，而且常常在你意想不到的地方冒出来。我们先从一个简单得不能再简单的例子说起。

```lean hidden
universe u v

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

open CTFP
```

::: tip Lean 深入：本章用到的范畴定义
在 [1.1 范畴：复合的本质](/part1/01-category) 里，我们已经逐行读过全书统一的 `CTFP.Category`。本章把它原样放在页首一个隐藏代码块里（点任意代码块的“在线运行”就能看到），下面直接使用。再提醒一下它的形状：

```lean no-check
class Category (Obj : Type u) where
  Hom  : Obj → Obj → Type v                         -- a ⟶ b：从 a 到 b 的态射
  id   : (a : Obj) → Hom a a                        -- 𝟙 a：恒等态射
  comp : {a b c : Obj} → Hom b c → Hom a b → Hom a c -- g ⊚ f：先 f 后 g
  id_comp : ∀ f, comp (id b) f = f                  -- 左单位律
  comp_id : ∀ f, comp f (id a) = f                  -- 右单位律
  assoc   : ∀ f g h, comp h (comp g f) = comp (comp h g) f  -- 结合律
```

要造一个范畴，就是给出 `Hom`、`id`、`comp` 三样数据，再**证明**三条定律。本章的每个例子，我们都会真的写出这样一个 `instance`，让 Lean 替我们把关。
:::

## 没有对象

最平凡的范畴，是一个对象也没有的范畴；既然没有对象，自然也就没有态射。单独拿出来看，它是个相当凄凉的范畴。但放在别的范畴的语境里，它可能很重要。比如在“所有范畴组成的范畴”里（没错，真有这么个东西），它就占有一席之地。如果你觉得空集是有意义的，那为什么不能有空范畴呢？

在 Lean 里，“没有元素的类型”现成就有：`Empty`。拿它当对象的类型，就得到空范畴：

```lean
instance emptyCategory : Category.{0, 0} Empty where
  Hom a _ := nomatch a      -- 根本不存在对象 a，所以这里什么也不用给
  id a := nomatch a
  comp {a} := nomatch a
  id_comp {a} := nomatch a  -- 三条定律也都“空洞地”成立
  comp_id {a} := nomatch a
  assoc {a} := nomatch a
```

::: tip Lean 深入：`nomatch` 与 `Category.{0, 0}`
- `nomatch a` 的意思是“对 `a` 做模式匹配，但一个分支也不写”。因为 `Empty` 没有任何构造子，一个分支都不需要，Lean 认可这样的匹配是**穷尽**的。它可以出现在任何期望类型的位置——既能当作“数据”（`Hom`、`id`），也能当作“证明”（三条定律）。这就是逻辑里的“从矛盾出发可以推出一切”（ex falso quodlibet）。
- `Category.{0, 0}` 显式指定了两个宇宙参数：对象的类型在 `Type 0`，hom-集也在 `Type 0`。`Category` 的 `Hom` 落在哪一层宇宙无法从 `Empty` 本身推断出来，所以我们得自己写明。本章的例子都是“小”范畴，统一写 `{0, 0}`；宇宙的意义在本章末尾讲“局部小”时再细说。
:::

::: tip Rust 视角
Rust 里的空类型是 `enum Void {}`。对它的值写 `match v {}`，编译器同样认可这个“零分支”的匹配是穷尽的，而且它的类型可以是任意类型——这正是 Lean 的 `nomatch`。`std::convert::Infallible` 就是标准库里的这样一个空类型。
:::

::: info 数学小课堂：空集与“空洞地成立”
**空集** $\varnothing$ 是不含任何元素的集合。关于空集有一条初学者常觉得别扭的规律：“空集中的**每个**元素都满足某某性质”永远为真——因为根本找不到反例。这叫**空洞真**（vacuous truth）。

空范畴的三条定律正是这样成立的：“对每一对可复合的态射，结合律成立”——可是一个态射也没有，所以没有任何东西需要检查。Lean 里的 `nomatch` 就是把这句话变成了证明。
:::

## 简单的图

只要用箭头把对象连起来，就能造出范畴。你可以设想：从任意一张有向图出发，往里面添加箭头，直到它变成一个范畴。

第一步，给每个节点添上一条恒等箭头。第二步，对于任意两条首尾相接的箭头——前一条的终点恰好是后一条的起点（换句话说，任意两条**可复合的**（composable）箭头）——添上一条新箭头，作为它们的复合。每添一条新箭头，你都得再考虑它和其它所有箭头（恒等箭头除外）以及和它自己的复合。最后通常会得到无穷多条箭头，不过这没关系。

比如从下面这张只有两条边的图出发：

```diagram
a: (0, 0)
b: (1.6, 0)
c: (3.2, 0)
f: a -> b "f"
g: b -> c "g"
caption: 一张有向图：三个节点、两条边
```

补上三条恒等箭头和一条复合箭头 $g \circ f$，它就成了一个范畴（这个例子里恰好不会冒出更多箭头）：

```diagram
a: (0, 0.6)
b: (1.6, 0.6)
c: (3.2, 0.6)
f: a -> b "f"
g: b -> c "g"
gf: a -> c "g \circ f" bend=-45 side=right color=brand
ida: a -> a "\mathrm{id}_a" loop=up color=gray
idb: b -> b "\mathrm{id}_b" loop=up color=gray
idc: c -> c "\mathrm{id}_c" loop=up color=gray
path "先走 f 再走 g": f g
path "直接走 g∘f": gf color=green
caption: 由这张图生成的自由范畴：灰色是新加的恒等箭头，蓝色是新加的复合箭头
```

换个角度看这个过程：你在构造一个范畴，图中的每个节点对应它的一个对象，而它的态射就是所有由可复合的边连成的**链**（chain）。（你甚至可以把恒等态射看作长度为零的链。）

这样得到的范畴，叫作由给定的图生成的**自由范畴**（free category）。这是**自由构造**（free construction）的一个例子：给定一个结构，用尽可能少的新东西把它补全，使它满足某些定律（这里是范畴的定律）。以后我们还会见到更多自由构造的例子。

::: info 数学小课堂：有向图与路径
**有向图**（directed graph）就是一些**节点**（node，也叫顶点），加上一些带方向的**边**（edge），每条边从某个节点指向某个节点（可以指向自己，两个节点之间也可以有多条边）。

图里的一条**路径**是一串首尾相接的边：$e_1$ 从 $a$ 到 $b$，$e_2$ 从 $b$ 到 $c$……路径的“长度”就是边的条数。长度为 0 的路径就是“原地不动”。

自由范畴的态射，正是这些路径；复合就是把两条路径接起来；恒等态射就是长度为 0 的路径。接路径显然满足结合律（先把前两段接起来，还是先把后两段接起来，结果都是同一串边），也显然以空路径为单位。
:::

### 用 Lean 构造自由范畴

“所有可复合的链”这个说法，在 Lean 里可以一字不差地写成一个**归纳类型族**。我们把图表示成“节点类型 `V`”加上“对每一对节点 `a b`，从 `a` 到 `b` 的边组成的类型 `E a b`”：

```lean
/-- 图 `E` 中从 `a` 到 `b` 的路径（边的链）。 -/
inductive Path {V : Type} (E : V → V → Type) : V → V → Type where
  /-- 长度为零的路径：原地不动。 -/
  | nil (a : V) : Path E a a
  /-- 先走一条边 `e : a → b`，再沿路径 `p` 从 `b` 走到 `c`。 -/
  | cons {a b c : V} (e : E a b) (p : Path E b c) : Path E a c
```

::: tip Lean 深入：带索引的归纳类型
`Path E` 后面的 `: V → V → Type` 表示：`Path E a c` 是一族类型，**由两个节点 `a`、`c` 索引**。两个构造子各自规定了自己落在哪个索引上：`nil a` 只能是 `Path E a a`（起点终点相同）；`cons e p` 要求 `e` 的终点和 `p` 的起点是同一个 `b`，否则根本写不出来。

于是，“首尾相接”这个条件不是运行时检查的，而是**写在类型里**的：一条不连贯的“路径”在 Lean 里无法构造。这类似于 `List`，只不过每个“元素”（边）的类型都依赖于它的前一个元素。
:::

::: tip Rust 视角
Rust 的类型不能依赖于值，所以你大概只能写一个 `Vec<Edge>`，再写一个 `fn is_valid(&self) -> bool` 在运行时检查首尾是否相接。Lean 的 `Path` 把这个检查挪到了编译期：类型检查通过，就保证路径是连贯的。
:::

把两条路径接起来，就是复合。按结构递归定义 `append`，然后证明它满足结合律、以空路径为单位：

```lean
namespace Path
variable {V : Type} {E : V → V → Type}

/-- 先走 `p`，再走 `q`。 -/
def append : {a b c : V} → Path E a b → Path E b c → Path E a c
  | _, _, _, nil _,    q => q
  | _, _, _, cons e p, q => cons e (append p q)

/-- 右单位律：后面接一条空路径，什么也没变。 -/
theorem append_nil : ∀ {a b : V} (p : Path E a b), p.append (nil b) = p
  | _, _, nil _    => rfl
  | _, _, cons e p => by simp [append, append_nil p]

/-- 结合律。 -/
theorem append_assoc : ∀ {a b c d : V} (p : Path E a b) (q : Path E b c) (r : Path E c d),
    (p.append q).append r = p.append (q.append r)
  | _, _, _, _, nil _,    _, _ => rfl
  | _, _, _, _, cons e p, q, r => by simp [append, append_assoc p q r]

/-- 路径的长度（边的条数）。 -/
def length : {a b : V} → Path E a b → Nat
  | _, _, nil _    => 0
  | _, _, cons _ p => p.length + 1
end Path
```

这两个定理的证明是**结构归纳**：定理本身被写成一个递归函数，对路径的两种形状分别处理。空路径的情况按定义直接成立（`rfl`）；`cons e p` 的情况，先用 `simp [append]` 展开一步定义，再引用对更短的路径 `p` 已经成立的结论（`append_nil p`，即归纳假设）。左单位律 `(nil a).append p = p` 则直接是 `append` 的第一行定义，连证明都不用写。

现在可以造出自由范畴了：

```lean
/-- 图 `E` 生成的自由范畴的对象：就是图的节点，外面包一层，好让 Lean 找到下面的实例。 -/
structure FreeCat {V : Type} (E : V → V → Type) where
  of : V

instance freeCategory {V : Type} (E : V → V → Type) : Category.{0, 0} (FreeCat E) where
  Hom a b := Path E a.of b.of        -- 态射 = 路径
  id a := Path.nil a.of              -- 恒等 = 长度为 0 的路径
  comp g f := f.append g             -- g ⊚ f = 先走 f 再走 g
  id_comp f := Path.append_nil f
  comp_id _ := rfl
  assoc f g h := Path.append_assoc f g h
```

::: tip Lean 深入：为什么要包一层 `structure FreeCat`
Lean 的类型类实例是**按类型查找**的：看到 `a ⟶ b`，它要根据 `a` 的类型决定用哪个 `Category` 实例。如果我们直接给 `V` 声明实例，同一个 `V` 上就只能有一种范畴结构——可同一组节点完全可以配上不同的边。包一层 `FreeCat E` 以后，“节点类型 + 哪张图”都写进了对象的类型里，实例查找就不会混淆。这和 Rust 的 **newtype 模式**（`struct Meters(f64);`）是同一个思路：想给同一个底层类型挂上另一套 trait 实现，就包一层新类型。
:::

用开头那张 $a \to b \to c$ 的图试一试：

```lean
inductive V3 | a | b | c

/-- 两条边：f : a → b，g : b → c。 -/
inductive E3 : V3 → V3 → Type
  | f : E3 .a .b
  | g : E3 .b .c

def fP : (⟨.a⟩ : FreeCat E3) ⟶ ⟨.b⟩ := .cons .f (.nil _)
def gP : (⟨.b⟩ : FreeCat E3) ⟶ ⟨.c⟩ := .cons .g (.nil _)

-- 复合 g ⊚ f 就是两条边连成的链 [f, g]，长度为 2
example : gP ⊚ fP = Path.cons E3.f (Path.cons E3.g (Path.nil _)) := rfl
example : (gP ⊚ fP).length = 2 := rfl
```

如果图里有环，自由范畴里就会有无穷多条态射。最简单的例子：一个节点加一条指向自己的边 $e$。于是 $e$、$e \circ e$、$e \circ e \circ e$……全都是不同的态射，它们和自然数一一对应（按长度）。这正是挑战题 1 的第二小题，参考答案里给出了 Lean 证明。

```diagram
x: (0, 0) "\bullet"
e: x -> x "e" loop=right
caption: 一个节点、一条自环边。它生成的自由范畴里有 id、e、e∘e、e∘e∘e……无穷多条态射
```

::: tip 补充：Mathlib 里的自由范畴
Lean 的数学库 Mathlib（本书不依赖它）中，“图”叫 `Quiver`（箭图），路径类型叫 `Quiver.Path`，自由范畴叫 `CategoryTheory.Paths`。它们的定义和我们上面写的几乎一样。
:::

## 序

接下来是完全不同的东西！考虑这样一种范畴：态射是对象之间的一种**关系**——小于或等于关系。我们来检查一下它是不是真的构成范畴。有恒等态射吗？每个对象都小于等于它自己：有！有复合吗？如果 $a \leqslant b$ 且 $b \leqslant c$，那么 $a \leqslant c$：有！复合满足结合律吗？满足！带有这样一种关系的集合称为**预序**（preorder），所以预序确实是一个范畴。

你还可以要求更强的关系，再加一个条件：如果 $a \leqslant b$ 且 $b \leqslant a$，那么 $a$ 必须和 $b$ 是同一个东西。这样的关系叫作**偏序**（partial order）。

最后，你还可以要求任意两个对象之间都有关系，不是这个方向就是那个方向；这就得到了**线性序**（linear order），也叫**全序**（total order）。

::: info 数学小课堂：关系，以及自反、传递、反对称、完全
集合 $S$ 上的一个**二元关系** $R$，就是对每一对元素 $(a, b)$ 回答“是”或“否”：$a$ 与 $b$ 有没有关系 $R$。写作 $a \mathrel{R} b$。下面是几条常见的性质：

| 性质 | 含义 | 例子 |
|---|---|---|
| 自反（reflexive） | 对所有 $a$，$a \mathrel{R} a$ | $5 \le 5$ |
| 传递（transitive） | $a \mathrel{R} b$ 且 $b \mathrel{R} c$ ⇒ $a \mathrel{R} c$ | $2 \le 3,\ 3 \le 7 \Rightarrow 2 \le 7$ |
| 反对称（antisymmetric） | $a \mathrel{R} b$ 且 $b \mathrel{R} a$ ⇒ $a = b$ | $a \le b,\ b \le a \Rightarrow a = b$ |
| 完全（total） | 对所有 $a, b$，$a \mathrel{R} b$ 或 $b \mathrel{R} a$ | 任意两个自然数总能比大小 |

- **预序** = 自反 + 传递。
- **偏序** = 预序 + 反对称。
- **全序** = 偏序 + 完全。

三个例子帮你分清它们：

1. 自然数上的 $\le$：全序。
2. 正整数上的**整除**关系 $a \mid b$（“$a$ 能整除 $b$”）：自反（$a \mid a$）、传递（$a \mid b$、$b \mid c$ ⇒ $a \mid c$）、反对称（互相整除的正整数必相等），所以是偏序；但 $2$ 和 $3$ 谁也不整除谁，所以**不是**全序。
3. 字符串“按长度比较”：$s \preceq t$ 当且仅当 `s.length ≤ t.length`。自反、传递都没问题，所以是预序；但 `"ab"` 和 `"cd"` 互相 $\preceq$，它们却不相等，所以**不是**偏序。
:::

我们把这几种有序集刻画成范畴。预序是这样一种范畴：从任意对象 $a$ 到任意对象 $b$，**至多**只有一条态射。这样的范畴还有一个名字，叫“瘦的”。预序就是一个**瘦范畴**（thin category）。

### 用 Lean 表达序

先用类型类把这三种序写下来。每个类只是在前一个的基础上多要求一条定律：

```lean
/-- 预序：自反 + 传递。`extends LE α` 表示它自带一个 `≤` 运算。 -/
class Preorder (α : Type) extends LE α where
  le_refl  : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c

/-- 偏序：再加反对称。 -/
class PartialOrder (α : Type) extends Preorder α where
  le_antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b

/-- 全序（线性序）：再加完全性。 -/
class LinearOrder (α : Type) extends PartialOrder α where
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
```

::: tip Lean 深入：`extends`
`class B extends A` 表示 `B` 包含 `A` 的全部字段，外加自己的新字段。有了 `PartialOrder α` 的实例，Lean 自动知道 `α` 也是 `Preorder` 和 `LE`。它很像 Rust 的 supertrait：`trait PartialOrder: Preorder { … }`。区别在于 Lean 的字段里可以有**定律**（`le_antisymm` 是一个证明），而 Rust 的 trait 只能写方法签名。
:::

接下来把任意预序变成一个范畴。这里有一个值得停下来好好讲的地方。

::: tip Lean 深入：Prop 与 Type，以及 `PLift`
在 Lean 里，`a ≤ b` 是一个**命题**，它的类型是 `Prop`；它的“元素”是**证明**。而我们的 `Category` 要求 `Hom a b : Type v`——hom-集得是一个装“数据”的类型。如果天真地写

```lean no-check
instance (α : Type) [Preorder α] : Category.{0, 0} (Thin α) where
  Hom a b := a.val ≤ b.val   -- 错误！
  ...
```

Lean 会报错：`a.val ≤ b.val` 的类型是 `Prop`，但这里期望的是 `Type`。

`Prop` 和 `Type` 是 Lean 宇宙层级里的两个不同“楼层”：`Prop` 是 `Sort 0`，`Type` 是 `Sort 1`。两者最大的区别是 `Prop` 满足**证明无关性**（proof irrelevance）：同一个命题的任意两个证明，在 Lean 看来是**定义上相等**的。你只关心“它成立”，不关心“它是怎么被证明的”。`Type` 里的值则各不相同：`3 : Nat` 和 `5 : Nat` 当然是两个不同的东西。

要把一个命题“搬”到 `Type` 里，核心库提供了 `PLift`：

```lean no-check
structure PLift (α : Sort u) : Type u where
  up ::
  down : α
```

`PLift (a ≤ b)` 是一个 `Type`，它的元素是 `⟨h⟩`，其中 `h : a ≤ b` 是一个证明。（另一个容易混淆的工具 `ULift` 只能把 `Type u` 抬到更高的 `Type`，不能处理 `Prop`；所以这里用的是 `PLift`，P 代表 Prop。）

好处在于：`PLift (a ≤ b)` 要么是空的（如果 $a \le b$ 不成立，就一个证明也造不出来），要么只有**一个**元素（如果成立，所有证明都相等）。这恰好就是“瘦”的定义！
:::

```lean
/-- 把预序 `α` 看成范畴时的对象：包一层，原因同 `FreeCat`。 -/
structure Thin (α : Type) where
  val : α

instance thinCategory (α : Type) [Preorder α] : Category.{0, 0} (Thin α) where
  Hom a b := PLift (a.val ≤ b.val)                    -- 态射 = “a ≤ b 的证明”
  id a := ⟨Preorder.le_refl a.val⟩                    -- 恒等 = 自反性
  comp g f := ⟨Preorder.le_trans f.down g.down⟩       -- 复合 = 传递性
  -- 三条定律不用写：默认的 `by intros; rfl` 就够了，因为证明无关性
```

注意三条定律一条也没写，用的是 `Category` 里的默认证明 `by intros; rfl`。比如左单位律要求 `comp (id b) f = f`，两边都是 “`a ≤ b` 的某个证明”，而同一命题的证明都相等，于是 `rfl` 直接成立。

瘦范畴最重要的性质——两点之间至多一条态射——也只需一行：

```lean
/-- 瘦：从 a 到 b 的任意两条态射都相等。 -/
theorem thin {α : Type} [Preorder α] {a b : Thin α} (f g : a ⟶ b) : f = g := by
  cases f; cases g; rfl
```

`cases f` 把 `f` 拆成 `⟨h₁⟩`，`cases g` 把 `g` 拆成 `⟨h₂⟩`，剩下的目标 `⟨h₁⟩ = ⟨h₂⟩` 由证明无关性得到，`rfl` 收尾。

我们来给自然数装上 $\le$，看看效果：

```lean
instance : Preorder Nat where
  le_refl := Nat.le_refl
  le_trans := Nat.le_trans
instance : PartialOrder Nat where
  le_antisymm := Nat.le_antisymm
instance : LinearOrder Nat where
  le_total := Nat.le_total

def le35 : (⟨3⟩ : Thin Nat) ⟶ ⟨5⟩ := ⟨by decide⟩
def le57 : (⟨5⟩ : Thin Nat) ⟶ ⟨7⟩ := ⟨by decide⟩
def le37 : (⟨3⟩ : Thin Nat) ⟶ ⟨7⟩ := ⟨by decide⟩

-- 3 ≤ 5 与 5 ≤ 7 的复合，就是那条唯一的 3 ≤ 7
example : le57 ⊚ le35 = le37 := thin _ _
```

这里的 `decide` 是一个 tactic：对于可以机械判定真假的命题（比如两个具体自然数比大小），它让 Lean 直接算出结果并据此给出证明。

瘦范畴有一个很妙的推论：**在预序里，任何图都交换**。从 $a$ 到 $c$ 不管走哪条路，到达时得到的都是同一条态射，因为从 $a$ 到 $c$ 本来就最多只有一条。点下面的按钮看看：

```diagram
n3: (0, 1.2) "3"
n5: (1.5, 0) "5"
n6: (1.5, 2.4) "6"
n7: (3, 1.2) "7"
a35: n3 -> n5 "\le"
a57: n5 -> n7 "\le"
a36: n3 -> n6 "\le" side=right
a67: n6 -> n7 "\le" side=right
a37: n3 -> n7 "\le" color=brand
path "经过 5": a35 a57
path "经过 6": a36 a67 color=purple
path "直接走": a37 color=green
caption: 在 (ℕ, ≤) 中：三条从 3 到 7 的路径，复合出来都是同一条态射
```

### hom-集

范畴 $\mathcal{C}$ 中从对象 $a$ 到对象 $b$ 的态射所组成的集合，称为 **hom-集**（hom-set，即“态射集合”），记作 $\mathcal{C}(a, b)$，有时也写成 $\mathbf{Hom}_{\mathcal{C}}(a, b)$。在 Lean 里，它就是类型 `a ⟶ b`，也就是 `Category.Hom a b`。

::: info 数学小课堂：hom-集
hom-集只是给“从 $a$ 到 $b$ 的所有箭头”起了个名字。几个例子：

- 在类型与函数的范畴里，$\mathbf{Type}(\mathtt{Nat}, \mathtt{Bool})$ 就是所有 `Nat → Bool` 函数组成的集合——无穷多个。
- 在开头 $a \to b \to c$ 的自由范畴里，$\mathcal{C}(a, c) = \{g \circ f\}$，只有一个元素；$\mathcal{C}(c, a) = \varnothing$，是空的。
- 在一个预序里，每个 hom-集要么是空集，要么只有一个元素（**单元素集**，singleton）。

“单元素集”就是恰好有一个元素的集合。
:::

所以，预序中的每个 hom-集要么是空的，要么是单元素集。这也包括 hom-集 $\mathcal{C}(a, a)$，即从 $a$ 到 $a$ 的态射集合：在任何预序中，它都必须是单元素集，里面只有恒等态射。不过，预序中可以有**环**（cycle），而偏序中不允许有环。

“按长度比较字符串”就是一个有环的预序：`"ab"` 和 `"cd"` 长度相同，于是它们之间两个方向都有箭头：

```lean
structure ByLen where
  s : String

instance : Preorder ByLen where
  le a b := a.s.length ≤ b.s.length
  le_refl _ := Nat.le_refl _
  le_trans := Nat.le_trans

def ab : Thin ByLen := ⟨⟨"ab"⟩⟩
def cd : Thin ByLen := ⟨⟨"cd"⟩⟩

def abToCd : ab ⟶ cd := ⟨(by decide : "ab".length ≤ "cd".length)⟩
def cdToAb : cd ⟶ ab := ⟨(by decide : "cd".length ≤ "ab".length)⟩

-- 一个环：ab → cd → ab。由于瘦，绕一圈回来就等于恒等态射
example : cdToAb ⊚ abToCd = 𝟙 ab := thin _ _
example : ab ≠ cd := by simp [ab, cd]

/-- 所以 ByLen 不是偏序：反对称性不成立。 -/
example : ¬ (∀ a b : ByLen, a ≤ b → b ≤ a → a = b) := by
  intro h
  have := h ⟨"ab"⟩ ⟨"cd"⟩ (by decide : "ab".length ≤ "cd".length)
    (by decide : "cd".length ≤ "ab".length)
  simp at this
```

偏序之所以不允许环，正是因为反对称性：如果 $a \to b$ 和 $b \to a$ 都存在，反对称性就逼迫 $a = b$。整除关系就是一个偏序，但它不是全序：

```lean
/-- 用整除关系排序的自然数。 -/
structure Dvd' where
  n : Nat

instance : Preorder Dvd' where
  le a b := a.n ∣ b.n
  le_refl a := Nat.dvd_refl a.n
  le_trans := Nat.dvd_trans

instance : PartialOrder Dvd' where
  le_antisymm {a b} h₁ h₂ := by
    cases a; cases b                  -- 拆开包装
    simp only [Dvd'.mk.injEq]         -- 目标变成 n = m
    exact Nat.dvd_antisymm h₁ h₂      -- 核心库的定理

/-- 不是全序：2 和 3 谁也不整除谁。 -/
example : ¬ ∀ a b : Dvd', a ≤ b ∨ b ≤ a := by
  intro h
  have h23 : 2 ∣ 3 ∨ 3 ∣ 2 := h ⟨2⟩ ⟨3⟩
  revert h23
  decide
```

（严格说来，`Nat` 里 $0$ 能被任何数整除、却只整除 $0$ 自己，但这不影响上面的结论。）

下面这个小工具让你亲手摆弄几个有限的序。点两个对象，看看它们之间的 hom-集；切换到“全部箭头”，看看补上恒等和复合以后箭头有多少——但无论多少，两点之间永远至多一条。

<div><Ch1_3PreorderExplorer /></div>

### 序与排序

能认出预序、偏序和全序非常重要，原因在于排序。快速排序、冒泡排序、归并排序等排序算法，只能在全序上正确工作。偏序则可以用拓扑排序（topological sort）来排。

Lean 核心库里的 `List.mergeSort` 恰好能说明这一点。它的正确性定理 `List.pairwise_mergeSort` 要求比较函数满足两个前提：

```lean
#check @List.pairwise_mergeSort
-- ∀ {α} {le : α → α → Bool},
--   (∀ a b c, le a b → le b c → le a c) →     -- 传递
--   (∀ a b, le a b || le b a) →                -- 完全
--   ∀ l, (l.mergeSort le).Pairwise le          -- 结果是有序的

#guard [5, 2, 9, 1].mergeSort (· ≤ ·) == [1, 2, 5, 9]
```

一个是传递，一个是完全：正是“全序”里干活的那两条。（细心的读者会发现，它没有要求反对称：一个“完全的预序”就够了。比如按长度给字符串排序完全没问题，长度相同的字符串谁先谁后都算“有序”。）如果比较关系不完全，比如整除，那么“排好序”这个说法本身就没有意义：`[2, 3]` 和 `[3, 2]` 哪个才算排好了？

::: tip Rust 视角：`Ord` 与 `PartialOrd`
Rust 把这个区别直接做进了标准库。`slice::sort` 要求元素实现 `Ord`（全序），而 `f64` 只实现了 `PartialOrd`——因为 `NaN` 跟谁都比不了大小，包括它自己（所以 `f64` 上的 `<=` 连自反性都没有）。于是 `vec_of_f64.sort()` 编译不过，你得明确告诉编译器怎么处理这种情况，例如用 IEEE 754 规定的全序 `total_cmp`：

```rust
pub fn sort_floats(v: &mut Vec<f64>) {
    v.sort_by(|a, b| a.total_cmp(b));
}
```
:::

## 作为集合的幺半群

幺半群是一个简单得令人难为情、却又强大得惊人的概念。基础算术背后就是它：加法和乘法都构成幺半群。幺半群在编程中无处不在：字符串、列表、可折叠的数据结构、并发编程里的 future、函数式响应式编程里的事件，等等。

传统上，幺半群被定义为一个带有二元运算的集合。对这个运算的全部要求，只是它满足结合律，并且存在一个特殊元素，对这个运算而言表现得像“单位”。

例如，带零的自然数在加法下构成幺半群。结合律的意思是：

$$(a + b) + c = a + (b + c)$$

（换句话说，做加法时可以省略括号。）

单位元是零，因为：

$$0 + a = a$$

以及

$$a + 0 = a$$

第二个等式其实是多余的，因为加法满足交换律 $(a + b = b + a)$；但交换律并不是幺半群定义的一部分。比如字符串拼接就不满足交换律，可它依然构成幺半群。顺便一提，字符串拼接的单位元是空字符串，把它接在任意字符串的哪一边，都不会改变那个字符串。

::: info 数学小课堂：二元运算、结合律、单位元
- 集合 $M$ 上的**二元运算**，是一个函数 $M \times M \to M$：吃进两个元素，吐出一个元素。例如加法 $(3, 4) \mapsto 7$。
- **结合律**：$(a \cdot b) \cdot c = a \cdot (b \cdot c)$。它说的是“先算哪两个”不重要，但**顺序**（谁在左、谁在右）没有变。
- **交换律**：$a \cdot b = b \cdot a$。它说的是可以交换左右——这是另一回事，幺半群不要求它。
- **单位元** $e$：$e \cdot a = a = a \cdot e$。

一个**幺半群**（monoid）就是三元组 $(M, \cdot, e)$，满足结合律和单位元律。例子与反例：

| 集合与运算 | 单位元 | 是幺半群吗？ |
|---|---|---|
| $(\mathbb{N}, +)$ | $0$ | 是（还交换） |
| $(\mathbb{N}, \times)$ | $1$ | 是（还交换） |
| $(\mathbb{N}, \max)$ | $0$ | 是 |
| 字符串, 拼接 | `""` | 是（不交换：`"ab" ++ "c" ≠ "c" ++ "ab"`） |
| $(\mathbb{N}, -)$ | — | 否：$(5 - 3) - 1 \ne 5 - (3 - 1)$，不满足结合律 |
| 正整数, $+$ | — | 否：没有单位元（$0$ 不在里面） |
:::

在 Haskell 里，可以为幺半群定义一个类型类：一个类型，它有一个叫 `mempty` 的单位元，以及一个叫 `mappend` 的二元运算。在 Lean 里，同样的东西写作：

```lean
namespace Plain

class Monoid (m : Type) where
  mempty  : m
  mappend : m → m → m

end Plain
```

`class` 声明一个类型类：任何类型 `m`，只要提供了这两样东西，就可以成为 `Monoid`。（我们把它放在 `Plain` 命名空间里，因为马上要写一个更好的版本。）

双参数函数的类型签名 `m → m → m`，乍看可能有点怪，等我们讲到柯里化，它就完全说得通了。带有多个箭头的签名，有两种基本的理解方式：一种是把它看作多参数函数，最右边的类型是返回类型；另一种是把它看作单参数函数（参数是最左边那个），返回一个函数。后一种理解可以通过加括号来强调：`m → (m → m)`。这对括号是多余的，因为箭头是**右结合**的——Lean 和 Haskell 在这一点上完全一样。我们马上还会回到这种理解方式。

::: tip Rust 视角：多参数函数与柯里化
在 Rust 里，`fn mappend(a: M, b: M) -> M` 和 `fn mappend(a: M) -> impl Fn(M) -> M` 是两个不同的东西。在 Lean 里它们是**同一个东西**：`m → m → m` 就是 `m → (m → m)`。所以你可以只给 `mappend` 一个参数，得到一个“还在等第二个参数”的函数，比如 `Monoid.mappend "foo" : String → String`。
:::

接下来要指出的是：在 Haskell 里，没有办法表达 `mempty` 和 `mappend` 的幺半群性质（即 `mempty` 是单位元、`mappend` 满足结合律）。确保它们成立，是程序员自己的责任。

**而在 Lean 里，我们可以把定律直接写进类型类。**类型类的字段不仅可以是数据，还可以是**证明**：

```lean
/-- 真正的幺半群：数据 + 定律。 -/
class Monoid (m : Type) where
  mempty  : m
  mappend : m → m → m
  mempty_mappend : ∀ x : m, mappend mempty x = x                 -- 左单位律
  mappend_mempty : ∀ x : m, mappend x mempty = x                 -- 右单位律
  mappend_assoc  : ∀ x y z : m,
    mappend (mappend x y) z = mappend x (mappend y z)            -- 结合律

/-- 一个方便的中缀记号，和 Haskell 的 `<>` 一样。 -/
infixr:65 " <> " => Monoid.mappend
```

现在，谁要声明一个类型是 `Monoid`，就**必须**交出这三条定律的证明，否则编译不过。写一个“假装是幺半群”的实例，在 Lean 里是做不到的。

::: tip Lean 深入：`infixr`
`infixr:65 " <> " => Monoid.mappend` 声明了一个右结合（`r`）的中缀运算符，优先级 65（和 `+`、`++` 相同）。于是 `x <> y <> z` 读作 `x <> (y <> z)`。自定义记号在 Lean 里很常见，前导中的 `⟶`、`⊚` 也是这样声明的。
:::

Haskell 的类不像 C++ 的类那样有“侵入性”。定义一个新类型时，你不必预先声明它属于哪些类。你可以拖延，等很久以后再声明某个类型是某个类的实例。Lean 的类型类也是这样。作为例子，我们来声明 `String` 是一个幺半群，给出 `mempty` 和 `mappend` 的实现（Haskell 的标准 Prelude 实际上已经替你做了这件事）。先看不带定律的版本：

```lean
instance : Plain.Monoid String where
  mempty  := ""
  mappend := (· ++ ·)
```

这里我们复用了拼接运算符 `++`。（在 Haskell 里，`String` 就是字符的列表，所以那里用的是列表拼接；Lean 的 `String` 是一个单独的类型，但同样用 `++` 拼接。）

再看带定律的版本。三条定律在核心库里都已经有现成的定理，直接引用即可：

```lean
instance : Monoid String where
  mempty  := ""
  mappend := (· ++ ·)
  mempty_mappend _ := String.empty_append
  mappend_mempty _ := String.append_empty
  mappend_assoc _ _ _ := String.append_assoc
```

顺手把 $(\mathbb{N}, +, 0)$ 和列表也声明成幺半群：

```lean
instance : Monoid Nat where
  mempty := 0
  mappend := (· + ·)
  mempty_mappend := Nat.zero_add
  mappend_mempty := Nat.add_zero
  mappend_assoc := Nat.add_assoc

instance {α : Type} : Monoid (List α) where
  mempty := []
  mappend := (· ++ ·)
  mempty_mappend := List.nil_append
  mappend_mempty := List.append_nil
  mappend_assoc := List.append_assoc

#guard ("foo" <> "bar") == "foobar"
example : (2 : Nat) <> 3 = 5 := rfl
example : [1, 2] <> [3] = [1, 2, 3] := rfl
```

::: warning 易错点：一个类型，多个幺半群
$\mathbb{N}$ 在乘法下也是幺半群（单位元是 $1$）。可是类型类实例是按类型查找的，`Nat` 已经有了“加法”这个实例，再声明一个“乘法”实例就会打架。通常的办法是包一层新类型。Haskell 标准库里有 `Sum` 和 `Product` 两个包装类型，Rust 标准库里有 `std::iter::Sum` 和 `std::iter::Product` 两个 trait，都是为了这件事。在 Lean 里：

```lean
structure NatMul where
  n : Nat

instance : Monoid NatMul where
  mempty := ⟨1⟩
  mappend a b := ⟨a.n * b.n⟩
  mempty_mappend a := by simp      -- 1 * n = n
  mappend_mempty a := by simp      -- n * 1 = n
  mappend_assoc a b c := by simp [Nat.mul_assoc]
```

`simp` 是 Lean 的“化简器”：它用一大批已知的等式（比如 `Nat.one_mul`）反复改写目标，直到目标变成显然成立的样子。方括号里可以额外塞给它一些定理。
:::

关于语法再说几句。在 Haskell 里，任何中缀运算符加上括号，就变成一个普通的双参数函数。Lean 的对应写法是 `(· ++ ·)`：这里的 `·` 是一个“空位”，整个表达式表示“把两个空位依次填上参数”的函数。给定两个字符串，你可以把 `++` 写在它们中间来拼接：

```lean
#guard "Hello " ++ "world!" == "Hello world!"
```

也可以把它们作为两个参数，传给 `(· ++ ·)`，或者传给 `++` 背后真正的函数 `HAppend.hAppend`：

```lean
#guard (· ++ ·) "Hello " "world!" == "Hello world!"
#guard HAppend.hAppend "Hello " "world!" == "Hello world!"
```

注意，函数的参数之间既不用逗号分隔，也不用括号括起来。（对习惯了 `f(a, b)` 的 Rust 程序员来说，这大概是学 Lean 时最需要适应的一点——Haskell 程序员倒是会觉得宾至如归。）

`#guard` 是一条命令：它在编译时计算后面的布尔表达式，如果不是 `true` 就报错。所以书里每一行 `#guard` 都是一个被机器检查过的“输出”。

值得强调的是，我们可以表达**函数之间的相等**，例如：

```lean
example : (Monoid.mappend : String → String → String) = (· ++ ·) := rfl
```

从概念上说，这和“函数产出的值相等”是不同的：

```lean
example : ∀ s₁ s₂ : String, Monoid.mappend s₁ s₂ = s₁ ++ s₂ := fun _ _ => rfl
```

前者说的是范畴 **Hask**（如果忽略底（⊥）——即永不结束的计算——就是 **Set**）中两个**态射相等**。这样的等式不仅更简洁，而且常常可以推广到其它范畴。后者叫作**外延**相等（extensional equality），它陈述的是：对于任意两个输入字符串，`mappend` 和 `++` 的输出都相同。由于参数的值有时被称为**点**（point）（比如说“$f$ 在点 $x$ 处的值”），这种相等也叫**逐点相等**（point-wise equality）。不写出参数的函数等式，则称为**无点**（point-free）风格。（顺带一提，无点等式里经常出现函数复合，而复合的符号恰好是一个点 $\circ$，初学者可能会因此有点困惑。）

::: tip Lean 深入：`funext`——从逐点相等到函数相等
在 Lean 里，“逐点相等推出函数相等”是一条定理，叫 `funext`（function extensionality，函数外延性）：

```lean
example (f g : String → String → String) (h : ∀ s₁ s₂, f s₁ s₂ = g s₁ s₂) : f = g := by
  funext s₁ s₂     -- 把目标 f = g 变成 f s₁ s₂ = g s₁ s₂
  exact h s₁ s₂
```

`funext x` 这个 tactic 的作用是：要证两个函数相等，只需对任意的 `x` 证明它们在 `x` 处的值相等。本书会大量使用它。

另外，Lean 没有 Haskell 那种“每个类型里都藏着一个 ⊥”的问题：Lean 的函数都是**全函数**，必须对每个输入在有限时间内给出结果（否则要显式标注 `partial`）。所以 Lean 的类型和函数，是集合与函数的范畴 **Set** 的一个相当忠实的模型，上面这些等式不需要“忽略底”之类的附加说明。
:::

在 C++ 里，最接近“声明一个幺半群”的做法，是使用 C++20 的 concept 特性。对 Rust 程序员来说，对应物是 **trait**：

```rust
pub trait Monoid {
    fn empty() -> Self;
    fn append(self, other: Self) -> Self;
}
```

`empty` 是一个关联函数（没有 `self` 参数），对每个实现类型给出单位元；`append` 是二元运算。两者都没有默认实现：每个实现者都必须逐一提供。（原书的 C++ 版本里，为了达到同样的效果，需要用 `= delete` 显式删除通用的默认版本。）

在泛型代码里写 `M: Monoid` 这样的约束，编译器就会检查给定的类型 `M` 是否确实有合适的 `empty` 和 `append`——这就是 C++ concept 所做的事情。

要让某个类型“成为”幺半群，只需为它实现这个 trait：

```rust
pub trait Monoid {
    fn empty() -> Self;
    fn append(self, other: Self) -> Self;
}

impl Monoid for String {
    fn empty() -> Self {
        String::new()
    }
    fn append(self, other: Self) -> Self {
        self + &other
    }
}

/// 幺半群最典型的用途：把一串元素“折叠”成一个。
pub fn mconcat<M: Monoid>(xs: Vec<M>) -> M {
    xs.into_iter().fold(M::empty(), M::append)
}
```

::: tip Rust 视角：trait 也是“非侵入式”的，但……
和 Lean 的类型类一样，Rust 允许你在类型定义之后很久，再为它实现某个 trait——上面我们就为标准库的 `String` 实现了自己的 `Monoid`。Rust 的限制是**孤儿规则**（orphan rule）：trait 和类型至少有一个得是你自己 crate 里定义的。Lean 没有这条限制。

更重要的区别是：和 Haskell、C++ 一样，Rust 的 trait **无法表达定律**。`impl Monoid for String` 里就算把 `append` 写成 `other + &self`（把顺序弄反），编译器也照单全收——碰巧它仍然是幺半群；可如果写成“取较短的那个”，结合律虽然成立，`empty()` 却不再是单位元了，编译器同样不会发现。Lean 版的 `Monoid` 会直接拒绝这样的实例。
:::

Lean 版的 `mconcat` 长这样。有了定律，我们还能证明它的一条好性质：先拼接列表再折叠，等于分别折叠再用 `<>` 合并。（这条性质正是并行折叠的理论基础：把一个大列表切成几块，分头计算，最后合并。）

```lean
def mconcat {m : Type} [Monoid m] : List m → m
  | [] => Monoid.mempty
  | x :: xs => x <> mconcat xs

#guard mconcat ["a", "b", "c"] == "abc"
example : mconcat [1, 2, 3, 4] = 10 := rfl

theorem mconcat_append {m : Type} [Monoid m] (xs ys : List m) :
    mconcat (xs ++ ys) = mconcat xs <> mconcat ys := by
  induction xs with
  | nil => simp [mconcat, Monoid.mempty_mappend]              -- 用到左单位律
  | cons x xs ih => simp [mconcat, ih, Monoid.mappend_assoc]  -- 用到结合律
```

`induction xs with` 对列表做归纳：`nil` 分支证明空列表的情况，`cons` 分支在假设 `ih`（归纳假设：结论对 `xs` 成立）的前提下证明 `x :: xs` 的情况。

## 作为范畴的幺半群

上面是用集合中的元素来定义幺半群，这是“大家熟悉的”定义。但你知道，在范畴论里，我们尽量摆脱集合和元素，转而谈论对象和态射。所以我们稍稍换个视角，把二元运算的“作用”看作在集合里把东西“挪动”或“平移”。

比如，有一个“给每个自然数加 5”的操作。它把 0 映到 5，1 映到 6，2 映到 7，依此类推。这是定义在自然数集合上的一个函数。很好：我们有了一个函数和一个集合。一般地，对任意数 $n$，都有一个“加 $n$”的函数——$n$ 的“加法器”（adder）。

```lean
/-- n 的加法器：给每个自然数加上 n。 -/
def adder (n : Nat) : Nat → Nat := fun k => n + k

#guard (List.range 3).map (adder 5) == [5, 6, 7]
```

加法器怎么复合？“加 5”的函数和“加 7”的函数复合起来，就是“加 12”的函数。所以加法器的复合可以和加法的规则对应起来。这也很好：我们可以用函数复合来代替加法。

```lean
/-- 加法器的复合 = 加法。 -/
theorem adder_comp (m n : Nat) : adder m ∘ adder n = adder (m + n) := by
  funext k
  simp [adder, Function.comp, Nat.add_assoc]

example : adder 5 ∘ adder 7 = adder 12 := adder_comp 5 7
```

且慢，还有呢：单位元零也有一个加法器。加零不会挪动任何东西，所以它就是自然数集合上的恒等函数。

```lean
theorem adder_zero : adder 0 = id := by
  funext k
  simp [adder]
```

与其告诉你传统的加法规则，我完全可以告诉你加法器的复合规则，而不丢失任何信息。注意，加法器的复合满足结合律，因为函数的复合满足结合律；而且我们有零加法器，对应恒等函数。

机敏的读者也许已经注意到了：从整数到加法器的这个映射，来自对 `mappend` 类型签名的第二种理解，即把它看作 `m → (m → m)`。它告诉我们，`mappend` 把幺半群集合中的一个元素映射为一个作用在这个集合上的函数。

::: tip 补充：对任意幺半群都成立
加法器的故事对**任何**幺半群都成立。把 `mappend` 只喂一个参数，就得到“左乘 $x$”这个函数；它把 `<>` 变成 `∘`，把 `mempty` 变成 `id`。这两条恰好就是结合律和左单位律换了个说法：

```lean
/-- x 的“作用”：从左边乘上 x。对 (ℕ, +, 0) 来说，就是 adder。 -/
def act {m : Type} [Monoid m] (x : m) : m → m := Monoid.mappend x

theorem act_mappend {m : Type} [Monoid m] (x y : m) : act (x <> y) = act x ∘ act y := by
  funext z
  simp [act, Function.comp, Monoid.mappend_assoc]

theorem act_mempty {m : Type} [Monoid m] : act (Monoid.mempty : m) = id := by
  funext z
  simp [act, Monoid.mempty_mappend]
```

数学上，这叫作幺半群的 **Cayley 表示**：任何幺半群都可以看成“某个集合上的一些函数，在复合下构成的幺半群”。
:::

现在，我希望你忘掉自己在和自然数集合打交道，只把它想成**一个**对象，一团带着许多态射（也就是那些加法器）的东西。幺半群就是只有一个对象的范畴。事实上，“幺半群”的英文 monoid 来自希腊语 *mono*，意思是“单一”。每个幺半群都可以描述为一个只有单个对象的范畴，它的态射集合遵循适当的复合规则。

![幺半群作为单对象范畴](/img/1.3/monoid.jpg "幺半群就是只有一个对象的范畴：所有态射都从这个对象出发、回到这个对象，复合规则就是幺半群的运算。")

用 Lean 写出来，几乎就是把上面这段话照抄一遍。对象的类型只需要**恰好一个元素**；hom-集就是幺半群本身：

```lean
/-- 由幺半群 m 得到的单对象范畴的对象类型：一个字段也没有的结构体，恰好只有一个值。 -/
structure MonoidCat (m : Type) where

/-- 那个唯一的对象。 -/
def MonoidCat.pt {m : Type} : MonoidCat m := {}

instance monoidCategory (m : Type) [Monoid m] : Category.{0, 0} (MonoidCat m) where
  Hom _ _ := m                        -- 唯一的 hom-集就是 m 本身
  id _ := Monoid.mempty               -- 恒等态射 = 单位元
  comp g f := g <> f                  -- 复合 = 幺半群运算
  id_comp := Monoid.mempty_mappend    -- 范畴的单位律 = 幺半群的单位律
  comp_id := Monoid.mappend_mempty
  assoc f g h := (Monoid.mappend_assoc h g f).symm   -- 范畴的结合律 = 幺半群的结合律
```

范畴的三条定律，恰好就是幺半群的三条定律：一一对应，不多不少。来看看加法器在这个范畴里长什么样：

```lean
/-- 在 (ℕ, +, 0) 的单对象范畴里，“加 n”这条自环态射。 -/
def plus (n : Nat) : (MonoidCat.pt : MonoidCat Nat) ⟶ MonoidCat.pt := n

example : plus 5 ⊚ plus 7 = plus 12 := rfl                     -- 复合就是加法
example : 𝟙 (MonoidCat.pt : MonoidCat Nat) = plus 0 := rfl     -- 恒等就是加 0
```

::: tip Lean 深入：没有字段的结构体
`structure MonoidCat (m : Type) where` 后面什么也没写，这是一个**零字段**的结构体。它恰好有一个值 `{}`（也可以写作 `⟨⟩`），作用和 `Unit` 一样。我们不直接用 `Unit` 作对象，原因还是实例查找：把 `m` 写进对象的类型，Lean 才知道 `MonoidCat Nat` 和 `MonoidCat String` 是两个不同的范畴。对应的 Rust 写法是零大小类型 `struct MonoidCat<M>(PhantomData<M>);`。
:::

下面的交互组件把这件事画了出来：一个对象，若干条自环箭头。依次点两条箭头，看看它们的复合是哪一条；同一个复合也会在右边的“hom-集”里作为**点**亮起，在下面的复合表里作为一个**格子**亮起。

<div><Ch1_3MonoidCategory /></div>

字符串拼接是个有趣的例子，因为我们可以选择定义“右追加器”（right appender），也可以选择定义“左追加器”（left appender，或者叫“前置器”（prepender），如果你愿意这么叫的话）。这两种模型的复合表互为镜像。你很容易就能说服自己：在 "foo" 之后追加 "bar"，对应于先前置 "bar"、再前置 "foo"：

```lean
def appendR (s : String) : String → String := fun t => t ++ s   -- 在右边追加 s
def prepend (s : String) : String → String := fun t => s ++ t   -- 在左边前置 s

-- 先追加 "foo" 再追加 "bar"，等于追加 "foobar"
theorem appendR_comp : appendR "bar" ∘ appendR "foo" = appendR "foobar" := by
  funext t
  simp [appendR, Function.comp, String.append_assoc]

-- 先前置 "bar" 再前置 "foo"，同样得到 "foobar"
theorem prepend_comp : prepend "foo" ∘ prepend "bar" = prepend "foobar" := by
  funext t
  simp [prepend, Function.comp, ← String.append_assoc]
```

两个定理的右边都是 "foobar"，但左边复合的顺序正好相反：用追加器时，"foo" 先作用；用前置器时，"bar" 先作用。这就是“镜像”的意思。（`simp` 列表里的 `← String.append_assoc` 表示把结合律**从右往左**用。）

你可能会问：是不是每个范畴意义下的幺半群——单对象范畴——都确定了唯一一个“集合加二元运算”意义下的幺半群？答案是肯定的：我们总能从单对象范畴中提取出一个集合。这个集合就是态射的集合——在我们的例子中，就是那些加法器。换句话说，我们有范畴 $\mathcal{M}$ 中唯一对象 $m$ 的 hom-集 $\mathcal{M}(m, m)$。在这个集合上定义二元运算很容易：两个集合元素的幺半群乘积，就是对应态射的复合所对应的那个元素。如果你给我 $\mathcal{M}(m, m)$ 中对应于 $f$ 和 $g$ 的两个元素，它们的乘积就对应于复合 $f \circ g$。复合总是存在的，因为这些态射的源和目标是同一个对象。复合满足结合律，这是范畴的规则所保证的。恒等态射就是这个乘积的单位元。所以，我们总能从范畴幺半群恢复出集合幺半群。无论从哪个角度看，它们都是一回事。

在 Lean 里，这个“提取”甚至对**任意**范畴中的**任意**对象都成立（不一定只有一个对象）：从 $x$ 到 $x$ 的态射，在复合下总是构成一个幺半群，叫作 $x$ 的**自态射幺半群**（endomorphism monoid）：

```lean
/-- 任意范畴中，对象 x 的 hom-集 x ⟶ x 在复合下构成幺半群。
（`Category.{u, 0}`：我们的 `Monoid` 只接受 `Type`，所以要求 hom-集在 `Type 0` 里。） -/
@[reducible] def endMonoid {C : Type u} [Category.{u, 0} C] (x : C) : Monoid (x ⟶ x) where
  mempty := 𝟙 x
  mappend g f := g ⊚ f
  mempty_mappend := Category.id_comp
  mappend_mempty := Category.comp_id
  mappend_assoc f g h := (Category.assoc h g f).symm

-- 来回走一圈：幺半群 → 单对象范畴 → 自态射幺半群，得到的就是原来的运算和单位元
example {m : Type} [Monoid m] :
    (endMonoid (MonoidCat.pt : MonoidCat m)).mappend = (Monoid.mappend : m → m → m) := rfl
example {m : Type} [Monoid m] :
    (endMonoid (MonoidCat.pt : MonoidCat m)).mempty = (Monoid.mempty : m) := rfl

-- 在类型的范畴里，Nat ⟶ Nat 就是 Nat → Nat，自态射幺半群就是函数复合
example : (endMonoid Nat).mappend (fun n => n + 1) (fun n => n * 2) 5 = 11 := rfl
```

两个 `rfl` 说明，来回走一圈之后，得到的运算和单位元**定义上**就是原来的那两个——“它们是一回事”在 Lean 里精确到了字面意义。

![幺半群的 hom-集](/img/1.3/monoidhomset.jpg "幺半群的 hom-集：既可以看作态射，也可以看作集合中的点。")

数学家们还有一个小小的毛病可挑：态射不一定构成集合。在范畴的世界里，有些东西比集合还大。任意两个对象之间的态射都构成集合的范畴，称为**局部小**（locally small）的。正如我承诺过的，我基本会忽略这类细节，但我觉得有必要提一句，以备查考。

::: tip Lean 深入：宇宙与“局部小”
Lean 用**宇宙**（universe）来处理“比集合还大”的问题。`Type 0`（就是 `Type`）里装着 `Nat`、`String` 这些普通类型；而 `Type 0` 本身也是一个类型，它住在 `Type 1` 里；`Type 1` 住在 `Type 2` 里……这样层层往上，就避免了“所有类型的类型包含它自己”这种悖论（这和集合论里“所有集合的集合”不是集合是同一个道理）。

我们的 `Category.{u, v} (Obj : Type u)` 有两个宇宙参数：对象住在 `Type u`，每个 hom-集 `Hom a b` 住在 `Type v`。这正是“局部小”的 Lean 版本——不管对象有多少，**两个对象之间的态射**总是装在一个固定的宇宙 `Type v` 里。

看看前导里的 `typeCategory : Category (Type u)`：对象是 `Type u` 里的所有类型，它们合起来组成 `Type u`，这本身住在 `Type (u+1)` 里——“太大了”；可是 hom-集 `a → b` 仍然在 `Type u` 里。所以类型的范畴是一个**大**的、但**局部小**的范畴，和数学家眼中的 **Set** 完全一样。
:::

范畴论中许多有趣的现象，都根源于这样一个事实：hom-集中的元素既可以看作态射——遵循复合规则；也可以看作集合中的点。在这里，$\mathcal{M}$ 中态射的复合，就变成了集合 $\mathcal{M}(m, m)$ 中的幺半群乘积。

## 挑战

1. 由下面的图生成自由范畴：
   1. 一个节点、没有边的图。
   2. 一个节点、一条（有向）边的图（提示：这条边可以和自己复合）。
   3. 两个节点、它们之间有一条箭头的图。
   4. 一个节点、26 条箭头的图，箭头分别标上字母表中的字母：a、b、c……z。
2. 下面是哪种序？
   1. 一个由集合组成的集合，配上包含关系：如果 $A$ 的每个元素也都是 $B$ 的元素，就说 $A$ 包含于 $B$。
   2. C++ 类型，配上这样的子类型关系：如果指向 `T1` 的指针可以传给一个期望指向 `T2` 的指针的函数而不引发编译错误，就说 `T1` 是 `T2` 的子类型。（Rust 版本：生命周期之间的“活得更久”关系 `'a: 'b`。如果 `'a: 'b`，那么 `&'a T` 可以用在需要 `&'b T` 的地方。）
3. `Bool` 是由 `true` 和 `false` 两个值组成的集合。证明：它在 `&&`（与）和 `||`（或）这两个运算下分别构成一个（集合意义下的）幺半群。
4. 把带“与”运算的 `Bool` 幺半群表示成一个范畴：列出它的态射以及它们的复合规则。
5. 把模 3 加法表示成一个幺半群范畴。

::: details 参考答案 1：自由范畴
**(1) 一个节点、没有边。** 唯一的态射是恒等态射（长度为 0 的路径）。这个范畴叫**平凡范畴**（只有一个对象和它的恒等态射），作为幺半群，它就是只有一个元素的幺半群。

```lean
inductive NoEdge : Unit → Unit → Type     -- 没有构造子：没有边

theorem c1a (p : Path NoEdge () ()) : p = .nil () := by
  cases p with
  | nil => rfl
  | cons e _ => cases e                   -- 不存在边 e，这一支自动消失
```

**(2) 一个节点、一条边 $e$。** 态射是 $\mathrm{id}, e, e \circ e, e \circ e \circ e, \dots$，和自然数一一对应（按长度），复合对应加法。所以这个自由范畴就是幺半群 $(\mathbb{N}, +, 0)$ 的单对象范畴。

```lean
inductive Loop : Unit → Unit → Type
  | e : Loop () ()

/-- 把 e 连续走 n 次。 -/
def loopN : Nat → Path Loop () ()
  | 0 => .nil ()
  | n + 1 => .cons .e (loopN n)

-- 长度 ∘ loopN = id，loopN ∘ 长度 = id：路径与自然数一一对应
theorem loopN_length : ∀ n, (loopN n).length = n
  | 0 => rfl
  | n + 1 => by simp [loopN, Path.length, loopN_length n]

theorem length_loopN : ∀ p : Path Loop () (), loopN p.length = p
  | .nil _ => rfl
  | .cons .e p => by simp [Path.length, loopN, length_loopN p]

-- 复合（接路径）对应加法（这条对任何图都成立）
theorem length_append {V : Type} {E : V → V → Type} :
    ∀ {a b c : V} (p : Path E a b) (q : Path E b c),
    (p.append q).length = p.length + q.length
  | _, _, _, .nil _, q => by simp [Path.append, Path.length]
  | _, _, _, .cons _ p, q => by
      simp [Path.append, Path.length, length_append p q]
      omega
```

（`omega` 是一个能自动证明线性整数算术等式与不等式的 tactic，这里它负责 `p + q + 1 = p + 1 + q` 这类整理工作。）

**(3) 两个节点 $A$、$B$，一条箭头 $f : A \to B$。** 态射只有三条：$\mathrm{id}_A$、$\mathrm{id}_B$、$f$。没有可以复合出新东西的箭头对（除了和恒等复合）。从 $B$ 到 $A$ 什么也没有。

```diagram
A: (0, 0)
B: (2, 0)
f: A -> B "f"
idA: A -> A "\mathrm{id}_A" loop=left color=gray
idB: B -> B "\mathrm{id}_B" loop=right color=gray
caption: 两个对象、三条态射。它也是一个偏序：A ≤ B
```

```lean
inductive Two | A | B
inductive Arr : Two → Two → Type
  | f : Arr .A .B

theorem c1c_BA (p : Path Arr .B .A) : False := by
  cases p with
  | cons e _ => cases e          -- 没有从 B 出发的边

theorem c1c_AA (p : Path Arr .A .A) : p = Path.nil Two.A := by
  cases p with
  | nil => rfl
  | cons e p => cases e; exact (c1c_BA p).elim   -- 走了 f 就回不来了

theorem c1c_BB (p : Path Arr .B .B) : p = Path.nil Two.B := by
  cases p with
  | nil => rfl
  | cons e _ => cases e

theorem c1c_AB (p : Path Arr .A .B) : p = Path.cons Arr.f (Path.nil Two.B) := by
  cases p with
  | cons e p => cases e; rw [c1c_BB p]
```

四个定理合起来说明：$\mathcal{C}(A, A) = \{\mathrm{id}_A\}$，$\mathcal{C}(B, B) = \{\mathrm{id}_B\}$，$\mathcal{C}(A, B) = \{f\}$，$\mathcal{C}(B, A) = \varnothing$。

**(4) 一个节点、26 条字母边。** 态射是所有由字母组成的有限序列——也就是所有“单词”（包括空单词，即恒等态射）；复合就是把单词拼接起来。这个范畴就是字符串幺半群的单对象范畴。它有个专门的名字：26 个字母生成的**自由幺半群**（free monoid），我们会在 [2.3 自由幺半群](/part2/03-free-monoids) 里详细讨论。

```lean
inductive Letters : Unit → Unit → Type
  | letter (c : Fin 26) : Letters () ()     -- Fin 26 = {0, 1, …, 25}，代表 a … z

def Letters.char : Letters a b → Fin 26
  | .letter c => c

def word : Path Letters () () → List (Fin 26)
  | .nil _ => []
  | .cons e p => e.char :: word p

def unword : List (Fin 26) → Path Letters () ()
  | [] => .nil ()
  | c :: cs => .cons (.letter c) (unword cs)

-- 路径与单词一一对应……
theorem word_unword : ∀ w, word (unword w) = w
  | [] => by simp [unword, word]
  | c :: cs => by simp [unword, word, Letters.char, word_unword cs]

theorem unword_word : ∀ p, unword (word p) = p
  | .nil _ => by simp [unword, word]
  | .cons (.letter c) p => by simp [unword, word, Letters.char, unword_word p]

-- ……而且接路径对应拼接单词
theorem word_append : ∀ (p q : Path Letters () ()), word (p.append q) = word p ++ word q
  | .nil _, q => by simp [Path.append, word]
  | .cons e p, q => by simp [Path.append, word, word_append p q]
```
:::

::: details 参考答案 2：是哪种序
**(1) 集合的包含关系**是**偏序**，但一般不是全序。自反：$A \subseteq A$；传递：$A \subseteq B$、$B \subseteq C$ ⇒ $A \subseteq C$；反对称：$A \subseteq B$ 且 $B \subseteq A$ ⇒ $A = B$（两个集合元素完全相同就相等，这是集合的“外延性”）。但 $\{0\}$ 和 $\{1\}$ 互不包含，所以不是全序。

在 Lean 里，可以把“$\alpha$ 的子集”表示成谓词 `α → Prop`（`A x` 表示 “$x \in A$”）：

```lean
def Subset {α : Type} (A B : α → Prop) : Prop := ∀ x, A x → B x

theorem subset_refl {α : Type} (A : α → Prop) : Subset A A := fun _ h => h

theorem subset_trans {α : Type} {A B C : α → Prop}
    (h₁ : Subset A B) (h₂ : Subset B C) : Subset A C :=
  fun x hA => h₂ x (h₁ x hA)

theorem subset_antisymm {α : Type} {A B : α → Prop}
    (h₁ : Subset A B) (h₂ : Subset B A) : A = B := by
  funext x                    -- 两个谓词相等 ⇐ 对每个 x 相等
  apply propext               -- 两个命题相等 ⇐ 它们互相蕴含
  exact ⟨h₁ x, h₂ x⟩

theorem subset_not_total : ¬ ∀ A B : Nat → Prop, Subset A B ∨ Subset B A := by
  intro h
  cases h (· = 0) (· = 1) with             -- 取 A = {0}，B = {1}
  | inl h01 => have := h01 0 rfl; simp at this   -- 0 ∈ {1}？矛盾
  | inr h10 => have := h10 1 rfl; simp at this   -- 1 ∈ {0}？矛盾
```

`propext`（命题外延性）是 Lean 的一条公理：两个互相蕴含的命题相等。

**(2) C++ 指针的子类型关系**大致是一个**偏序**：每个类型都是自己的子类型（自反）；派生类指针可以隐式转成基类指针，基类指针又可以转成它的基类指针（通常传递）；继承关系不可能成环，所以两个类型互为子类型时必然是同一个类型（反对称）。它显然不是全序：两个毫不相干的类，谁也不是谁的子类型。不过有个陷阱：在“菱形”多重继承中，如果 `D` 经由两条路径继承了同一个 `B`（非虚继承），`D*` 可以转成两个中间类的指针，中间类的指针也都能转成 `B*`，但 `D*` 直接转成 `B*` 却会因为二义性而编译失败——这时连传递性都不成立，严格说来就连预序都算不上了。

**Rust 版本**：生命周期的“活得更久”关系 `'a: 'b` 是自反的（`'a: 'a`），也是传递的（`'a: 'b` 且 `'b: 'c` ⇒ `'a: 'c`），所以至少是一个预序；把生命周期看作程序中的一段区域，它就是区域之间的包含关系，因此是偏序，但不是全序——两个不重叠的作用域谁也不比谁活得更久。
:::

::: details 参考答案 3：Bool 的两个幺半群
`&&` 的单位元是 `true`，`||` 的单位元是 `false`。所有定律都只涉及有限多种情况，`decide` 可以逐一检查：

```lean
example : ∀ a b c : Bool, ((a && b) && c) = (a && (b && c)) := by decide
example : ∀ a : Bool, (true && a) = a ∧ (a && true) = a := by decide
example : ∀ a b c : Bool, ((a || b) || c) = (a || (b || c)) := by decide
example : ∀ a : Bool, (false || a) = a ∧ (a || false) = a := by decide
```

因为一个类型只能有一个 `Monoid` 实例，我们用两个包装类型（和 Haskell 标准库 `Data.Monoid` 里的 `All`、`Any` 同名）：

```lean
structure All where
  get : Bool

structure Any where
  get : Bool

instance : Monoid All where
  mempty := ⟨true⟩
  mappend a b := ⟨a.get && b.get⟩
  mempty_mappend a := by cases a; rfl
  mappend_mempty a := by cases a; simp
  mappend_assoc a b c := by cases a; cases b; cases c; simp [Bool.and_assoc]

instance : Monoid Any where
  mempty := ⟨false⟩
  mappend a b := ⟨a.get || b.get⟩
  mempty_mappend a := by cases a; rfl
  mappend_mempty a := by cases a; simp
  mappend_assoc a b c := by cases a; cases b; cases c; simp [Bool.or_assoc]
```
:::

::: details 参考答案 4：“与”幺半群作为范畴
只有一个对象；有两条态射，分别对应 `true` 和 `false`。把它们看作“作用”（`fun x => b && x`）：`true` 对应“什么也不做”，也就是恒等态射；`false` 对应“不管输入是什么都变成 `false`”的常函数。复合表（行是 $g$、列是 $f$，格子里是 $g \circ f$）：

| $g \circ f$ | $f = T$ | $f = F$ |
|---|---|---|
| $g = T$ | $T$ | $F$ |
| $g = F$ | $F$ | $F$ |

$F$ 和谁复合都得 $F$：一旦“变成 false”，就再也变不回去了。

```lean
def T : (MonoidCat.pt : MonoidCat All) ⟶ MonoidCat.pt := (⟨true⟩ : All)
def F : (MonoidCat.pt : MonoidCat All) ⟶ MonoidCat.pt := (⟨false⟩ : All)

example : 𝟙 _ = T := rfl                                   -- T 就是恒等态射
example : T ⊚ T = T ∧ T ⊚ F = F ∧ F ⊚ T = F ∧ F ⊚ F = F :=  -- 复合表
  ⟨rfl, rfl, rfl, rfl⟩

/-- 除了 T 和 F，再没有别的态射。 -/
theorem allHoms (h : (MonoidCat.pt : MonoidCat All) ⟶ MonoidCat.pt) : h = T ∨ h = F := by
  rcases h with ⟨_ | _⟩     -- 拆开包装，再对里面的 Bool 分 false / true 两种情况
  · exact Or.inr rfl
  · exact Or.inl rfl
```

在上面的交互组件里选“Bool 与”，就能看到这个范畴和它的复合表。
:::

::: details 参考答案 5：模 3 加法
一个对象，三条态射 $0, 1, 2$（分别是“加 0”“加 1”“加 2”，都按模 3 计算）。$0$ 是恒等态射。复合表：

| $g \circ f$ | $f = 0$ | $f = 1$ | $f = 2$ |
|---|---|---|---|
| $g = 0$ | $0$ | $1$ | $2$ |
| $g = 1$ | $1$ | $2$ | $0$ |
| $g = 2$ | $2$ | $0$ | $1$ |

可以看到：$1 \circ 1 = 2$，$1 \circ 2 = 0 = \mathrm{id}$，所以 $1$ 和 $2$ 互为逆态射——每条态射都可逆的单对象范畴，叫作**群**。这个表关于对角线对称，说明这个幺半群还满足交换律。

```diagram
x: (0, 0) "\bullet"
z: x -> x "0 = \mathrm{id}" loop=up color=gray
o: x -> x "1" loop=right
t: x -> x "2" loop=left
caption: 模 3 加法作为单对象范畴：三条自环态射
```

Lean 核心库的 `Fin 3` 就是 $\{0, 1, 2\}$，它的 `+` 正好按模 3 计算。所有定律都可以 `decide`：

```lean
instance : Monoid (Fin 3) where
  mempty := 0
  mappend := (· + ·)
  mempty_mappend := by decide
  mappend_mempty := by decide
  mappend_assoc := by decide

def r (k : Fin 3) : (MonoidCat.pt : MonoidCat (Fin 3)) ⟶ MonoidCat.pt := k

example : r 1 ⊚ r 1 = r 2 := rfl
example : r 1 ⊚ r 2 = 𝟙 _ := rfl     -- 1 和 2 互逆
example : r 2 ⊚ r 2 = r 1 := rfl

/-- 复合可交换：复合表关于对角线对称。 -/
theorem mod3_comm : ∀ f g : Fin 3, r g ⊚ r f = r f ⊚ r g := by
  intro f g
  show g + f = f + g      -- 把态射的复合展开成 Fin 3 上的加法
  revert f g
  decide                  -- 3 × 3 = 9 种情况逐一检查
```

在上面的交互组件里选“模 3 加法”，可以亲手验证这张表。
:::

## 本章小结

- **空范畴**没有对象也没有态射，三条定律“空洞地”成立；在 Lean 里用 `Empty` 和 `nomatch` 就能造出来。
- 任何有向图都能**自由地**生成一个范畴：态射是图中的路径，复合是接路径，恒等是空路径。在 Lean 里，路径是一个由起点、终点索引的归纳类型 `Path E a b`，“首尾相接”写在类型里。
- **预序**（自反 + 传递）就是**瘦范畴**：任意两个对象之间至多一条态射。**偏序**再加反对称，不允许环；**全序**再要求任意两个元素可比。排序算法需要全序（准确地说，需要传递 + 完全）。
- 在 Lean 里，`a ≤ b` 是 `Prop`，而 hom-集必须是 `Type`，所以用 `PLift (a ≤ b)` 包装。**证明无关性**让瘦范畴的三条定律和“至多一条态射”都几乎免费成立。
- **hom-集** $\mathcal{C}(a, b)$ 是从 $a$ 到 $b$ 的所有态射，在 Lean 里就是类型 `a ⟶ b`。
- **幺半群**是带有一个满足结合律的二元运算和单位元的集合。Haskell、C++、Rust 都无法表达它的定律，Lean 可以把定律写进类型类，不满足定律的实例根本编译不过。
- 函数相等有“无点”和“逐点（外延）”两种表达方式，Lean 的 `funext` 把后者变成前者。
- **幺半群就是只有一个对象的范畴**：元素是自环态射（例如“加法器”），运算是复合，单位元是恒等态射；范畴定律和幺半群定律一一对应。反过来，任何对象的自态射 $x \to x$ 都构成幺半群。
- hom-集的元素既是**态射**（可以复合），又是集合里的**点**（可以做乘法）：这个双重身份贯穿整个范畴论。
- 态射不一定构成集合；hom-集都是集合的范畴叫**局部小**的。Lean 用宇宙层级 `Category.{u, v}` 精确地表达了这一点。
