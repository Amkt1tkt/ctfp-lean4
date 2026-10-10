# 1.10 自然变换

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

/-- 类型与函数构成的范畴 **Type**。 -/
instance typeCategory : Category (Type u) where
  Hom a b := a → b
  id _ := fun x => x
  comp g f := fun x => g (f x)

/-- 范畴之间的函子。 -/
structure CFunctor (C : Type u₁) [Category.{u₁, v₁} C] (D : Type u₂) [Category.{u₂, v₂} D] where
  obj : C → D
  map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id : ∀ (a : C), map (𝟙 a) = 𝟙 (obj a)
  map_comp : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c), map (g ⊚ f) = map g ⊚ map f

end CTFP

open CTFP
```

我们已经谈过函子：它是范畴之间保持结构的映射。

函子把一个范畴“嵌入”到另一个范畴里。它可以把好几样东西压成一样，但绝不会扯断原有的连接。
一种理解方式是：借助函子，我们在一个范畴内部**建模**另一个范畴。源范畴充当模型、充当蓝图，
描述的是目标范畴中的某一块结构。

![函子把源范畴嵌入目标范畴](/img/1.10/1_functors.jpg "函子 F 与 G 把同一张“蓝图”（范畴 C）以两种方式画进了范畴 D。")

把一个范畴嵌入另一个范畴的方式可能有很多种。有时它们彼此等价，有时又天差地别。
有的嵌入把整个源范畴压成一个对象；有的则把每个对象送到不同的对象、每个态射送到不同的态射。
同一张蓝图可以有许多种不同的实现。**自然变换**（natural transformation）帮助我们比较这些实现。
它是函子之间的映射——一种保持函子“本性”的特殊映射。

考虑范畴 $\mathcal{C}$ 与 $\mathcal{D}$ 之间的两个函子 $F$ 和 $G$。如果你只盯着 $\mathcal{C}$ 中的一个对象 $a$，
它会被映到两个对象：$F a$ 和 $G a$。因此，一个“函子之间的映射”应当把 $F a$ 映到 $G a$。

![自然变换的分量](/img/1.10/2_natcomp.jpg "对象 a 在两个函子下的像 F a 与 G a，由一个态射 α_a 连接起来。")

注意，$F a$ 和 $G a$ 是同一个范畴 $\mathcal{D}$ 中的对象。同一范畴中对象之间的映射，不应当违背这个范畴的“纹理”。
我们不想在对象之间人为地凭空牵线。所以，使用**已有的**连接——也就是态射——是再*自然*不过的事了。
自然变换就是对态射的一种挑选：对每个对象 $a$，它挑出一个从 $F a$ 到 $G a$ 的态射。
如果把这个自然变换叫作 $\alpha$，那么这个态射就称为 $\alpha$ 在 $a$ 处的**分量**（component），记作 $\alpha_a$：

$$\alpha_a : F a \to G a$$

请记住，$a$ 是 $\mathcal{C}$ 中的对象，而 $\alpha_a$ 是 $\mathcal{D}$ 中的态射。

如果对某个 $a$，$\mathcal{D}$ 中根本不存在从 $F a$ 到 $G a$ 的态射，那么 $F$ 与 $G$ 之间就不可能有自然变换。

当然，这只讲了一半的故事，因为函子不仅映射对象，还映射态射。那么，自然变换拿这些态射的映射怎么办呢？
事实证明，态射的映射是固定的——在 $F$ 与 $G$ 之间的任何自然变换下，$F f$ 都必须被变换成 $G f$。
更重要的是，两个函子对态射的映射会极大地**限制**我们定义（与之相容的）自然变换时的选择余地。
考虑 $\mathcal{C}$ 中两个对象 $a$ 与 $b$ 之间的态射 $f$。它被映到 $\mathcal{D}$ 中的两个态射 $F f$ 和 $G f$：

$$F f : F a \to F b \qquad G f : G a \to G b$$

自然变换 $\alpha$ 又提供了两个态射，把 $\mathcal{D}$ 中的这幅图补完整：

$$\alpha_a : F a \to G a \qquad \alpha_b : F b \to G b$$

![自然性](/img/1.10/3_naturality.jpg "C 中的一个态射 f，在 D 中撑起了一个由 F f、G f、α_a、α_b 围成的方块。")

现在，从 $F a$ 到 $G b$ 有了两条路。为了保证它们相等，我们必须施加一条对任意 $f$ 都成立的**自然性条件**（naturality condition）：

$$G f \circ \alpha_a = \alpha_b \circ F f$$

下面就是这个**自然性方块**（naturality square）。点击按钮，看光点分别沿两条路径从 $F a$ 走到 $G b$——
“自然”的意思，就是无论走哪条路，到达的都是同一个态射。

```diagram
Fa: (0, 0) "F a"
Ga: (2.2, 0) "G a"
Fb: (0, 1.6) "F b"
Gb: (2.2, 1.6) "G b"
aa: Fa -> Ga "\alpha_a"
ab: Fb -> Gb "\alpha_b" side=right
Ff: Fa -> Fb "F f" side=right
Gf: Ga -> Gb "G f"
path "先 α_a，再 G f": aa Gf
path "先 F f，再 α_b": Ff ab color=green
caption: 自然性方块：对 C 中的每个 f : a → b，两条路径都必须相等。
```

::: info 数学小课堂：什么叫“图交换”
数学家说一幅图**交换**（commute），意思是：图中从同一个起点到同一个终点的任意两条路径，复合出来的态射都相等。
上面的方块交换，说的就是等式 $G f \circ \alpha_a = \alpha_b \circ F f$。

用编程的话来说：你手里有一个 `F a` 类型的值，想得到一个 `G b` 类型的值。可以先用 $\alpha_a$ 换容器、再用 $G f$ 改内容；
也可以先用 $F f$ 改内容、再用 $\alpha_b$ 换容器。“方块交换”就是保证这两种写法的程序**行为完全相同**，
所以你可以放心地用其中一种替换另一种——这正是重构与编译器优化所依赖的东西。
:::

自然性条件是一条相当严苛的要求。例如，如果态射 $F f$ 是可逆的，那么自然性就能用 $\alpha_a$ 把 $\alpha_b$ 确定下来。
它沿着 $f$ 把 $\alpha_a$ **运送**（transport）过去：

$$\alpha_b = (G f) \circ \alpha_a \circ (F f)^{-1}$$

![运送](/img/1.10/4_transport.jpg "若 F f 可逆，α_b 就被 α_a 唯一确定：先倒着走 (F f)⁻¹，再走 α_a，最后走 G f。")

```diagram
Fa: (0, 0) "F a"
Ga: (2.2, 0) "G a"
Fb: (0, 1.6) "F b"
Gb: (2.2, 1.6) "G b"
aa: Fa -> Ga "\alpha_a"
ab: Fb -> Gb "\alpha_b" side=right
Fi: Fb -> Fa "(F f)^{-1}"
Gf: Ga -> Gb "G f"
path "直接走 α_b": ab color=green
path "(F f)⁻¹，再 α_a，再 G f": Fi aa Gf
caption: 运送：可逆的 F f 让 α_b 别无选择。
```

::: info 数学小课堂：可逆态射
态射 $h : x \to y$ 称为**可逆的**，如果存在反方向的态射 $h^{-1} : y \to x$，使得 $h^{-1} \circ h = \mathrm{id}_x$ 且 $h \circ h^{-1} = \mathrm{id}_y$。
在类型与函数的范畴里，可逆函数就是**双射**：例如 `Bool` 上的 `not`，它的逆就是它自己。
上面的“运送”公式只用到了一半条件 $F f \circ (F f)^{-1} = \mathrm{id}$，下面的 Lean 证明会让你看清这一点。
:::

如果两个对象之间有不止一个可逆态射，那么所有这些“运送”的结果都必须一致。一般来说，态射并不可逆；
但你已经能看出，两个函子之间存在自然变换这件事远非理所当然。所以，由自然变换联系起来的函子是稀少还是丰富，
能告诉你很多关于这些函子所连接的范畴的结构信息。等我们讲到极限和米田引理时，会看到这方面的例子。

从分量的角度看自然变换，可以说它把**对象映到态射**。而由于自然性条件，也可以说它把**态射映到交换方块**——
$\mathcal{C}$ 中的每个态射，都对应 $\mathcal{D}$ 中的一个交换的自然性方块。

![自然性方块的全景](/img/1.10/naturality.jpg "C 中的每个态射 f 都在 D 中对应一个交换方块。")

自然变换的这个性质，在许多范畴论构造中都非常好用，因为这些构造里往往包含交换图。
只要明智地挑选函子，很多交换性条件都可以改写成自然性条件。等讲到极限、余极限和伴随时，我们会看到例子。

最后，自然变换可以用来定义**函子之间的同构**。说两个函子**自然同构**，几乎就等于说它们是同一个函子。
**自然同构**（natural isomorphism）定义为所有分量都是同构（可逆态射）的自然变换。

## 补充：在 Lean 中写下自然变换

原书只能用文字和图来描述自然变换；而在 Lean 里，我们可以把“自然性条件”**写进类型**。
下面就是全书公共前导 `Prelude.lean` 中的定义（本章开头的隐藏代码块里已经引入了 [1.7 函子](/part1/07-functors) 中的
`Category` 与 `CFunctor`）：

```lean
namespace CTFP

/-- 自然变换 `α : F ⟹ G`：每个对象一个分量，满足自然性方块交换。 -/
structure NatTrans {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    (F G : CFunctor C D) where
  app : (a : C) → (F.obj a ⟶ G.obj a)
  naturality : ∀ {a b : C} (f : a ⟶ b), G.map f ⊚ app a = app b ⊚ F.map f

infixr:50 " ⟹ " => NatTrans

end CTFP
```

逐行来看：

- `structure NatTrans ... where`：自然变换是一个**结构体**（就像 Rust 的 `struct`），由两个字段组成。
- `{C : Type u₁} [Category.{u₁, v₁} C]`：花括号是**隐式参数**——Lean 会根据上下文自己推断出 `C` 是谁；
  方括号是**实例参数**，相当于 Rust 的 trait 约束 `C: Category`。`.{u₁, v₁}` 是宇宙参数：
  对象住在 `Type u₁` 里，态射住在 `Type v₁` 里。之所以需要宇宙变量，是因为后面我们要让“函子本身”也当对象，
  它们比普通类型“高一层”。对于本章的绝大部分内容，你可以把它们都当成 `Type`。
- `(F G : CFunctor C D)`：显式参数，两个从 $\mathcal{C}$ 到 $\mathcal{D}$ 的函子。注意：自然变换的**类型**依赖于 `F` 和 `G` 这两个**值**——
  这就是依值类型。Rust 里做不到“类型里写着两个具体的函子”。
- `app : (a : C) → (F.obj a ⟶ G.obj a)`：分量。这是一个**依值函数**：返回值的类型 `F.obj a ⟶ G.obj a` 随输入 `a` 变化。
  `app a` 就是数学里的 $\alpha_a$。
- `naturality : ∀ {a b : C} (f : a ⟶ b), G.map f ⊚ app a = app b ⊚ F.map f`：自然性条件，一字不差地照抄了
  $G f \circ \alpha_a = \alpha_b \circ F f$。它是一个**命题**，字段的值是它的**证明**。
  所以，想构造一个 `NatTrans`，光给出分量不够，还必须交出一份“方块交换”的证明——编译器会替你把关。
- `infixr:50 " ⟹ " => NatTrans`：引入记号，`F ⟹ G` 就是 `NatTrans F G`（输入法：`\==>`）。

::: tip Lean 深入：把证明当字段
在 Rust 里，一个 `struct` 的字段只能是数据；“这个值满足某条定律”最多写进文档注释，或者靠测试抽查。
在 Lean 里，命题也是类型，证明是这个类型的值，所以“定律”可以直接当字段。
`Category` 结构里的 `id_comp`、`assoc`，`CFunctor` 里的 `map_id`、`map_comp`，以及这里的 `naturality` 都是如此。
一个类型为 `F ⟹ G` 的值存在，本身就**保证了**自然性成立。
:::

借助 `NatTrans`，“运送”公式也成了一条可以证明的定理：

```lean
namespace CTFP

/-- 若 `h` 是 `F.map f` 的右逆，则 `α_b` 由 `α_a` 唯一确定：`α_b = G f ∘ α_a ∘ h`。 -/
theorem NatTrans.transport {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    {F G : CFunctor C D} (α : F ⟹ G) {a b : C} (f : a ⟶ b)
    (h : F.obj b ⟶ F.obj a) (inv : F.map f ⊚ h = 𝟙 (F.obj b)) :
    α.app b = G.map f ⊚ α.app a ⊚ h := by
  calc α.app b
      = α.app b ⊚ 𝟙 (F.obj b)          := (Category.comp_id _).symm
    _ = α.app b ⊚ (F.map f ⊚ h)        := by rw [inv]
    _ = (α.app b ⊚ F.map f) ⊚ h        := by rw [Category.assoc]
    _ = (G.map f ⊚ α.app a) ⊚ h        := by rw [α.naturality]
    _ = G.map f ⊚ α.app a ⊚ h          := by rw [Category.assoc]

end CTFP
```

::: tip Lean 深入：`calc` 链式推导
`calc` 让你像在黑板上一样写一串等式：每一行 `_ = 新表达式 := 理由`，下划线代表上一行的右边。
`rw [h]`（rewrite）用等式 `h` 把目标中的左边改写成右边；`rw [← h]` 则反方向改写。
`(Category.comp_id _).symm` 直接给出证明项：`comp_id` 说 $x \circ \mathrm{id} = x$，`.symm` 把等式左右对调。
`⊚` 是右结合的，所以最后一行的 `G.map f ⊚ α.app a ⊚ h` 就是 `G.map f ⊚ (α.app a ⊚ h)`。
:::

自然同构也可以照着定义写出来：一对方向相反的自然变换，每个分量都互为逆。

```lean
namespace CTFP

/-- 自然同构：一对互逆的自然变换。 -/
structure NatIso {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    (F G : CFunctor C D) where
  hom : F ⟹ G
  inv : G ⟹ F
  hom_inv : ∀ a, inv.app a ⊚ hom.app a = 𝟙 (F.obj a)
  inv_hom : ∀ a, hom.app a ⊚ inv.app a = 𝟙 (G.obj a)

end CTFP
```

## 多态函数

我们谈过函子（更具体地说，自函子）在编程中的角色。它们对应于把类型映到类型的**类型构造器**，
同时也把函数映到函数，这个映射由高阶函数 `fmap` 实现——在 Lean 里叫 `Functor.map`，中缀写作 `<$>`；
在 Rust 里则是 `Option::map`、`Iterator::map` 之类的方法。

要构造一个自然变换，我们从一个对象——这里是一个类型 `a`——出发。一个函子 `F` 把它映成类型 `F a`，
另一个函子 `G` 把它映成 `G a`。自然变换 `alpha` 在 `a` 处的分量，是一个从 `F a` 到 `G a` 的函数。
用伪代码写就是：

```lean no-check
alpha_a : F a → G a
```

自然变换是一个对**所有**类型 `a` 都有定义的多态函数。在 Lean 里，“对所有类型”写成一个类型参数：

```lean no-check
def alpha : {a : Type} → F a → G a        -- 或者写成 ∀ {a : Type}, F a → G a
```

在 Haskell 里，`forall a .` 是可以省略的。Lean 也一样：只要打开了**自动绑定隐式参数**（auto-bound implicit，默认就是开的），
签名里出现一个没声明过的单个字母或希腊字母，Lean 就会自动把它当作隐式类型参数。所以通常你会直接写：

```lean no-check
def alpha : F a → G a
```

请记住，这其实是一**族**函数，由 `a` 参数化。花括号表示 `a` 是**隐式**的：调用时不必写出来，Lean 会根据实参的类型推断。
Rust 中类似的写法是泛型函数，只是因为 Rust 没有“类型构造器的变量”（高阶类型，HKT），你没法把 `F`、`G` 也抽象出来，
只能对具体的容器写，例如：

```rust
fn alpha<A>(fa: Vec<A>) -> Option<A> {
    fa.into_iter().next()
}
```

Lean 的多态函数与 C++ 的泛型函数之间有更深刻的差别，它体现在这些函数的实现方式和类型检查方式上。
在 Lean（以及 Haskell）里，多态函数必须对所有类型**一致地**定义：一个公式通吃所有类型。
这叫作**参数多态**（parametric polymorphism）。

而 C++ 默认支持的是**特设多态**（ad hoc polymorphism），意思是一个模板不必对所有类型都良定义。
一个模板对给定类型能否工作，要到**实例化**时——把具体类型代入类型参数时——才决定。类型检查被推迟了，
这常常导致令人费解的错误信息（相信不少人都有被几百行模板报错淹没的经历）。

C++ 里还有函数重载和模板特化的机制，允许同一个函数对不同类型有不同的定义。
在 Haskell 中，这一功能由类型类和类型族提供；在 Lean 中，由类型类以及“返回类型的函数”（Lean 里类型就是普通的值，
可以直接写 `def T : Bool → Type`）提供。

::: tip Rust 视角：Rust 泛型站在参数多态这一边
Rust 的泛型在这一点上像 Lean 而不像 C++：泛型函数在**定义处**就要通过类型检查，函数体里只能使用 trait 约束所承诺的操作。
`fn f<T>(v: Vec<T>) -> Option<T>` 没有任何约束，因此函数体对 `T` 一无所知：不能比较、不能打印、不能凭空造出一个 `T`。
它唯一能做的，就是挪动、复制（如果有 `Clone`）、丢弃已有的元素。正是这种“无知”，让它天然就是“自然”的。
想对不同类型做不同的事，你得显式地写 trait 并为每个类型 `impl`——这正对应 Lean 的类型类。
（Rust 的 specialization 至今仍是不稳定特性；假如它稳定下来，一个泛型函数就可能对某些具体类型“另起炉灶”，这种推理也就随之失效。）
:::

参数多态有一个出人意料的推论：任何如下类型的多态函数

```lean no-check
alpha : F a → G a
```

只要 `F` 和 `G` 是函子，就**自动**满足自然性条件。用范畴论的记号写（$f$ 是函数 $f : a \to b$）：

$$G f \circ \alpha_a = \alpha_b \circ F f$$

在编程中，函子 `G` 对态射 `f` 的作用由 `fmap` 实现。我先写成带显式类型标注的伪代码：

```lean no-check
fmap_G f ∘ alpha_a = alpha_b ∘ fmap_F f
```

由于有类型推断，这些标注都不必要，下面的等式成立：

```lean no-check
Functor.map f ∘ alpha = alpha ∘ Functor.map f
```

在 Haskell 里，这还不是真正的代码——Haskell 无法在代码中表达函数之间的相等；它只是一个恒等式，
程序员可以用它做等式推理，编译器也可以用它实现优化。**而在 Lean 里，它就是真正的代码**：
函数的相等是一个命题，可以写下来、可以证明。我们把“多态函数 `η` 是自然的”定义成一个命题：

```lean
/-- 多态函数 `η : F α → G α` 是自然的：对任意 `f`，`map f ∘ η = η ∘ map f`。 -/
def Natural (F G : Type → Type) [Functor F] [Functor G]
    (η : {α : Type} → F α → G α) : Prop :=
  ∀ {α β : Type} (f : α → β), Functor.map f ∘ η = η ∘ Functor.map f
```

这里 `Functor` 是 Lean 核心库自带的类型类（对应 Haskell 的 `Functor`），`Functor.map f` 就是 `fmap f`。
参数 `η : {α : Type} → F α → G α` 的类型本身就带着一个隐式的类型参数：`η` 是一个**多态函数**被当作参数传进来。
这在 Rust 里没有直接对应物（Rust 的闭包不能是泛型的）。

为什么在 Haskell 里自然性条件是自动成立的？这与“**免费的定理**”（theorems for free）有关。
用来在 Haskell 中定义自然变换的参数多态，对实现施加了非常强的限制——一个公式通吃所有类型。
这些限制会转化为关于这类函数的等式定理。对于在函子之间做变换的函数来说，这些免费定理恰好就是自然性条件。
（关于免费定理，可以读读我的博客文章
[Parametricity: Money for Nothing and Theorems for Free](https://bartoszmilewski.com/2014/09/22/parametricity-money-for-nothing-and-theorems-for-free/)。）

::: warning 易错点：Lean 能“内部”证明“所有多态函数都自然”吗？不能。
“参数多态的函数都是自然的”这一结论，叫作**参数性定理**（parametricity）。注意它是一条**元定理**（metatheorem）：
它不是在语言**内部**证明的，而是在语言**外部**、通过分析“这门语言里一共能写出哪些程序”得到的。
你没法在 Lean 里写出这样一条定理：

```lean no-check
theorem all_natural (η : {α : Type} → List α → Option α) : Natural List Option η := ...  -- 证不出来！
```

原因有二。第一，Lean 的逻辑本身并不包含参数性这条公理。第二，更要命的是，Lean 带有经典逻辑的
选择公理 `Classical.choice`，借助它，你**真的能**写出一个“会看类型下菜碟”的多态函数，从而打破自然性。下面就是一个反例。
:::

```lean
def safeHead {α : Type} : List α → Option α
  | []     => none
  | x :: _ => some x

/-- `Nat` 与 `Bool` 不是同一个类型：`Bool` 中任意三个元素必有两个相等，`Nat` 则不然。 -/
theorem nat_ne_bool : Nat ≠ Bool := by
  intro h
  have key : ∀ x y z : Bool, x = y ∨ y = z ∨ x = z := by decide
  have : ∀ x y z : Nat, x = y ∨ y = z ∨ x = z := h ▸ key
  have := this 0 1 2
  simp at this

open Classical in
/-- 一个“会看类型”的冒牌多态函数：元素类型恰好是 `Bool` 时，它故意返回 `none`。 -/
noncomputable def weird {α : Type} (xs : List α) : Option α :=
  if α = Bool then none else safeHead xs

/-- 它不是自然的：取 `f : Nat → Bool`，两条路径在 `[0]` 上给出不同结果。 -/
theorem weird_not_natural : ¬ Natural List Option weird := by
  intro h
  have := congrFun (h (fun (_ : Nat) => true)) [0]
  simp [Functor.map, weird, nat_ne_bool, safeHead] at this
```

::: tip Lean 深入：这几行代码在做什么
- `if α = Bool then ... else ...`：要对一个命题做 `if`，Lean 需要知道它**可判定**（`Decidable`）。“两个类型是否相等”
  在计算上是没法判定的，`open Classical in` 借来经典逻辑，宣布“任何命题都可判定”。代价是函数不再能运行，
  所以必须标记为 `noncomputable`。
- `h ▸ key`：用等式 `h : Nat = Bool` 把 `key` 中的 `Bool` 换成 `Nat`（`▸` 读作“沿着 h 运送”）。
- `decide` 让 Lean 把 `Bool` 的所有 $2^3$ 种情况逐一算一遍；`simp at this` 把 `0 = 1 ∨ 1 = 2 ∨ 0 = 2` 化简成 `False`，完成反证。
- `congrFun`：由函数相等 `f = g` 得出 `f x = g x`。

结论：在 Lean 里，**自然性不是免费的**，要对每个具体函数分别证明。好消息是，对于老老实实用模式匹配写出来的函数，
这些证明几乎总是 `funext` + `cases`（或 `induction`）+ `rfl` 三板斧。本章接下来就逐个演示。
:::

::: tip Rust 视角：Rust 的参数性也有小漏洞
在 Rust 里，类似的“作弊”也能做到，而且不需要任何 trait 约束：`std::any::type_name::<T>()` 和
`std::mem::size_of::<T>()` 对任何 `T` 都能调用。

```rust
use std::any::type_name;

fn weird<T>(v: Vec<T>) -> Option<T> {
    if type_name::<T>() == type_name::<String>() {
        None
    } else {
        v.into_iter().next()
    }
}
```

所以“Rust 泛型函数天然自然”是一条**好的经验法则**，而不是定理。不过，老老实实写出来的泛型函数确实都满足它。
:::

我之前提到过，可以把函子看作**广义的容器**。沿着这个比喻继续：自然变换就是把一个容器里的东西**重新装进**另一个容器的配方。
我们不碰这些东西本身：既不修改它们，也不创造新的。我们只是把它们（的一部分）复制——有时复制好几次——到新容器里。

这样一来，自然性条件就成了这样一句话：先用 `fmap` 修改容器里的东西、再重新装箱，与先重新装箱、再用新容器自己的 `fmap`
修改里面的东西，结果是一样的。“重新装箱”和“`fmap`”这两个动作是**正交**的。
**一个负责挪鸡蛋，一个负责煮鸡蛋。**

我们来看几个自然变换的例子。第一个是从列表函子到 `Option` 函子（Haskell 里叫 `Maybe`）的变换：
它返回列表的头元素，但只在列表非空时才返回。这正是上面已经定义过的 `safeHead`：

```lean no-check
def safeHead {α : Type} : List α → Option α
  | []     => none
  | x :: _ => some x
```

它是 `α` 上的多态函数，对任何类型 `α` 都能工作，没有任何限制，所以它是参数多态的一个例子。
因此它是这两个函子之间的自然变换。不过为了让自己信服，我们还是来验证一下自然性条件：

```lean no-check
Option.map f ∘ safeHead = safeHead ∘ List.map f
```

要考虑两种情况。空列表：

```lean
example {α β : Type} (f : α → β) :
    Option.map f (safeHead []) = none := calc
  Option.map f (safeHead []) = Option.map f none := rfl
  _                          = none              := rfl

example {α β : Type} (f : α → β) :
    safeHead (List.map f []) = none := calc
  safeHead (List.map f []) = safeHead [] := rfl
  _                        = none        := rfl
```

以及非空列表：

```lean
example {α β : Type} (f : α → β) (x : α) (xs : List α) :
    Option.map f (safeHead (x :: xs)) = some (f x) := calc
  Option.map f (safeHead (x :: xs)) = Option.map f (some x) := rfl
  _                                 = some (f x)            := rfl

example {α β : Type} (f : α → β) (x : α) (xs : List α) :
    safeHead (List.map f (x :: xs)) = some (f x) := calc
  safeHead (List.map f (x :: xs)) = safeHead (f x :: List.map f xs) := rfl
  _                               = some (f x)                      := rfl
```

两种情况下两边都得出了同一个值。这里我用到了列表的 `map` 的实现：

```lean
namespace Sketch

def listMap {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: listMap f xs

end Sketch
```

以及 `Option` 的：

```lean
namespace Sketch

def optionMap {α β : Type} (f : α → β) : Option α → Option β
  | none   => none
  | some x => some (f x)

end Sketch
```

（Lean 核心库中的 `List.map` 与 `Option.map` 正是这样定义的，所以上面的每一步都是 `rfl`——“按定义展开即可”。）

把两种情况合起来，就是一条完整的定理。`funext` 把“两个函数相等”化归为“对每个输入，两边的值相等”；
`cases xs` 把列表分成空与非空两种情况：

```lean
theorem safeHead_natural {α β : Type} (f : α → β) :
    Option.map f ∘ safeHead = safeHead ∘ List.map f := by
  funext xs            -- 目标变成：Option.map f (safeHead xs) = safeHead (List.map f xs)
  cases xs with
  | nil         => rfl -- 两边都是 none
  | cons x rest => rfl -- 两边都是 some (f x)

/-- 用上面定义的 `Natural` 来陈述，证明是同一个。 -/
theorem safeHead_isNatural : Natural List Option safeHead := by
  intro α β f
  exact safeHead_natural f
```

下面这个小工具让你亲手“走”一遍自然性方块。选一个自然变换、一个函数 `f` 和一个输入列表，然后一步步地看：
上路先 `safeHead` 再 `Option.map f`，下路先 `List.map f` 再 `safeHead`，两条路的中间值逐个出现，最后在右下角汇合。
别忘了试试最后那个“冒牌货” `weird`（为了让效果更明显，组件里的版本在元素类型为 `String` 时作怪）：
有的 `f` 能让它侥幸过关，有的则立刻露馅——而自然性要求对**所有** `f` 都成立。

<div><Ch1_10NaturalitySquare /></div>

::: tip Rust 视角：用测试“抽查”自然性
Rust 里没有证明，但你可以把自然性条件写成一个性质测试（property test）：

```rust
fn safe_head<T>(v: Vec<T>) -> Option<T> {
    v.into_iter().next()
}

/// 自然性：先 map 再取头 == 先取头再 map。
fn naturality_holds<A: Clone, B: PartialEq>(v: Vec<A>, f: impl Fn(A) -> B) -> bool {
    let left = safe_head(v.clone()).map(&f);
    let right = safe_head(v.into_iter().map(&f).collect());
    left == right
}

#[test]
fn check() {
    assert!(naturality_holds(vec![3, 1, 2], |n: i32| n.to_string()));
    assert!(naturality_holds(Vec::<i32>::new(), |n: i32| n * 2));
}
```

测试只能抽查有限个输入；Lean 的 `safeHead_natural` 则对**所有**类型、所有 `f`、所有列表一次性成立。
顺带一提，这条等式也正是编译器可以用来做优化的依据：右边要先把整个列表 `map` 一遍，左边只需对一个元素调用 `f`。
:::

### 把多态函数装进 `NatTrans`

`Natural` 是程序员视角的说法；`NatTrans` 是范畴论视角的说法。两者是一回事，我们来把它们接上。
首先，把 Lean 的 `Functor` 包装成类型范畴上的 `CFunctor`。这需要函子定律，Lean 核心库用类型类 `LawfulFunctor` 表达：
`id_map` 是“保持恒等”，`comp_map` 是“保持复合”。（核心库恰好没有为 `List` 提供 `LawfulFunctor` 实例，我们顺手补上。）

```lean
instance : LawfulFunctor List where
  map_const := rfl
  id_map xs := List.map_id xs
  comp_map _ _ _ := (List.map_map ..).symm

/-- 一个守法的 Lean `Functor`，就是类型范畴上的一个自函子。 -/
def toCFunctor (F : Type → Type) [Functor F] [LawfulFunctor F] : CFunctor Type Type where
  obj := F
  map f := Functor.map f
  map_id _ := by funext x; exact id_map x
  map_comp f g := by funext x; exact comp_map f g x

/-- 自然的多态函数 ⇒ 自然变换。 -/
def NatTrans.ofNatural {F G : Type → Type} [Functor F] [LawfulFunctor F]
    [Functor G] [LawfulFunctor G]
    (η : {α : Type} → F α → G α) (h : Natural F G η) : toCFunctor F ⟹ toCFunctor G where
  app _ := η
  naturality f := h f

def safeHeadNat : toCFunctor List ⟹ toCFunctor Option :=
  NatTrans.ofNatural safeHead safeHead_isNatural

example : safeHeadNat.app Nat [1, 2, 3] = some 1 := rfl
```

注意 `ofNatural` 的签名：它要求你同时交出函数 `η` **和**它的自然性证明 `h`。在 Lean 里，“参数多态带来的免费定理”
不再是免费的，但它变成了一张**由编译器验收的收据**。

### 列表反转

再来一个“装箱”例子：把列表反转。它从列表函子到列表函子自己，元素一个不少，只是换了个顺序。
这次需要对列表做**归纳**（induction），因为 `reverse` 会一路走到列表末尾：

```lean
theorem reverse_isNatural : Natural List List List.reverse := by
  intro α β f
  funext xs
  show List.map f xs.reverse = (List.map f xs).reverse
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    -- (x :: xs).reverse = xs.reverse ++ [x]，再用 map 对 ++ 的分配律与归纳假设 ih
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, ih]

def reverseNat : toCFunctor List ⟹ toCFunctor List :=
  NatTrans.ofNatural List.reverse reverse_isNatural

/-- 反转是它自己的逆，所以它甚至是一个自然同构。 -/
def reverseIso : NatIso (toCFunctor List) (toCFunctor List) where
  hom := reverseNat
  inv := reverseNat
  hom_inv _ := by funext (xs : List _); exact List.reverse_reverse xs
  inv_hom _ := by funext (xs : List _); exact List.reverse_reverse xs
```

::: info 数学小课堂：数学归纳法
要证明“对所有列表 `xs`，P(xs) 成立”，只需证明两件事：
（1）P(`[]`) 成立；（2）如果 P(`xs`) 成立（这叫**归纳假设**），那么 P(`x :: xs`) 也成立。
因为每个列表都是从 `[]` 出发、一次次用 `::` 搭起来的，这两步就像多米诺骨牌，推倒第一块，后面的全倒。
Lean 的 `induction xs with | nil => … | cons x xs ih => …` 正是这两步，`ih` 就是归纳假设。
:::

### `Const` 函子

一个有趣的情形是：其中一个函子是平凡的 `Const` 函子。从 `Const` 函子出发、或者到达 `Const` 函子的自然变换，
看起来就像一个仅在返回类型上多态、或仅在参数类型上多态的函数。

Lean 核心库里没有 `Const`，我们自己定义：`Const c α` 里装着一个 `c` 类型的值，而类型参数 `α` 只是摆设（“幻影类型”）。
`map` 什么也不做——反正里面没有 `α`：

```lean
structure Const (c : Type) (α : Type) where
  unConst : c

instance : Functor (Const c) where
  map _ k := ⟨k.unConst⟩

instance : LawfulFunctor (Const c) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

例如，`length` 可以看作从列表函子到 `Const Int` 函子的自然变换：

```lean
def length {α : Type} : List α → Const Int α
  | []      => ⟨0⟩
  | _ :: xs => ⟨1 + (length xs).unConst⟩
```

这里字段访问 `.unConst` 用来把 `Const` 的外壳剥掉，作用和原书中的函数 `unConst` 一样：

```lean
example : (⟨42⟩ : Const Int String).unConst = 42 := rfl
```

当然，在实际中 `length` 被定义为：

```lean no-check
List.length : List α → Nat
```

这就有效地掩盖了它是一个自然变换的事实。自然性的证明需要归纳，因为 `length` 也要走遍整个列表：

```lean
theorem length_isNatural : Natural List (Const Int) length := by
  intro α β f
  funext xs
  -- 左边：Const 的 map 什么也不做，只是改了改幻影类型
  show (⟨(length xs).unConst⟩ : Const Int β) = length (List.map f xs)
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show (⟨1 + (length xs).unConst⟩ : Const Int β) = ⟨1 + (length (List.map f xs)).unConst⟩
    rw [← ih]

def lengthNat : toCFunctor List ⟹ toCFunctor (Const Int) :=
  NatTrans.ofNatural length length_isNatural
```

找一个**从** `Const` 函子出发的参数多态函数则要难一点，因为那需要无中生有地造出一个值。我们能做到的最好的就是：

```lean
def scam {α : Type} : Const Int α → Option α
  | ⟨_⟩ => none

theorem scam_isNatural : Natural (Const Int) Option scam := by
  intro α β f
  funext ⟨_⟩
  rfl
```

（`funext ⟨_⟩` 在引入变量的同时对它做模式匹配，把结构体拆开。）

### Reader 函子

另一个我们已经见过、并将在米田引理中扮演重要角色的常见函子是 `Reader` 函子。我把它的定义改写成一个单字段的结构体
（Haskell 里用 `newtype`；Lean 核心库里对应的是 `ReaderM`，即 `ReaderT ρ Id`）：

```lean
structure Reader (e : Type) (α : Type) where
  run : e → α
```

它由两个类型参数化，但只在第二个参数上是（协变的）函子：

```lean
instance : Functor (Reader e) where
  map f r := ⟨fun x => f (r.run x)⟩

instance : LawfulFunctor (Reader e) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

对每个类型 `e`，你都可以定义一族从 `Reader e` 到任意其他函子 `f` 的自然变换。我们以后会看到，
这一族的成员总是与 `f e` 的元素一一对应（这就是[米田引理](/part2/05-the-yoneda-lemma)）。

例如，考虑那个有点平凡的单位类型 `Unit`，它只有一个元素 `()`。函子 `Reader Unit` 把任意类型 `α` 映成函数类型 `Unit → α`。
这恰好是所有“从集合 `α` 中挑出一个元素”的函数，有多少个元素，就有多少个这样的函数。
现在来考虑从这个函子到 `Option` 函子的自然变换：

```lean no-check
alpha : Reader Unit α → Option α
```

这样的变换只有两个：`dumb` 和 `obvious`：

```lean
def dumb {α : Type} : Reader Unit α → Option α
  | ⟨_⟩ => none
```

以及

```lean
def obvious {α : Type} : Reader Unit α → Option α
  | ⟨g⟩ => some (g ())
```

（拿到 `g` 之后，你唯一能做的就是把它应用到单位值 `()` 上。）它们都是自然的，证明照例是“拆开、`rfl`”：

```lean
theorem dumb_isNatural : Natural (Reader Unit) Option dumb := by
  intro α β f; funext ⟨g⟩; rfl

theorem obvious_isNatural : Natural (Reader Unit) Option obvious := by
  intro α β f; funext ⟨g⟩; rfl
```

果然，正如米田引理所预言的，它们对应于 `Option Unit` 类型的两个元素：`none` 和 `some ()`。
我们以后还会回到米田引理——这只是一个小小的预告。

::: warning 易错点：“只有两个”是哪种意义上的“只有”？
“从 `Reader Unit` 到 `Option` 的自然变换只有两个”，这句话在范畴论意义上完全正确：**自然的**变换只有 `dumb` 和 `obvious`。
但“能写出的多态函数只有两个”就要靠参数性这条元定理了；在 Lean 里，借助 `Classical`，你可以写出更多“看类型下菜碟”的函数，
只不过它们统统**不自然**（就像前面的 `weird`）。范畴论只关心自然的那些，这正是我们用 `NatTrans` 而不是裸的多态函数来做定义的原因。
:::

## 超越自然性

两个函子之间的参数多态函数（包括 `Const` 函子这种边界情形）总是自然变换。由于所有标准的代数数据类型都是函子，
所以这些类型之间的任何多态函数都是自然变换（在 Haskell 里由参数性保证；在 Lean 里，对于不借用经典逻辑、老老实实写出来的函数，你通常都能逐个证明出来）。

我们手里还有函数类型，而函数类型在返回类型上是函子性的。我们可以用它们构造函子（比如 `Reader` 函子），
并定义本身是高阶函数的自然变换。

然而，函数类型在**参数类型**上不是协变的，而是**逆变**（contravariant）的。当然，逆变函子等价于从对偶范畴出发的协变函子。
两个逆变函子之间的多态函数，在范畴论意义上仍然是自然变换，只不过它们作用的函子是从（Lean 类型范畴的）对偶范畴到类型范畴的。

你也许还记得我们之前看过的那个逆变函子的例子：

```lean
structure Op (r : Type) (α : Type) where
  run : α → r
```

这个函子在 `α` 上是逆变的。Lean 核心库没有 `Contravariant` 类型类，我们自己写一个：

```lean
class Contravariant (F : Type → Type) where
  contramap : {α β : Type} → (β → α) → F α → F β

instance : Contravariant (Op r) where
  contramap f g := ⟨g.run ∘ f⟩
```

我们可以写一个从（比如说）`Op Bool` 到 `Op String` 的多态函数：

```lean
def predToStr {α : Type} : Op Bool α → Op String α
  | ⟨f⟩ => ⟨fun x => if f x then "T" else "F"⟩
```

但由于这两个函子都不是协变的，这在类型范畴里**不是**自然变换。不过，因为它们都是逆变的，它们满足“反过来的”自然性条件：

```lean
theorem predToStr_natural {α β : Type} (f : β → α) :
    Contravariant.contramap f ∘ predToStr = predToStr ∘ Contravariant.contramap f := by
  funext ⟨g⟩
  rfl
```

注意，由于 `contramap` 的签名，这里的函数 `f` 的方向必须与你在 `fmap` 中使用的方向相反：

```lean no-check
contramap : (β → α) → (Op Bool α → Op Bool β)
```

有没有既不是协变函子、也不是逆变函子的类型构造器呢？下面就是一例：

```lean
def Endo (α : Type) : Type := α → α
```

它不是函子，因为同一个类型 `α` 既出现在负（逆变）位置，又出现在正（协变）位置。你没法为这个类型实现 `fmap` 或 `contramap`：

```lean no-check
instance : Functor Endo where
  map f e := fun b => f (e ?)   -- 要喂给 e 一个 α，可我们手里只有 b : β 和 f : α → β
```

因此，签名为

```lean no-check
(α → α) → F α
```

的函数（其中 `F` 是任意函子）不可能是自然变换。有趣的是，有一种自然变换的推广，叫作**双自然变换**（dinatural transformation），
专门处理这类情形。等我们讨论[端](/part3/10-ends-and-coends)的时候再来说它。

## 函子范畴

既然有了函子之间的映射——自然变换——自然会问：函子是否构成一个范畴？确实如此！
对于每一对范畴 $\mathcal{C}$ 和 $\mathcal{D}$，都有一个函子范畴。这个范畴的对象是从 $\mathcal{C}$ 到 $\mathcal{D}$ 的函子，
态射是这些函子之间的自然变换。

我们必须定义两个自然变换的复合，不过这很容易。自然变换的分量是态射，而我们知道怎样复合态射。

确实，取一个从函子 $F$ 到 $G$ 的自然变换 $\alpha$。它在对象 $a$ 处的分量是某个态射：

$$\alpha_a : F a \to G a$$

我们想把 $\alpha$ 与 $\beta$ 复合，$\beta$ 是从函子 $G$ 到 $H$ 的自然变换。$\beta$ 在 $a$ 处的分量是态射：

$$\beta_a : G a \to H a$$

这两个态射可以复合，复合结果是另一个态射：

$$\beta_a \circ \alpha_a : F a \to H a$$

我们就用这个态射作为自然变换 $\beta \cdot \alpha$——即两个自然变换的复合，$\beta$ 在 $\alpha$ 之后——的分量：

$$(\beta \cdot \alpha)_a = \beta_a \circ \alpha_a$$

![垂直复合](/img/1.10/5_vertical.jpg "两个自然变换的复合：在每个对象 a 处，把分量 α_a 与 β_a 首尾相接。")

（久久地）看一眼图，就能确信这个复合的结果确实是从 $F$ 到 $H$ 的自然变换：

$$H f \circ (\beta \cdot \alpha)_a = (\beta \cdot \alpha)_b \circ F f$$

![垂直复合的自然性](/img/1.10/6_verticalnaturality.jpg "上下两个自然性方块拼在一起，大长方形也交换。")

下面这幅图把“久久地看”变成了动画。三条路径：左边一列再底边（$H f \circ (\beta\cdot\alpha)_a$）、
顶边再右边一列（$(\beta\cdot\alpha)_b \circ F f$），以及一条从中间横穿的路径。
上半个方块（$\alpha$ 的自然性）让你把“顶边再往下”换成“往下再走中间”；下半个方块（$\beta$ 的自然性）再把“中间再往下”换成“往下再走底边”。

```diagram
Fa: (0, 0) "F a"
Ga: (0, 1.3) "G a"
Ha: (0, 2.6) "H a"
Fb: (2.4, 0) "F b"
Gb: (2.4, 1.3) "G b"
Hb: (2.4, 2.6) "H b"
Ff: Fa -> Fb "F f"
Gf: Ga -> Gb "G f"
Hf: Ha -> Hb "H f" side=right
aa: Fa -> Ga "\alpha_a" side=right
ba: Ga -> Ha "\beta_a" side=right
ab: Fb -> Gb "\alpha_b"
bb: Gb -> Hb "\beta_b"
path "(β·α)_b ∘ F f": Ff ab bb
path "穿过中间：β_b ∘ G f ∘ α_a": aa Gf bb color=orange
path "H f ∘ (β·α)_a": aa ba Hf color=green
caption: 两个自然性方块上下拼接，外框也交换——这就是垂直复合仍然自然的原因。
```

在 Lean 里，这个“久久地看”就是一条五步的 `calc`。每一步要么是结合律（挪括号），要么是某个自然性条件（过一个方块）：

```lean
namespace CTFP
open Category

variable {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
  {E : Type u₃} [Category.{u₃, v₃} E]

/-- 垂直复合 `β · α`：分量逐个复合。 -/
def NatTrans.vcomp {F G H : CFunctor C D} (β : G ⟹ H) (α : F ⟹ G) : F ⟹ H where
  app a := β.app a ⊚ α.app a
  naturality {a b} f := calc
    H.map f ⊚ (β.app a ⊚ α.app a)
        = (H.map f ⊚ β.app a) ⊚ α.app a := by rw [Category.assoc]   -- 挪括号
      _ = (β.app b ⊚ G.map f) ⊚ α.app a := by rw [β.naturality]     -- 过下方块
      _ = β.app b ⊚ (G.map f ⊚ α.app a) := by rw [Category.assoc]   -- 挪括号
      _ = β.app b ⊚ (α.app b ⊚ F.map f) := by rw [α.naturality]     -- 过上方块
      _ = (β.app b ⊚ α.app b) ⊚ F.map f := by rw [Category.assoc]   -- 挪括号

end CTFP
```

::: tip Lean 深入：`variable`
`variable {C : Type u₁} [Category C] ...` 声明了一组“公共参数”。之后在同一个命名空间（或 `section`）里写的定义，
只要用到了 `C`，Lean 就会自动把它们加为隐式参数。这省去了在每个定义前重复写一长串 `{C : Type u₁} [Category.{u₁, v₁} C]`。
:::

自然变换的复合满足结合律，因为它们的分量是普通的态射，而普通态射的复合满足结合律。

最后，对每个函子 $F$，都有一个恒等自然变换 $1_F$，它的分量是恒等态射：

$$\mathrm{id}_{F a} : F a \to F a$$

所以，函子确实构成一个范畴。

要在 Lean 里把这句话变成一个 `Category` 实例，还差一块拼图：我们需要知道**什么时候两个自然变换相等**。
一个自然变换有两个字段：分量 `app` 和证明 `naturality`。直觉上，分量相同的两个自然变换就是同一个——
证明长什么样无关紧要。这在 Lean 里成立，靠的是**证明无关性**（proof irrelevance）：同一个命题的任意两个证明在定义上相等。
于是有下面这条**外延性引理**：

```lean
namespace CTFP
open Category

variable {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
  {E : Type u₃} [Category.{u₃, v₃} E]

/-- 外延性：分量相同的自然变换相等（自然性证明自动相等）。 -/
theorem NatTrans.ext {F G : CFunctor C D} {α β : F ⟹ G} (h : α.app = β.app) : α = β := by
  cases α        -- 把 α 拆成 ⟨app₁, nat₁⟩
  cases β        -- 把 β 拆成 ⟨app₂, nat₂⟩
  cases h        -- 用 h : app₁ = app₂ 把 app₂ 替换成 app₁
  rfl            -- 剩下 ⟨app₁, nat₁⟩ = ⟨app₁, nat₂⟩：证明无关性让它按定义成立

/-- 恒等自然变换 `1_F`：分量都是恒等态射。 -/
def NatTrans.id (F : CFunctor C D) : F ⟹ F where
  app a := 𝟙 (F.obj a)
  naturality f := by rw [Category.id_comp, Category.comp_id]

/-- 函子范畴 `[C, D]`：对象是函子，态射是自然变换，复合是垂直复合。 -/
instance functorCategory : Category (CFunctor C D) where
  Hom F G := F ⟹ G
  id F := NatTrans.id F
  comp β α := NatTrans.vcomp β α
  id_comp α := NatTrans.ext (by funext a; exact Category.id_comp (α.app a))
  comp_id α := NatTrans.ext (by funext a; exact Category.comp_id (α.app a))
  assoc α β γ := NatTrans.ext (by funext a; exact Category.assoc (α.app a) (β.app a) (γ.app a))

end CTFP
```

看看这三条定律的证明：每一条都是“用外延性化归到分量，再引用 $\mathcal{D}$ 中相应的定律”。
这正是原书那句话的 Lean 版本：自然变换的复合满足结合律，**因为**它们的分量满足。

::: tip Lean 深入：`cases h` 为什么能“替换”
`h : app₁ = app₂` 中的 `app₂` 是一个刚刚由 `cases β` 引入的局部变量。对一个“右边是变量”的等式做 `cases`，
Lean 会把这个变量处处替换成左边（相当于 `subst`）。之后两个结构体只差在证明字段上，而 Lean 的命题是证明无关的，`rfl` 就能收尾。
:::

现在可以在函子范畴里真的做复合了。把“反转”与“取头”垂直复合，就得到“取最后一个元素”：

```lean
/-- 函子范畴里的复合：先反转，再取头 = 取最后一个元素。 -/
def lastNat : toCFunctor List ⟶ toCFunctor Option :=
  (safeHeadNat : toCFunctor List ⟶ toCFunctor Option) ⊚
  (reverseNat : toCFunctor List ⟶ toCFunctor List)

example : lastNat.app Nat [1, 2, 3] = some 3 := rfl
example : lastNat.app Nat ([] : List Nat) = none := rfl
```

（和 [1.7 函子](/part1/07-functors) 中裸 lambda 的情况一样，`⊚` 需要知道用哪个范畴实例，所以这里给两个自然变换标注了
`⟶` 类型；也可以直接写 `NatTrans.vcomp safeHeadNat reverseNat`。）

关于记号说一句。我遵循 Saunders Mac Lane 的习惯，用点 $\cdot$ 表示刚才描述的这种自然变换复合。
问题在于，自然变换有**两种**复合方式。这一种叫作**垂直复合**（vertical composition），因为在描述它的图中，函子通常是上下堆叠的。
垂直复合在定义函子范畴时很重要。水平复合我很快就会解释。

![垂直复合的另一种画法](/img/1.10/6a_vertical.jpg "三个函子 F、G、H 从 C 到 D 上下排开，α 与 β 像两节楼梯一样垂直相接。")

范畴 $\mathcal{C}$ 与 $\mathcal{D}$ 之间的函子范畴记作 $\mathbf{Fun}(\mathcal{C}, \mathcal{D})$，或 $[\mathcal{C}, \mathcal{D}]$，有时也写成 $\mathcal{D}^\mathcal{C}$。
最后这个记号暗示，函子范畴本身也许可以看作另一个范畴中的函数对象（指数对象）。事实真是如此吗？

我们来看看迄今为止搭起来的抽象层级。我们从范畴开始，范畴是对象和态射的集合。范畴本身（严格来说是**小**范畴，即对象构成集合的范畴）
又是一个更高层次的范畴 $\mathbf{Cat}$ 中的对象。这个范畴中的态射是函子。$\mathbf{Cat}$ 中的一个 hom-集就是一个函子的集合。
例如 $\mathbf{Cat}(\mathcal{C}, \mathcal{D})$ 就是两个范畴 $\mathcal{C}$ 与 $\mathcal{D}$ 之间的函子的集合。

![Cat 中的 hom-集](/img/1.10/7_cathomset.jpg "在 Cat 中，从 C 到 D 的所有函子构成一个 hom-集 Cat(C, D)。")

::: info 数学小课堂：“小”范畴与“大”范畴
“所有集合的集合”会导致罗素悖论，所以数学家把“对象构成一个集合”的范畴叫作**小范畴**，其余的叫作**大范畴**。
$\mathbf{Cat}$ 是所有小范畴的范畴，它自己是大的，所以它不是自己的对象——悖论就此避开。
Lean 用**宇宙**（`Type 0 : Type 1 : Type 2 : …`）解决同样的问题：`Type` 本身住在 `Type 1` 里。
这就是为什么 `Category`、`CFunctor`、`NatTrans` 的定义都带着 `u₁ v₁` 这样的宇宙变量：
`CFunctor C D` 比 `C`、`D` 的对象“大一号”，函子范畴的对象住在更高的宇宙里。
:::

函子范畴 $[\mathcal{C}, \mathcal{D}]$ 也是两个范畴之间的函子的集合（外加作为态射的自然变换）。它的对象与 $\mathbf{Cat}(\mathcal{C}, \mathcal{D})$ 的成员相同。
而且，函子范畴作为一个范畴，本身也必须是 $\mathbf{Cat}$ 的一个对象（恰好，两个小范畴之间的函子范畴本身也是小的）。
于是我们得到了一个范畴中 hom-集与同一范畴中某个对象之间的关系。这种情形与我们在[上一章](/part1/09-function-types)见过的指数对象一模一样。
我们来看看如何在 $\mathbf{Cat}$ 中构造后者。

你也许还记得，要构造指数对象，得先定义积。在 $\mathbf{Cat}$ 中这相对容易，因为小范畴的对象构成**集合**，而我们知道如何定义集合的笛卡尔积。
所以，积范畴 $\mathcal{C} \times \mathcal{D}$ 中的对象就是一对对象 $(c, d)$，一个来自 $\mathcal{C}$，一个来自 $\mathcal{D}$。
类似地，两个这样的对 $(c, d)$ 与 $(c', d')$ 之间的态射是一对态射 $(f, g)$，其中 $f : c \to c'$，$g : d \to d'$。
这些态射对逐分量复合，并且总有一个恒等对，它就是一对恒等态射。长话短说，$\mathbf{Cat}$ 是一个货真价实的笛卡尔闭范畴，
其中任意两个范畴都有指数对象 $\mathcal{D}^\mathcal{C}$。而我说的 $\mathbf{Cat}$ 中的“对象”就是一个范畴，所以 $\mathcal{D}^\mathcal{C}$ 是一个范畴，
我们可以把它等同于 $\mathcal{C}$ 与 $\mathcal{D}$ 之间的函子范畴。

::: details 补充：积范畴的 Lean 实现
积范畴的三条定律都直接继承自两个分量范畴，`simp only` 把每个分量上的定律改写一遍即可：

```lean
namespace CTFP
open Category

variable {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]

/-- 积范畴 `C × D`：对象是对，态射是态射对，逐分量复合。 -/
instance prodCategory : Category (C × D) where
  Hom p q := (p.1 ⟶ q.1) × (p.2 ⟶ q.2)
  id p := (𝟙 p.1, 𝟙 p.2)
  comp g f := (g.1 ⊚ f.1, g.2 ⊚ f.2)
  id_comp f := by simp only [Category.id_comp]
  comp_id f := by simp only [Category.comp_id]
  assoc f g h := by simp only [Category.assoc]

end CTFP
```

（$\mathbf{Cat}$ 的笛卡尔闭性还要求“柯里化”：从 $\mathcal{C} \times \mathcal{D}$ 到 $\mathcal{E}$ 的函子，一一对应于从 $\mathcal{C}$ 到函子范畴 $[\mathcal{D}, \mathcal{E}]$ 的函子。
这需要更多的宇宙与外延性体操，这里就不展开了。）
:::

## 2-范畴

把这些说清楚之后，我们来仔细看看 $\mathbf{Cat}$。按定义，$\mathbf{Cat}$ 中的任意 hom-集都是一个函子的集合。但正如我们所见，
两个对象之间的函子拥有比单纯集合更丰富的结构：它们构成一个范畴，以自然变换为态射。由于函子在 $\mathbf{Cat}$ 中被视为态射，
自然变换就是**态射之间的态射**。

这种更丰富的结构是 **2-范畴**（2-category）的一个例子。2-范畴是范畴的推广：除了对象和态射（在这里可以叫作 1-态射），
还有 2-态射，也就是态射之间的态射。

把 $\mathbf{Cat}$ 看作 2-范畴时，我们有：

- 对象：（小）范畴
- 1-态射：范畴之间的函子
- 2-态射：函子之间的自然变换

![Cat 作为 2-范畴](/img/1.10/8_cat-2-cat.jpg "两个范畴之间不再只是一个函子集合，而是一个 hom-范畴：函子是它的对象，自然变换是它的态射。")

两个范畴 $\mathcal{C}$ 与 $\mathcal{D}$ 之间不再是一个 hom-集，而是一个 **hom-范畴**——函子范畴 $\mathcal{D}^\mathcal{C}$。
我们有普通的函子复合：$\mathcal{D}^\mathcal{C}$ 中的函子 $F$ 与 $\mathcal{E}^\mathcal{D}$ 中的函子 $G$ 复合，得到 $\mathcal{E}^\mathcal{C}$ 中的 $G \circ F$。
在 Lean 里，函子复合就是“对象和态射都先过 `F` 再过 `G`”，两条函子定律则先用 `F` 的、再用 `G` 的：

```lean
namespace CTFP
open Category

variable {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
  {E : Type u₃} [Category.{u₃, v₃} E]

/-- 函子复合 `G ∘ F`（Cat 中的 1-态射复合）。 -/
def CFunctor.comp (G : CFunctor D E) (F : CFunctor C D) : CFunctor C E where
  obj a := G.obj (F.obj a)
  map f := G.map (F.map f)
  map_id a := by rw [F.map_id, G.map_id]
  map_comp f g := by rw [F.map_comp, G.map_comp]

end CTFP
```

但我们在每个 hom-范畴**内部**也有复合——函子之间的自然变换（即 2-态射）的垂直复合。

一个 2-范畴里有两种复合，问题就来了：它们彼此之间如何相互作用？

我们在 $\mathbf{Cat}$ 中取两个函子（即 1-态射）：

$$F : \mathcal{C} \to \mathcal{D} \qquad G : \mathcal{D} \to \mathcal{E}$$

以及它们的复合：

$$G \circ F : \mathcal{C} \to \mathcal{E}$$

假设我们有两个自然变换 $\alpha$ 和 $\beta$，分别作用在函子 $F$ 和 $G$ 上：

$$\alpha : F \to F' \qquad \beta : G \to G'$$

![水平复合的原料](/img/1.10/10_horizontal.jpg "α 连接 C 到 D 的两个函子 F 与 F′，β 连接 D 到 E 的两个函子 G 与 G′。")

注意，我们不能对这一对使用垂直复合，因为 $\alpha$ 的目标与 $\beta$ 的源不同。事实上，它们属于两个不同的函子范畴：$\mathcal{D}^\mathcal{C}$ 和 $\mathcal{E}^\mathcal{D}$。
不过，我们可以复合函子 $F'$ 和 $G'$，因为 $F'$ 的目标正是 $G'$ 的源——范畴 $\mathcal{D}$。函子 $G' \circ F'$ 与 $G \circ F$ 之间是什么关系？

有了 $\alpha$ 和 $\beta$，我们能否定义一个从 $G \circ F$ 到 $G' \circ F'$ 的自然变换？让我勾勒一下这个构造。

![水平复合的构造](/img/1.10/9_horizontal.jpg "对象 a 先分裂成 F a 与 F′a，再分裂成四个对象，四个态射围成一个方块。")

照例，我们从 $\mathcal{C}$ 中的一个对象 $a$ 出发。它的像在 $\mathcal{D}$ 中分裂成两个对象：$F a$ 和 $F' a$。还有一个态射——$\alpha$ 的一个分量——连接这两个对象：

$$\alpha_a : F a \to F' a$$

从 $\mathcal{D}$ 走到 $\mathcal{E}$ 时，这两个对象进一步分裂成四个对象：$G(F a)$、$G'(F a)$、$G(F' a)$、$G'(F' a)$。
我们还有四个态射，围成一个方块。其中两个态射是自然变换 $\beta$ 的分量：

$$\beta_{F a} : G(F a) \to G'(F a) \qquad \beta_{F' a} : G(F' a) \to G'(F' a)$$

另外两个是 $\alpha_a$ 在两个函子下的像（函子会映射态射）：

$$G \alpha_a : G(F a) \to G(F' a) \qquad G' \alpha_a : G'(F a) \to G'(F' a)$$

态射可真不少。我们的目标是找到一个从 $G(F a)$ 到 $G'(F' a)$ 的态射，作为连接函子 $G \circ F$ 与 $G' \circ F'$ 的自然变换的分量的候选。
实际上，从 $G(F a)$ 到 $G'(F' a)$ 的路径不是一条，而是两条：

$$G' \alpha_a \circ \beta_{F a} \qquad \beta_{F' a} \circ G \alpha_a$$

我们很幸运，它们是相等的，因为我们围出来的这个方块，恰好就是 $\beta$ 的自然性方块（对态射 $\alpha_a$ 而言）。

```diagram
GFa: (0, 0) "G(F a)"
G'Fa: (2.6, 0) "G'(F a)"
GF'a: (0, 1.7) "G(F' a)"
G'F'a: (2.6, 1.7) "G'(F' a)"
bFa: GFa -> G'Fa "\beta_{F a}"
Gaa: GFa -> GF'a "G \alpha_a" side=right
G'aa: G'Fa -> G'F'a "G' \alpha_a"
bF'a: GF'a -> G'F'a "\beta_{F' a}" side=right
diag: GFa -> G'F'a "(\beta \circ \alpha)_a" dashed color=purple pos=0.4
path "G'α_a ∘ β_{Fa}": bFa G'aa
path "β_{F'a} ∘ Gα_a": Gaa bF'a color=green
path "对角线 (β∘α)_a": diag color=purple
caption: 水平复合的分量：方块是 β 在态射 α_a 上的自然性方块，所以两条路径相等，对角线就是它们的公共值。
```

在 Lean 里，“它们相等”就是 $\beta$ 的自然性条件在 $\alpha_a$ 上的一个特例，一行就够了：

```lean
namespace CTFP
open Category

variable {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
  {E : Type u₃} [Category.{u₃, v₃} E]

/-- 两条路径相等：这正是 β 在态射 `α.app a` 上的自然性方块。 -/
theorem NatTrans.hcomp_square {F F' : CFunctor C D} {G G' : CFunctor D E}
    (β : G ⟹ G') (α : F ⟹ F') (a : C) :
    G'.map (α.app a) ⊚ β.app (F.obj a) = β.app (F'.obj a) ⊚ G.map (α.app a) :=
  β.naturality (α.app a)

end CTFP
```

我们刚刚定义了一个从 $G \circ F$ 到 $G' \circ F'$ 的自然变换的分量。只要有足够的耐心，证明这个变换的自然性相当直接。
Lean 恰好有无穷的耐心：

```lean
namespace CTFP
open Category

variable {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
  {E : Type u₃} [Category.{u₃, v₃} E]

/-- 水平复合 `β ∘ α : G ∘ F ⟹ G' ∘ F'`。 -/
def NatTrans.hcomp {F F' : CFunctor C D} {G G' : CFunctor D E}
    (β : G ⟹ G') (α : F ⟹ F') : G.comp F ⟹ G'.comp F' where
  app a := G'.map (α.app a) ⊚ β.app (F.obj a)
  naturality {a b} f := calc
    G'.map (F'.map f) ⊚ (G'.map (α.app a) ⊚ β.app (F.obj a))
        = (G'.map (F'.map f) ⊚ G'.map (α.app a)) ⊚ β.app (F.obj a) := by rw [Category.assoc]
      _ = G'.map (F'.map f ⊚ α.app a) ⊚ β.app (F.obj a) := by rw [G'.map_comp]   -- G' 保持复合
      _ = G'.map (α.app b ⊚ F.map f) ⊚ β.app (F.obj a) := by rw [α.naturality]   -- α 的方块
      _ = (G'.map (α.app b) ⊚ G'.map (F.map f)) ⊚ β.app (F.obj a) := by rw [G'.map_comp]
      _ = G'.map (α.app b) ⊚ (G'.map (F.map f) ⊚ β.app (F.obj a)) := by rw [Category.assoc]
      _ = G'.map (α.app b) ⊚ (β.app (F.obj b) ⊚ G.map (F.map f)) := by rw [β.naturality] -- β 的方块
      _ = (G'.map (α.app b) ⊚ β.app (F.obj b)) ⊚ G.map (F.map f) := by rw [Category.assoc]

end CTFP
```

证明的思路是：先用“$G'$ 保持复合”把 $G'(F' f)$ 与 $G'\alpha_a$ 合成 $G'(F' f \circ \alpha_a)$，在 $G'$ 的“里面”用一次 $\alpha$ 的自然性，
再拆开；然后用一次 $\beta$ 的自然性（这次是对态射 $F f$），把 $\beta$ 挪到最右边。

我们把这个自然变换称为 $\alpha$ 与 $\beta$ 的**水平复合**（horizontal composition）：

$$\beta \circ \alpha : G \circ F \to G' \circ F'$$

同样遵循 Mac Lane 的习惯，我用小圆圈表示水平复合，不过你也可能见到用星号代替的写法。

下面的小工具用具体的函子演示水平复合：取 $F = G = $ `List`，$F' = G' = $ `Option`，$\alpha$ 与 $\beta$ 各自可以选 `safeHead` 或“取最后一个”。
输入是一个**列表的列表**，你可以看到两条路径的中间值截然不同（一条先处理外层，一条先处理内层），最后却在 `Option (Option Nat)` 里汇合。

<div><Ch1_10NaturalitySquare mode="horizontal" /></div>

这里有一条范畴论的经验法则：**每当你看到复合，就去找一个范畴。** 我们有自然变换的垂直复合，它是函子范畴的一部分。
那水平复合呢？它住在哪个范畴里？

要弄清楚这一点，得**侧着**看 $\mathbf{Cat}$。不要把自然变换看成函子之间的箭头，而要看成范畴之间的箭头。
一个自然变换位于两个范畴之间——就是被它所变换的函子连接起来的那两个范畴。我们可以认为它连接了这两个范畴。

![侧着看 Cat](/img/1.10/sideways.jpg "侧着看：自然变换被当作从 C 到 D 的箭头，水平复合就是这些箭头的复合。")

我们聚焦于 $\mathbf{Cat}$ 的两个对象——范畴 $\mathcal{C}$ 与 $\mathcal{D}$。在连接 $\mathcal{C}$ 与 $\mathcal{D}$ 的函子之间，有一个自然变换的集合。
这些自然变换就是我们从 $\mathcal{C}$ 到 $\mathcal{D}$ 的新箭头。同理，在连接 $\mathcal{D}$ 与 $\mathcal{E}$ 的函子之间也有自然变换，
我们可以把它们当成从 $\mathcal{D}$ 到 $\mathcal{E}$ 的新箭头。水平复合就是这些箭头的复合。

我们还有一个从 $\mathcal{C}$ 到 $\mathcal{C}$ 的恒等箭头：作用在 $\mathcal{C}$ 的恒等函子上、把它映到自身的恒等自然变换。
注意，水平复合的恒等也是垂直复合的恒等，但反之不然。

```lean
namespace CTFP
open Category

variable {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]

def idFunctor (C : Type u) [Category.{u, v} C] : CFunctor C C where
  obj a := a
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 水平复合的恒等：恒等函子上的恒等自然变换，从左边复合时什么也不改变。 -/
theorem NatTrans.hcomp_id_left {F G : CFunctor C D} (α : F ⟹ G) (a : C) :
    (NatTrans.hcomp (NatTrans.id (idFunctor D)) α).app a = α.app a :=
  Category.comp_id _

/-- 从右边复合也一样。 -/
theorem NatTrans.hcomp_id_right {F G : CFunctor C D} (α : F ⟹ G) (a : C) :
    (NatTrans.hcomp α (NatTrans.id (idFunctor C))).app a = α.app a := by
  show G.map (𝟙 a) ⊚ α.app a = α.app a
  rw [G.map_id, Category.id_comp]

end CTFP
```

（这里我们只比较了分量。`G.comp F` 与 `idFunctor D` 复合 `F` 这两个函子的“类型”只在定义展开后才一致，
逐分量陈述可以避开这个技术细节。）

最后，这两种复合满足**交换律**（interchange law）：

$$(\beta' \cdot \alpha') \circ (\beta \cdot \alpha) = (\beta' \circ \beta) \cdot (\alpha' \circ \alpha)$$

这里我引用 Saunders Mac Lane 的话：*读者也许会享受亲手写下证明这一事实所需的那些显然的图。*

在 Lean 里，我们可以享受写下这个证明本身。设 $\alpha : F \Rightarrow G$、$\beta : G \Rightarrow H$（从 $\mathcal{C}$ 到 $\mathcal{D}$），
$\alpha' : F' \Rightarrow G'$、$\beta' : G' \Rightarrow H'$（从 $\mathcal{D}$ 到 $\mathcal{E}$）。用外延性化归到分量之后，
两边在对象 $a$ 处分别是

$$H'(\beta_a \circ \alpha_a) \circ \beta'_{F a} \circ \alpha'_{F a} \quad\text{和}\quad H'\beta_a \circ \beta'_{G a} \circ G'\alpha_a \circ \alpha'_{F a}$$

区别只在中间：左边是 $H'\alpha_a \circ \beta'_{F a}$，右边是 $\beta'_{G a} \circ G'\alpha_a$。而这恰恰是 $\beta'$ 在态射 $\alpha_a$ 上的自然性方块！

```lean
namespace CTFP
open Category

variable {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
  {E : Type u₃} [Category.{u₃, v₃} E]

/-- 交换律：(β' · α') ∘ (β · α) = (β' ∘ β) · (α' ∘ α)。 -/
theorem NatTrans.interchange {F G H : CFunctor C D} {F' G' H' : CFunctor D E}
    (α : F ⟹ G) (β : G ⟹ H) (α' : F' ⟹ G') (β' : G' ⟹ H') :
    NatTrans.hcomp (NatTrans.vcomp β' α') (NatTrans.vcomp β α)
      = NatTrans.vcomp (NatTrans.hcomp β' β) (NatTrans.hcomp α' α) := by
  apply NatTrans.ext
  funext a
  -- 把两边在 a 处的分量按定义展开写出来
  show H'.map (β.app a ⊚ α.app a) ⊚ (β'.app (F.obj a) ⊚ α'.app (F.obj a))
     = (H'.map (β.app a) ⊚ β'.app (G.obj a)) ⊚ (G'.map (α.app a) ⊚ α'.app (F.obj a))
  calc H'.map (β.app a ⊚ α.app a) ⊚ (β'.app (F.obj a) ⊚ α'.app (F.obj a))
      = H'.map (β.app a) ⊚ ((H'.map (α.app a) ⊚ β'.app (F.obj a)) ⊚ α'.app (F.obj a)) := by
        rw [H'.map_comp, Category.assoc, Category.assoc, Category.assoc]
    _ = H'.map (β.app a) ⊚ ((β'.app (G.obj a) ⊚ G'.map (α.app a)) ⊚ α'.app (F.obj a)) := by
        rw [β'.naturality]                     -- 唯一的一步“真”推理：β' 的自然性方块
    _ = (H'.map (β.app a) ⊚ β'.app (G.obj a)) ⊚ (G'.map (α.app a) ⊚ α'.app (F.obj a)) := by
        rw [Category.assoc, Category.assoc, Category.assoc]

end CTFP
```

将来还有一个记号可能会派上用场。在这种侧着看 $\mathbf{Cat}$ 的新解读中，从一个对象到另一个对象有两种方式：用函子，或者用自然变换。
不过，我们可以把函子箭头重新解释为一种特殊的自然变换：作用在这个函子上的恒等自然变换。所以你会经常看到这样的记号：

$$F \circ \alpha$$

其中 $F$ 是从 $\mathcal{D}$ 到 $\mathcal{E}$ 的函子，$\alpha$ 是两个从 $\mathcal{C}$ 到 $\mathcal{D}$ 的函子之间的自然变换。
由于你没法把一个函子与一个自然变换复合，这个记号被解释为恒等自然变换 $1_F$ 在 $\alpha$ 之后的水平复合。

类似地：

$$\alpha \circ F$$

是 $\alpha$ 在 $1_F$ 之后的水平复合。

这种“函子与自然变换的复合”通常叫作**须化**（whiskering，因为画出来像在自然变换旁边添了一根胡须）。
展开定义，它们的分量非常简单：$(F \circ \alpha)_a = F(\alpha_a)$，$(\alpha \circ F)_a = \alpha_{F a}$。

```lean
namespace CTFP
open Category

variable {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
  {E : Type u₃} [Category.{u₃, v₃} E]

/-- `K ∘ α`：分量是 `K (α_a)`。 -/
theorem NatTrans.whiskerLeft_app {F G : CFunctor C D} (K : CFunctor D E) (α : F ⟹ G) (a : C) :
    (NatTrans.hcomp (NatTrans.id K) α).app a = K.map (α.app a) :=
  Category.comp_id _

/-- `α ∘ K`：分量是 `α_{K a}`。 -/
theorem NatTrans.whiskerRight_app {F G : CFunctor D E} (α : F ⟹ G) (K : CFunctor C D) (a : C) :
    (NatTrans.hcomp α (NatTrans.id K)).app a = α.app (K.obj a) := by
  show G.map (𝟙 (K.obj a)) ⊚ α.app (K.obj a) = α.app (K.obj a)
  rw [G.map_id, Category.id_comp]

end CTFP
```

在编程中，须化你天天都在用：`List.map safeHead : List (List α) → List (Option α)` 就是 `List ∘ safeHead`；
而 `safeHead : List (List α) → Option (List α)`（把 `safeHead` 用在“元素本身是列表”的列表上）就是 `safeHead ∘ List`。

## 结语

本书的第一部分到此结束。我们已经学会了范畴论的基本词汇。你可以把对象和范畴看作**名词**；把态射、函子和自然变换看作**动词**。
态射连接对象，函子连接范畴，自然变换连接函子。

但我们也看到，在一个抽象层次上表现为“动作”的东西，到了下一个层次就变成了“对象”。态射的集合变成了函数对象。
作为对象，它可以是另一个态射的源或目标。这就是高阶函数背后的思想。

函子把对象映到对象，所以我们可以把它用作类型构造器，或者说参数化类型。函子也映射态射，所以它又是一个高阶函数——`fmap`。
有一些简单的函子，比如 `Const`、积和余积，可以用来生成形形色色的代数数据类型。函数类型也是函子性的，既有协变的，也有逆变的，
可以用来扩展代数数据类型。

函子可以被看作函子范畴中的对象。作为对象，它们成为态射的源和目标：这些态射就是自然变换。
自然变换是一种特殊的多态函数。

## 挑战

1. 定义一个从 `Option` 函子到列表函子的自然变换。证明它的自然性条件。
2. 在 `Reader Unit` 与列表函子之间定义至少两个不同的自然变换。由 `Unit` 组成的不同列表有多少个？
3. 对 `Reader Bool` 与 `Option` 继续上一题。
4. 证明自然变换的水平复合满足自然性条件（提示：使用分量）。这是一个很好的“追图”（diagram chasing）练习。
5. 写一篇短文，谈谈你会如何享受写下证明交换律所需的那些显然的图。
6. 为不同的 `Op` 函子之间的变换所满足的“反过来的”自然性条件编写一些测试用例。下面是一种选择：

```lean no-check
def op : Op Bool Int := ⟨fun x => decide (x > 0)⟩
def f (x : String) : Int := x.toInt?.getD 0     -- 原书：f x = read x
```

::: details 参考答案
**1.** 把 `none` 送到空列表，把 `some x` 送到单元素列表。证明分两种情况，每种都是 `rfl`：

```lean
def optToList {α : Type} : Option α → List α
  | none   => []
  | some x => [x]

theorem optToList_isNatural : Natural Option List optToList := by
  intro α β f
  funext o
  cases o <;> rfl     -- `<;>` 把后面的 tactic 用在 cases 产生的每个子目标上

def optToListNat : toCFunctor Option ⟹ toCFunctor List :=
  NatTrans.ofNatural optToList optToList_isNatural
```

（Rust 里这就是 `opt.into_iter().collect::<Vec<_>>()`。）

**2.** 例如“返回空列表”“返回单元素列表”“返回两个元素的列表”。一般地，对每个自然数 `n`，把 `g ()` 重复 `n` 次都是一个自然变换：

```lean
def rNil {α : Type} : Reader Unit α → List α
  | ⟨_⟩ => []

def rOne {α : Type} : Reader Unit α → List α
  | ⟨g⟩ => [g ()]

def rRep (n : Nat) {α : Type} : Reader Unit α → List α
  | ⟨g⟩ => List.replicate n (g ())

theorem rRep_isNatural (n : Nat) : Natural (Reader Unit) List (rRep n) := by
  intro α β f
  funext ⟨g⟩
  show List.map f (List.replicate n (g ())) = List.replicate n (f (g ()))
  simp                -- 核心库里有 List.map_replicate 这条 simp 引理

example : rRep 0 (α := Nat) ⟨fun _ => 7⟩ = rNil ⟨fun _ => 7⟩ := rfl
example : rRep 1 (α := Nat) ⟨fun _ => 7⟩ = rOne ⟨fun _ => 7⟩ := rfl
```

由 `Unit` 组成的列表有**无穷多个**：`[]`、`[()]`、`[(), ()]`……每个长度恰好一个，所以 `List Unit` 与 `Nat` 一一对应。
按米田引理，从 `Reader Unit` 到 `List` 的自然变换也恰好是这么多——正好就是上面的 `rRep n`。

**3.** `Option Bool` 有三个元素：`none`、`some true`、`some false`。对应的三个自然变换是：

```lean
def rb₁ {α : Type} : Reader Bool α → Option α
  | ⟨_⟩ => none

def rb₂ {α : Type} : Reader Bool α → Option α
  | ⟨g⟩ => some (g true)

def rb₃ {α : Type} : Reader Bool α → Option α
  | ⟨g⟩ => some (g false)

theorem rb₁_isNatural : Natural (Reader Bool) Option rb₁ := by intro α β f; funext ⟨g⟩; rfl
theorem rb₂_isNatural : Natural (Reader Bool) Option rb₂ := by intro α β f; funext ⟨g⟩; rfl
theorem rb₃_isNatural : Natural (Reader Bool) Option rb₃ := by intro α β f; funext ⟨g⟩; rfl
```

（像 `if g true = g false then ...` 这样的写法是不行的：对任意 `α` 我们无法比较两个元素是否相等——参数性又一次限制了我们。）

**4.** 正文中 `NatTrans.hcomp` 的 `naturality` 字段就是完整的证明：它把 $G'(F' f) \circ G'\alpha_a \circ \beta_{F a}$ 依次变形为
$G'\alpha_b \circ \beta_{F b} \circ G(F f)$，其中用到了 $G'$ 保持复合、$\alpha$ 的自然性（在 $G'$ 内部）与 $\beta$ 的自然性（对态射 $F f$）。
画成图，就是两个方块左右拼接：左边是 $G'$ 作用在 $\alpha$ 的自然性方块上得到的方块，右边是 $\beta$ 在 $F f$ 上的自然性方块。

**5.** 一篇短文：

> 证明交换律需要的图，是一个三行三列的格子：最上一行是 $F'(F a)$，最下一行是 $H'(H a)$，中间横着竖着全是 $\alpha$、$\beta$、$\alpha'$、$\beta'$ 的分量与它们在函子下的像。
> 左边的等式沿“先下后右”的锯齿走，右边的等式沿“先右后下”的锯齿走。只有格子正中央那一个小方块需要真正的论证——
> 它是 $\beta'$ 在 $\alpha_a$ 上的自然性方块——其余的格子要么是函子保持复合，要么只是同一条路径换了个括号。
> 享受来自于两件事：一是发现整幅看似吓人的图里只有一处“真”内容；二是知道这个结论对**任何**范畴、任何函子都成立。
> 在 Lean 里，这份享受被浓缩为 `NatTrans.interchange` 里的三步 `calc`，其中两步是挪括号，一步是 `rw [β'.naturality]`。
> Mac Lane 说这些图是“显然的”；Lean 同意，并且给出了收据。

**6.** 取 `op` 和 `f`，验证 `contramap f ∘ predToStr` 与 `predToStr ∘ contramap f` 在一些字符串上的结果相同
（一般情形当然已经由 `predToStr_natural` 证明了）：

```lean
def op : Op Bool Int := ⟨fun x => decide (x > 0)⟩
def readInt (s : String) : Int := s.toInt?.getD 0

def lhs (s : String) : String := (Contravariant.contramap readInt (predToStr op)).run s
def rhs (s : String) : String := (predToStr (Contravariant.contramap readInt op)).run s

#guard lhs "42" == "T"
#guard rhs "42" == "T"
#guard lhs "-7" == rhs "-7"
#guard lhs "0" == rhs "0"
#guard lhs "abc" == rhs "abc"      -- 解析失败时 readInt 返回 0，两边都是 "F"
example : lhs = rhs := congrArg (fun h => fun s => (h op).run s) (predToStr_natural readInt)
```

`#guard e` 会在编译时求值布尔表达式 `e`，为假就报错——一种写在源码里、由编译器执行的单元测试。
:::

## 本章小结

- **自然变换** $\alpha : F \Rightarrow G$ 为每个对象 $a$ 挑出一个分量 $\alpha_a : F a \to G a$，并要求对每个态射 $f$，**自然性方块**交换：
  $G f \circ \alpha_a = \alpha_b \circ F f$。
- 在 Lean 中，`NatTrans` 是一个结构体：字段 `app` 是分量，字段 `naturality` 是自然性条件的**证明**。类型为 `F ⟹ G` 的值存在，本身就保证了自然性。
- 在编程中，自然变换就是多态函数 `{α : Type} → F α → G α`：“一个负责挪鸡蛋（换容器），一个负责煮鸡蛋（`map`）”，两者正交。
- 在 Haskell 中，参数性让自然性“免费”成立；但参数性是**元定理**，Lean 无法在内部证明它，借助 `Classical` 甚至能写出不自然的多态函数。
  所以在 Lean 里我们对每个函数**分别证明**自然性——通常是 `funext` + `cases`/`induction` + `rfl`。
- 例子：`safeHead : List ⟹ Option`、`reverse : List ⟹ List`（甚至是自然同构）、`length : List ⟹ Const Int`、`Reader Unit ⟹ Option` 的 `dumb` 与 `obvious`。
- 逆变函子之间的多态函数满足“反过来的”自然性条件；像 `α → α` 这样既协变又逆变的构造器根本不是函子。
- 两个自然变换可以**垂直复合**（分量逐个复合）。借助外延性引理 `NatTrans.ext`，函子与自然变换构成**函子范畴** $[\mathcal{C}, \mathcal{D}]$。
- $\mathbf{Cat}$ 是一个 **2-范畴**：对象是范畴，1-态射是函子，2-态射是自然变换。
- **水平复合** $\beta \circ \alpha : G \circ F \Rightarrow G' \circ F'$ 的分量是 $G'\alpha_a \circ \beta_{F a} = \beta_{F' a} \circ G\alpha_a$；两种复合满足**交换律**，Lean 中的证明只有一步“真”推理。
