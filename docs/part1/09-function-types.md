# 1.9 函数类型

到目前为止，我一直对函数类型的含义含糊其辞。函数类型和其他类型不一样。

拿 `Int` 来说：它就是一个整数的集合。`Bool` 是一个两元素集合。但函数类型 $a \to b$ 不止于此：
它是对象 $a$ 与 $b$ 之间**态射的集合**。任何范畴中两个对象之间的态射集合都叫 hom-集。
碰巧的是，在范畴 $\mathbf{Set}$ 中，每个 hom-集本身又是**同一个范畴**里的对象——因为它说到底也是一个**集合**。

```lean hidden
universe u v

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

end CTFP

open CTFP
```

![Set 中的 hom-集](/img/1.9/set-hom-set.jpg "在 Set 中，hom-集不过是一个集合——它本身就是 Set 的对象。")

在其他范畴里就不是这样了：那里的 hom-集位于范畴**外部**，所以它们甚至被称为**外部** hom-集（external hom-set）。

![范畴 C 中的 hom-集](/img/1.9/hom-set.jpg "在一般的范畴 C 中，hom-集 C(a, b) 是范畴外部的一个集合。")

正是 $\mathbf{Set}$ 范畴的这种“自指”性质，使函数类型显得特别。不过，至少在某些范畴中，有办法构造出**代表** hom-集的对象。
这样的对象叫**内部** hom-集（internal hom-set）。

::: info 数学小课堂：内部与外部，用 Lean 看一眼
在 Lean 里，“`Type` 中的 hom-集是 `Type` 的对象”这句话是可以直接检查的：`Nat → Bool` 和 `Nat`、`Bool` 一样，
都是 `Type` 类型的东西。

```lean
example : Type := Nat → Bool       -- 函数类型本身就是一个类型：内部 hom
example : Type := (Nat → Bool) → Nat  -- 所以还能把它当参数类型，继续构造函数类型
```

对比一个**预序**范畴：对象是自然数，从 `m` 到 `n` 有（唯一一个）态射当且仅当 `m ≤ n`。
在这个范畴里，hom-集 `Hom 3 5` 是“`3 ≤ 5` 的证明”组成的东西，它显然**不是**一个自然数——不是这个范畴的对象。
这就是外部 hom-集。
:::

## 泛构造

我们暂时忘掉“函数类型是集合”这件事，试着从零开始构造函数类型——更一般地说，构造一个内部 hom-集。
照例，我们从 $\mathbf{Set}$ 范畴中汲取灵感，但小心避免用到集合的任何特有性质，这样构造就能自动适用于其他范畴。

函数类型可以看作一种复合类型，因为它和参数类型、结果类型都有关系。我们已经见过复合类型的构造——那些涉及对象之间关系的构造。
我们用泛构造定义了[积类型与余积类型](/part1/05-products-and-coproducts)。同样的技巧也可以用来定义函数类型。
我们需要一个涉及三个对象的模式：正在构造的函数类型、参数类型和结果类型。

连接这三个类型的最显然的模式，叫**函数应用**（function application）或**求值**（evaluation）。
给定一个函数类型的候选者，叫它 $z$（注意，如果不在 $\mathbf{Set}$ 中，它只是一个普普通通的对象），以及参数类型 $a$（一个对象），
应用就把这一对映到结果类型 $b$（一个对象）。我们有三个对象，其中两个是固定的（代表参数类型和结果类型的那两个）。

我们还有应用本身，它是一个映射。怎样把这个映射纳入模式？如果允许看进对象内部，我们可以把一个函数 $f$（$z$ 的一个元素）
和一个参数 $x$（$a$ 的一个元素）配成对，映到 $f\,x$（$f$ 应用于 $x$ 的结果，是 $b$ 的一个元素）。

![Set 中的函数应用](/img/1.9/functionset.jpg "在 Set 中，我们可以从函数集合 z 里挑出一个函数 f，从集合（类型）a 里挑出一个参数 x，得到集合（类型）b 中的元素 f x。")

但与其和一个个的对子 $(f, x)$ 打交道，不如直接谈论函数类型 $z$ 与参数类型 $a$ 的整个**积**。
积 $z \times a$ 是一个对象，我们可以挑一个从它到 $b$ 的箭头 $g$ 作为我们的应用态射。在 $\mathbf{Set}$ 中，
$g$ 就是把每个对子 $(f, x)$ 映到 $f\,x$ 的那个函数。

于是模式是：两个对象 $z$ 与 $a$ 的积，经由态射 $g$ 连到另一个对象 $b$。

![泛构造的起点](/img/1.9/functionpattern.jpg "作为泛构造起点的对象与态射模式：z × a 经由 g 到达 b。")

这个模式足够具体，能用泛构造把函数类型挑出来吗？并非在每个范畴里都行，但在我们感兴趣的范畴里可以。
还有一个问题：能不能不先定义积就定义函数对象？有些范畴根本没有积，或者并非所有对象对都有积。答案是不能：
**没有积类型，就没有函数类型**。等讲到指数时我们还会回到这一点。

我们来回顾一下泛构造。我们从一个对象与态射的模式出发。这是一个不精确的查询，通常会命中大量结果。
尤其是在 $\mathbf{Set}$ 中，几乎所有东西都和所有东西相连。我们可以任取一个对象 $z$，构成它和 $a$ 的积，
总会有一个从积到 $b$ 的函数（除非 $b$ 是空集）。

这时就该祭出我们的秘密武器：**排名**。通常的做法是要求候选对象之间存在唯一的映射——一个能以某种方式把我们的构造“因子分解”的映射。
在这里，我们规定：$z$ 连同从 $z \times a$ 到 $b$ 的态射 $g$，**优于**另一个带着自己的应用 $g'$ 的 $z'$，
当且仅当存在唯一的映射 $h : z' \to z$，使得 $g'$ 的应用可以经由 $g$ 的应用分解。（提示：边看图边读这句话。）

![候选者之间的排名](/img/1.9/functionranking.jpg "在函数对象的候选者之间建立排名：z' 经由唯一的 h 映到 z。")

现在到了棘手的部分，也是我把这个泛构造推迟到现在才讲的主要原因。给定态射 $h : z' \to z$，
我们想要闭合这张图——图里既有 $z'$ 也有 $z$，它们都和 $a$ 做了积。真正需要的是：给定从 $z'$ 到 $z$ 的映射 $h$，
得到一个从 $z' \times a$ 到 $z \times a$ 的映射。而在讨论过[积的函子性](/part1/08-functoriality)之后，我们知道该怎么做了。
因为积本身是一个函子（准确地说，是一个自-双-函子），所以可以提升态射对。换句话说，我们不仅能定义对象的积，还能定义态射的积。

由于我们不碰积 $z' \times a$ 的第二个分量，我们提升的是态射对 $(h, \mathrm{id})$，其中 $\mathrm{id}$ 是 $a$ 上的恒等态射。

于是，这样就能把一个应用 $g$ 从另一个应用 $g'$ 中分解出来：

$$g' = g \circ (h \times \mathrm{id})$$

这里的关键是积在态射上的作用。在 Lean 中，$h \times \mathrm{id}$ 就是上一章见过的 `Prod.map h id`
（也就是 `Bifunctor` 的 `first h`）。

泛构造的第三步是挑出那个“普遍最优”的对象。我们把这个对象记作 $a \Rightarrow b$（把它看作某一个对象的符号名，
不要和 Haskell 里写类型类约束用的 `=>` 混淆——稍后我会讨论给它命名的其他方式）。这个对象带着自己的应用——一个从 $(a \Rightarrow b) \times a$ 到 $b$ 的态射——
我们管它叫 $\mathit{eval}$。如果任何其他函数对象候选者都能被唯一地映到 $a \Rightarrow b$，并且它的应用态射 $g$ 能经由 $\mathit{eval}$ 分解，
那么 $a \Rightarrow b$ 就是最优的。按照我们的排名，这个对象比任何其他对象都好。

![泛函数对象](/img/1.9/universalfunctionobject.jpg "泛函数对象的定义。这和上一张图是同一张图，只是现在对象 a ⇒ b 是“泛”的。")

```diagram
za: (0, 0) "z \times a"
ea: (0, 2) "(a \Rightarrow b) \times a"
b: (3, 1) "b"
z: (-2.2, 0) "z"
e: (-2.2, 2) "a \Rightarrow b"
g: za -> b "g"
hid: za -> ea "h \times \mathrm{id}" side=right dashed
ev: ea -> b "\mathit{eval}" side=right color=brand
h: z -> e "h" side=right dashed
path "直接用 g": g
path "先 h × id，再 eval": hid ev color=brand
caption: 对任何候选者 (z, g)，都存在唯一的 h，使 g = eval ∘ (h × id)。两条路径给出同样的结果。
```

正式的定义是：

::: tip 定义：函数对象
从 $a$ 到 $b$ 的**函数对象**是一个对象 $a \Rightarrow b$ 连同态射

$$\mathit{eval} : ((a \Rightarrow b) \times a) \to b$$

使得对任何其他带有态射

$$g : z \times a \to b$$

的对象 $z$，都存在**唯一**的态射

$$h : z \to (a \Rightarrow b)$$

把 $g$ 经由 $\mathit{eval}$ 分解：

$$g = \mathit{eval} \circ (h \times \mathrm{id})$$
:::

当然，在给定的范畴中，并不能保证对任意一对对象 $a$ 和 $b$ 都存在这样的对象 $a \Rightarrow b$。但在 $\mathbf{Set}$ 中它总是存在。
而且在 $\mathbf{Set}$ 中，这个对象同构于 hom-集 $\mathbf{Set}(a, b)$。

这就是为什么在 Lean 中，我们把函数类型 `a → b` 解释为范畴论中的函数对象 $a \Rightarrow b$。

我们来把这个定义逐字写进 Lean，然后**证明** `a → b` 连同普通的函数应用确实满足它。Lean 核心库没有“唯一存在” `∃!` 的记号
（那是 Mathlib 提供的），所以我们把“唯一存在”拆成两半写：**存在**一个 `h`，并且任意两个满足条件的 `h` 都**相等**。

```lean
/-- 求值：把函数应用到参数上 -/
def eval {a b : Type} : (a → b) × a → b := fun (f, x) => f x

/-- “(z, ev) 是从 a 到 b 的函数对象” -/
structure IsFunctionObject (a b z : Type) (ev : z × a → b) : Prop where
  universal : ∀ (z' : Type) (g : z' × a → b),
    -- 存在：有一个 h 能分解 g
    (∃ h : z' → z, g = ev ∘ Prod.map h id) ∧
    -- 唯一：任何两个能分解 g 的 h 都相等
    (∀ h₁ h₂ : z' → z, g = ev ∘ Prod.map h₁ id → g = ev ∘ Prod.map h₂ id → h₁ = h₂)
```

存在性的证人就是“把 `g` 的第一个参数先固定下来”的那个函数——我们把它叫作 `factorizer`（因子分解器），
下一节会看到它还有一个更响亮的名字：

```lean
def factorizer {z a b : Type} (g : z × a → b) : z → (a → b) :=
  fun z => fun a => g (z, a)

/-- 存在：factorizer g 确实分解了 g（两边按定义就相等） -/
theorem eval_factor {z a b : Type} (g : z × a → b) :
    g = eval ∘ Prod.map (factorizer g) id := rfl

/-- 唯一：任何分解了 g 的 h 都只能是 factorizer g -/
theorem factor_unique {z a b : Type} (g : z × a → b) (h : z → (a → b))
    (hg : g = eval ∘ Prod.map h id) : h = factorizer g := by
  funext z x       -- 只需证：对每个 z 和 x，h z x = g (z, x)
  rw [hg]          -- 把 g 换成 eval ∘ Prod.map h id
  rfl              -- 右边展开后正是 h z x

theorem arrow_is_function_object (a b : Type) : IsFunctionObject a b (a → b) eval where
  universal z' g := by
    refine ⟨⟨factorizer g, rfl⟩, ?_⟩
    intro h₁ h₂ e₁ e₂
    rw [factor_unique g h₁ e₁, factor_unique g h₂ e₂]
```

::: tip Lean 深入：`refine` 与 `?_`
`refine ⟨证人, ?_⟩` 的意思是：“目标的这一部分我现在就给出，`?_` 标记的那部分留作新的子目标，稍后再证。”
这里目标是一个“且”（`∧`），我们先交出存在性的证明 `⟨factorizer g, rfl⟩`，再单独处理唯一性。
`theorem ... where universal z' g := ...` 则是用 `where` 语法逐个字段地构造一个结构体（这里是一个命题的证明）。
:::

## 柯里化

我们再看一眼函数对象的所有候选者。不过这一回，把态射 $g$ 看成**两个变量** $z$ 和 $a$ 的函数：

$$g : z \times a \to b$$

作为一个从积出发的态射，它已经是最接近“两个变量的函数”的东西了。特别地，在 $\mathbf{Set}$ 中，$g$ 是一个定义在值的对子上的函数，
对子的一个分量来自集合 $z$，另一个来自集合 $a$。

另一方面，泛性质告诉我们，对每个这样的 $g$，都有唯一的态射 $h$ 把 $z$ 映到函数对象 $a \Rightarrow b$：

$$h : z \to (a \Rightarrow b)$$

在 $\mathbf{Set}$ 中，这只是说 $h$ 是一个函数，它接受一个 $z$ 类型的变量，返回一个从 $a$ 到 $b$ 的函数。这使 $h$ 成了一个高阶函数。
因此，泛构造在“两个变量的函数”与“返回函数的单变量函数”之间建立了一一对应。这个对应叫**柯里化**（currying），
$h$ 叫作 $g$ 的柯里化版本。

这个对应是一一的：因为给定任何 $g$，都有唯一的 $h$；而给定任何 $h$，你总能用这个公式重建两个参数的函数 $g$：

$$g = \mathit{eval} \circ (h \times \mathrm{id})$$

函数 $g$ 可以叫作 $h$ 的**反柯里化**（uncurried）版本。

::: info 数学小课堂：一一对应
“一一对应”（也叫**双射**）是说两堆东西可以完美地两两配对，不多也不少。要证明两个集合之间有一一对应，标准做法是给出两个方向的映射，
并证明它们**互逆**：从一边出发，去了再回来，回到原处；从另一边出发也一样。

本章会反复用到这个套路，并且每次都让 Lean 检查“回到原处”这两步。
:::

柯里化本质上就内建在 Lean 的语法里。一个返回函数的函数：

```lean no-check
a → (b → c)
```

通常被看作两个变量的函数。不加括号的签名就是这么读的：

```lean no-check
a → b → c
```

`→` 是**右结合**的，所以 `a → b → c` 就是 `a → (b → c)`，两者是**同一个类型**。我们定义多参数函数的方式也体现了这种解读。例如：

```lean
def catstr (s s' : String) : String := s ++ s'
```

同一个函数也可以写成一个返回函数（一个 lambda）的单参数函数：

```lean
def catstr' (s : String) : String → String := fun s' => s ++ s'

example : catstr = catstr' := rfl   -- 两个定义完全等价
```

这两个定义是等价的，都可以只喂一个参数进行部分应用，得到一个单参数函数，比如：

```lean
def greet : String → String := catstr "Hello "

#guard greet "Haskell Curry" == "Hello Haskell Curry"
```

::: tip Lean 深入：Lean 里的所有多参数函数本来就是柯里化的
`def catstr (s s' : String) : String` 只是 `def catstr : String → String → String := fun s => fun s' => ...` 的语法糖。
Lean 的核心理论里**只有单参数函数**；“多参数”永远是“返回函数的函数”。所以部分应用是零成本的、处处可用的——不需要任何预先设计。

（这和 Rust 很不一样，下面就会看到。）
:::

严格来说，两个变量的函数是一个接受对子（积类型）的函数：

```lean no-check
(a × b) → c
```

在两种表示之间转换是小事一桩，完成转换的两个（高阶）函数不出意料地叫作 `curry` 和 `uncurry`。
Lean 核心库里有现成的 `Function.curry` 和 `Function.uncurry`；为了看清楚，我们自己写一遍：

```lean
def curry {α β γ : Type} (f : α × β → γ) : α → β → γ := fun a b => f (a, b)

def uncurry {α β γ : Type} (f : α → β → γ) : α × β → γ := fun (a, b) => f a b
```

注意，`curry` 正是函数对象泛构造的**因子分解器**（factorizer）。写成下面这种形式就尤其明显了：

```lean
example {α β γ : Type} (g : α × β → γ) : curry g = fun a => (fun b => g (a, b)) := rfl

example {α β γ : Type} : @curry α β γ = @factorizer α β γ := rfl
```

（提醒一下：因子分解器从一个候选者出发，产出那个起分解作用的函数。）

原书说“在两种表示之间转换是小事一桩”。在 Lean 里，我们把“它们互为逆映射”证明出来：

```lean
/-- 先 curry 再 uncurry，回到原处 -/
theorem uncurry_curry {α β γ : Type} (f : α × β → γ) : uncurry (curry f) = f := by
  funext ⟨a, b⟩   -- 对每个对子 (a, b) 验证
  rfl

/-- 先 uncurry 再 curry，回到原处（这个方向连 funext 都不用） -/
theorem curry_uncurry {α β γ : Type} (f : α → β → γ) : curry (uncurry f) = f := rfl
```

有趣的是，第二个方向是 `rfl`，第一个方向却需要 `funext ⟨a, b⟩` 把对子拆开。原因是：`uncurry (curry f)` 展开后是
`fun (a, b) => f (a, b)`，它对一个**任意**的对子 `p` 计算的是 `f (p.1, p.2)`，而 Lean 需要先把 `p` 拆成 `(a, b)`，
才能看出它就是 `f p`。

在非函数式语言中，比如 C++（以及 Rust），柯里化是可能的，但并不简单。你可以把 C++ 或 Rust 中的多参数函数
看作对应于 Lean 中接受元组的函数（更让人困惑的是，C++ 里你还可以定义显式接受 `std::tuple` 的函数、变参函数，
以及接受初始化列表的函数；Rust 里则有显式接受元组的函数，以及用宏模拟的变参“函数”，比如 `println!`）。

在 C++ 中，你可以用模板 `std::bind` 部分应用一个函数。Rust 没有 `bind`，同样的事情用闭包来做。比如，给定一个接受两个字符串的函数：

```rust
pub fn catstr(s1: String, s2: String) -> String {
    s1 + &s2
}
```

你可以定义一个只接受一个字符串的函数：

```rust
pub fn catstr(s1: String, s2: String) -> String {
    s1 + &s2
}

pub fn demo() {
    // C++ 写作 auto greet = std::bind(catstr, "Hello ", _1);
    // Rust 中用闭包把第一个参数“捕获”进去
    let greet = |s: &str| catstr("Hello ".to_string(), s.to_string());
    println!("{}", greet("Haskell Curry"));
}
```

Scala 比 C++ 或 Java 更函数式一些，处在两者之间。如果你预料到正在定义的函数会被部分应用，就用多个参数列表来定义它：

```scala
def catstr(s1: String)(s2: String) = s1 + s2
```

当然，这要求库作者具备一定的远见，或者说先见之明。

::: tip Rust 视角：闭包、`impl Fn`、`Box<dyn Fn>`，以及柯里化的不便
在 Rust 中想要“柯里化风格”的函数，需要显式地**返回闭包**：

```rust
// 返回一个闭包：用 impl Fn 表示“某个实现了 Fn 的具体类型”
pub fn catstr_curried(s1: String) -> impl Fn(&str) -> String {
    move |s2| format!("{s1}{s2}") // move：把 s1 的所有权搬进闭包
}

// 通用的 curry：因为闭包要被调用多次，捕获的 A 必须能 Clone
pub fn curry<A: Clone + 'static, B: 'static, C: 'static>(
    f: impl Fn((A, B)) -> C + Clone + 'static,
) -> impl Fn(A) -> Box<dyn Fn(B) -> C> {
    move |a: A| {
        let f = f.clone();
        Box::new(move |b: B| f((a.clone(), b)))
    }
}

pub fn uncurry<A, B, C, G: Fn(B) -> C>(h: impl Fn(A) -> G) -> impl Fn((A, B)) -> C {
    move |(a, b)| h(a)(b)
}

pub fn demo() -> bool {
    let add = curry(|(x, y): (i32, i32)| x + y);
    let add_back = uncurry(|x: i32| move |y: i32| x + y);
    add(1)(2) == 3 && add_back((1, 2)) == 3 && catstr_curried("Hello ".into())("Rust") == "Hello Rust"
}
```

注意几处 Lean 里没有的摩擦：

1. **每个闭包都有自己独一无二的匿名类型**，所以返回闭包时要么写 `impl Fn(..)`（静态分发），要么装箱成 `Box<dyn Fn(..)>`（动态分发）。
2. `impl Trait` 不能嵌套出现在 `Fn` 的返回类型里，下面这种最自然的写法**编译不过**，只好在内层改用 `Box<dyn Fn>`：

   ```rust no-check
   fn add() -> impl Fn(i32) -> impl Fn(i32) -> i32 { |x| move |y| x + y }
   // error[E0562]: `impl Trait` is not allowed in the return type of `Fn` trait bounds
   ```

3. **所有权**：被捕获的值要么被 `move` 进闭包，要么被借用（于是要操心生命周期）；如果闭包要被调用多次，还得 `Clone`。

在 Lean 中，函数是不可变的值，所有这些问题都不存在——柯里化是语言的默认形态，而不是一种需要精心设计的模式。
:::

下面这个组件把柯里化画成了表格：两个参数的函数是一张二维表；柯里化就是把它按行切开，变成“一列由一维表组成的表”。

<div><Ch1_9Curry /></div>

## 指数

在数学文献中，函数对象，也就是两个对象 $a$ 与 $b$ 之间的内部 hom-对象，常被称为**指数对象**（exponential），记作 $b^{a}$。
注意参数类型在指数的位置上。这个记号初看可能有点怪，但只要想一想函数与积之间的关系，就会觉得它再合理不过。
我们已经看到，在内部 hom-对象的泛构造中必须用到积，但两者的联系比这还要深。

考虑有限类型之间的函数，最能看清这一点——所谓有限类型，就是只有有限多个值的类型，比如 `Bool`、`Char`，甚至 `Int` 或 `Float`
（它们有很多值，但毕竟是有限个）。这样的函数，至少在原则上，可以被完全**记忆化**（memoize），或者变成可供查找的数据结构。
这正是函数（态射）与函数类型（对象）之间等价关系的精髓。

例如，一个从 `Bool` 出发的（纯）函数完全由一对值确定：一个对应 `false`，一个对应 `true`。从 `Bool` 到比如说 `Int` 的所有可能函数的集合，
就是所有 `Int` 对的集合。这和积 `Int × Int` 一样；在记号上稍微发挥一下创意，也就是 `Int`²。

在 Lean 中我们可以把这个“一样”说准确：`Bool → α` 与 `α × α` **同构**。为此先定义什么是类型之间的同构：

```lean
/-- 类型 α 与 β 同构：有来回两个映射，并且互逆 -/
structure Iso (α β : Type) where
  to : α → β
  inv : β → α
  inv_to : ∀ x, inv (to x) = x
  to_inv : ∀ y, to (inv y) = y

infix:25 " ≅ " => Iso

def boolExp (α : Type) : (Bool → α) ≅ α × α where
  to f := (f false, f true)                   -- 函数 ↦ 它的“查找表”
  inv p := fun b => if b then p.2 else p.1    -- 查找表 ↦ 函数
  inv_to f := by funext b; cases b <;> rfl     -- 对 b = false / true 分别验证
  to_inv _ := rfl
```

::: tip Lean 深入：把同构写成结构体
`Iso` 的四个字段里，前两个是**数据**（两个函数），后两个是**证明**（两条互逆定律）。
构造一个 `Iso` 的值，就等于同时交出程序和它的正确性证明——这正是本章结尾“柯里-霍华德同构”的一个预演。
（Mathlib 中对应的东西叫 `Equiv`，记作 `α ≃ β`。核心库里没有，所以我们自己定义。）
:::

再举一个例子，看看 C 和 C++ 的 `char` 类型，它包含 256 个值（Lean 的 `Char` 更大，因为它代表 Unicode 字符；
和 C 的 `char` 对应的是 `UInt8`）。C 标准库中有好几个函数通常是用查表实现的。像 `isupper` 或 `isspace` 这样的函数，
就是用表格实现的，而表格等价于由 256 个布尔值组成的元组。元组是积类型，所以我们面对的是 256 个布尔值的积：
`bool × bool × bool × ... × bool`。我们从算术中知道，重复的乘积定义了幂。如果你把 `bool` 与它自己“相乘” 256 次（或者说 `char` 次），
你就得到了 `bool` 的 `char` 次幂，即 `bool`<sup>`char`</sup>。

```lean
/-- 用一张 256 格的表实现 isUpper：函数 = 数据 -/
def isUpperTable : Array Bool := Array.ofFn (n := 256) fun i => 65 ≤ i.val && i.val ≤ 90

def isUpper (c : UInt8) : Bool := isUpperTable[c.toNat]!

#guard isUpper 'A'.toNat.toUInt8
#guard !isUpper 'a'.toNat.toUInt8
```

由 256 个 `bool` 组成的元组这个类型里有多少个值？恰好 $2^{256}$ 个。这也是从 `char` 到 `bool` 的不同函数的个数，
每个函数对应一个唯一的 256 元组。类似地可以算出，从 `bool` 到 `char` 的函数个数是 $256^{2}$，依此类推。
在这些情形下，函数类型的指数记号再合理不过。

我们可以用 Lean 枚举出两个小有限类型之间的**所有**函数（每个函数表示为一张查找表），数一数：

```lean
/-- 列出从 as 到 bs 的所有函数，每个函数是一张查找表 [(a, f a), ...] -/
def allTables {α β : Type} (as : List α) (bs : List β) : List (List (α × β)) :=
  as.foldr (fun a acc => bs.flatMap fun b => acc.map fun t => (a, b) :: t) [[]]

#guard (allTables [false, true] [false, true]).length == 2 ^ 2        -- Bool → Bool：4 个
#guard (allTables [0, 1, 2] [false, true]).length == 2 ^ 3            -- 3 元素 → Bool：8 个
#guard (allTables [false, true] [0, 1, 2]).length == 3 ^ 2            -- Bool → 3 元素：9 个
#guard (allTables ([] : List Nat) [false, true]).length == 1          -- 空类型出发：1 个
#guard (allTables [0, 1] ([] : List Bool)).length == 0                -- 到空类型：0 个
```

最后两行已经预告了下文的 $a^0 = 1$：从空类型出发的函数恰好有一个——那张空表。

自己动手试试：选两个小类型，看看 $B^A$ 里到底有哪些元素，以及 `eval` 怎样从一张表里查出结果。

<div><Ch1_9Exponential /></div>

我们大概不会想把一个从 `Int` 或 `Float` 出发的函数完全记忆化。但函数与数据类型之间的这种等价，就算不总是实用，也是确实存在的。
还有一些无穷类型，比如列表、字符串或树。要急切地（eagerly）把从这些类型出发的函数记忆化，就需要无穷的存储空间。
但 Haskell 是惰性语言，所以惰性求值的（无穷）数据结构与函数之间的界线是模糊的。这种“函数与数据”的二元性，
解释了为什么 Haskell 的函数类型被等同于范畴论中的指数对象——后者更接近我们对**数据**的理解。

::: tip Lean 深入：严格求值的 Lean 里，函数就是“懒”数据
Lean 是**严格求值**的语言：一个 `List` 一定是有限的，构造它时每个元素都要算出来。所以在 Lean 里，“无穷的数据结构”通常干脆就**写成函数**：
一个无穷序列可以表示为 `Nat → α`——第 `n` 项要用时才算。这恰好是“指数对象就是数据”的另一面：`α^Nat` 就是 `α` 的无穷元组。

```lean
def squares : Nat → Nat := fun n => n * n     -- “无穷列表” 0, 1, 4, 9, ...
#guard (List.range 5).map squares == [0, 1, 4, 9, 16]
```

如果想要“算一次、记下来”的惰性值，Lean 提供了 `Thunk α`，它把一个 `Unit → α` 包起来，第一次求值后缓存结果。
:::

## 笛卡尔闭范畴

虽然我会继续用集合范畴作为类型与函数的模型，但值得一提的是，还有一个更大的范畴家族可以担此重任。
这些范畴叫**笛卡尔闭范畴**（Cartesian closed category），$\mathbf{Set}$ 只是其中一例。

一个笛卡尔闭范畴必须包含：

1. 终对象，
2. 任意一对对象的积，以及
3. 任意一对对象的指数。

如果把指数看作重复的积（可能重复无穷多次），那么可以把笛卡尔闭范畴想象成支持任意元数之积的范畴。
特别地，终对象可以看作零个对象的积——或者说一个对象的零次幂。

从计算机科学的角度看，笛卡尔闭范畴的有趣之处在于：它们为**简单类型 λ 演算**（simply typed lambda calculus）提供了模型，
而简单类型 λ 演算是所有带类型的编程语言的基础。

::: tip 补充：把“笛卡尔闭范畴”写成 Lean 类型类
上面三条要求，加上终对象、积、指数各自的泛性质，可以一字不差地写成一个类型类。对任意范畴 `C`：

```lean
class CartesianClosed (C : Type u) [Category.{u, v} C] where
  -- 1. 终对象：任何对象到它都有唯一的箭头
  one : C
  bang : (a : C) → (a ⟶ one)
  bang_unique : ∀ {a : C} (f : a ⟶ one), f = bang a
  -- 2. 积：两个投影，加上唯一的“配对”
  prod : C → C → C
  fst : {a b : C} → (prod a b ⟶ a)
  snd : {a b : C} → (prod a b ⟶ b)
  pair : {a b c : C} → (c ⟶ a) → (c ⟶ b) → (c ⟶ prod a b)
  fst_pair : ∀ {a b c : C} (f : c ⟶ a) (g : c ⟶ b), fst ⊚ pair f g = f
  snd_pair : ∀ {a b c : C} (f : c ⟶ a) (g : c ⟶ b), snd ⊚ pair f g = g
  pair_unique : ∀ {a b c : C} (h : c ⟶ prod a b), h = pair (fst ⊚ h) (snd ⊚ h)
  -- 3. 指数：eval，加上唯一的 curry（h × id 写作 pair (h ⊚ fst) snd）
  exp : C → C → C
  eval : {a b : C} → (prod (exp a b) a ⟶ b)
  curry : {a b z : C} → (prod z a ⟶ b) → (z ⟶ exp a b)
  eval_curry : ∀ {a b z : C} (g : prod z a ⟶ b),
    eval ⊚ pair (curry g ⊚ fst) snd = g
  curry_unique : ∀ {a b z : C} (g : prod z a ⟶ b) (h : z ⟶ exp a b),
    eval ⊚ pair (h ⊚ fst) snd = g → h = curry g
```

`Type` 是一个笛卡尔闭范畴：终对象是 `Unit`，积是 `×`，指数是 `→`。所有定律都几乎是按定义成立的：

```lean
instance : CartesianClosed Type where
  one := Unit
  bang _ := fun _ => ()
  bang_unique _ := rfl          -- 到 Unit 的函数只有一个：结构体的 η 规则让 Lean 直接看出来
  prod a b := a × b
  fst := Prod.fst
  snd := Prod.snd
  pair f g := fun x => (f x, g x)
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl
  pair_unique _ := rfl
  exp a b := a → b
  eval := fun p => p.1 p.2
  curry g := fun z a => g (z, a)
  eval_curry _ := rfl
  curry_unique g h e := by
    subst e                     -- 用假设 e 把 g 替换掉
    rfl
```

`subst e` 的意思是：既然假设 `e` 说 `g` 等于某个表达式，就把目标中所有的 `g` 都换成那个表达式。
:::

终对象和积都有对偶：始对象与余积。一个同时支持这两者、并且积对余积满足分配律的笛卡尔闭范畴

$$a \times (b + c) = a \times b + a \times c$$
$$(b + c) \times a = b \times a + c \times a$$

叫作**双笛卡尔闭范畴**（bicartesian closed category）。下一节我们会看到，双笛卡尔闭范畴（$\mathbf{Set}$ 是其中的典范）有一些有趣的性质。

分配律在 Lean 中同样是一个可以构造出来的同构（这里的“等号”照例理解为“同构”）：

```lean
def distrib (a b c : Type) : a × (b ⊕ c) ≅ (a × b) ⊕ (a × c) where
  to
    | (x, .inl y) => .inl (x, y)
    | (x, .inr z) => .inr (x, z)
  inv
    | .inl (x, y) => (x, .inl y)
    | .inr (x, z) => (x, .inr z)
  inv_to := by intro ⟨x, s⟩; cases s <;> rfl
  to_inv := by intro s; cases s <;> rfl
```

## 指数与代数数据类型

把函数类型解释成指数，与代数数据类型的体系配合得天衣无缝。原来，中学代数里那些关于数字 0 和 1、和、积、指数的基本恒等式，
在任何双笛卡尔闭范畴中几乎原封不动地成立——分别对应于始对象与终对象、余积、积和指数。
我们还没有证明它们所需的工具（比如伴随或**米田引理**（Yoneda lemma）），但我还是把它们列在这里，作为宝贵直觉的来源。

> 原书在这里只列出恒等式。在 Lean 里，我们可以对 `Type` 这个具体的双笛卡尔闭范畴**逐个构造出同构并证明**。
> 一般范畴中的证明要等到学了伴随和米田引理之后。

### 零次幂

$$a^{0} = 1$$

在范畴论的解释中，我们把 0 换成始对象，把 1 换成终对象，把等号换成同构。指数就是内部 hom-对象。
这个特定的指数代表从始对象到任意对象 $a$ 的态射集合。根据始对象的定义，这样的态射恰好有一个，所以 hom-集 $\mathcal{C}(0, a)$ 是一个单元素集合。
单元素集合是 $\mathbf{Set}$ 中的终对象，所以这个恒等式在 $\mathbf{Set}$ 中显然成立。我们现在说的是：它在任何双笛卡尔闭范畴中都成立。

在 Lean 中，我们把 0 换成 `Empty`，1 换成单元类型 `Unit`，指数换成函数类型。断言是：从 `Empty` 到任意类型 `a` 的函数集合，
等价于单元类型——一个单元素集合。换句话说，`Empty → a` 的函数只有一个。我们以前见过这个函数，它叫 `absurd`（Lean 中是 `Empty.elim`）。

```lean
def zerothPower (a : Type) : (Empty → a) ≅ Unit where
  to _ := ()
  inv _ := fun e => nomatch e     -- 对一个不可能存在的值做模式匹配：零个分支
  inv_to f := by funext e; cases e -- 要对每个 e : Empty 验证……而 Empty 没有值，cases 直接结束
  to_inv _ := rfl
```

这在 Haskell 里有点微妙，原因有二。一是 Haskell 中其实没有真正无人居住的类型——每个类型都包含“永不终止的计算的结果”，也就是底（⊥）。
二是 `absurd` 的所有实现都是等价的，因为无论它们做什么，谁都无法执行它们：没有任何值可以传给 `absurd`。
（如果你设法传给它一个永不终止的计算，它也永远不会返回！）

::: tip Lean 深入：在 Lean 里，这两个“微妙之处”都消失了
1. Lean 是全函数语言，没有处处都在的 ⊥：`Empty` 是**真正**空的类型，`def x : Empty := ...` 根本写不出来
   （Lean 会拒绝不终止的定义，除非你标上 `partial`，而 `partial def` 要求结果类型非空——恰好排除了 `Empty`）。
2. “`absurd` 的所有实现都等价”在 Lean 里是一条可以证明的**定理**，上面 `inv_to` 的证明就是它：
   任何两个 `Empty → a` 的函数都相等，因为要逐点比较时，根本没有点可比。
:::

### 一的幂

$$1^{a} = 1$$

这个恒等式在 $\mathbf{Set}$ 中解释时，就是在重述终对象的定义：从任何对象到终对象都有唯一的态射。
一般地，从 $a$ 到终对象的内部 hom-对象同构于终对象本身。

在 Lean 中，从任何类型 `a` 到 `Unit` 的函数只有一个。我们以前见过这个函数——它叫 `unit`。
你也可以把它看成部分应用于 `()` 的函数 `Function.const`：

```lean
def unit {a : Type} : a → Unit := Function.const a ()

def powerOfOne (a : Type) : (a → Unit) ≅ Unit where
  to _ := ()
  inv _ := unit
  inv_to _ := rfl   -- 任何 a → Unit 的函数按定义就等于 unit（Unit 的 η 规则）
  to_inv _ := rfl
```

### 一次幂

$$a^{1} = a$$

这是在重述之前的观察：从终对象出发的态射可以用来挑出对象 `a` 的“元素”。这样的态射的集合同构于对象本身。
在 $\mathbf{Set}$ 和 Lean 中，这个同构存在于集合 `a` 的元素与挑出这些元素的函数 `Unit → a` 之间。

```lean
def firstPower (a : Type) : (Unit → a) ≅ a where
  to f := f ()          -- 一个“挑选函数” ↦ 它挑出的那个元素
  inv x := fun _ => x   -- 一个元素 ↦ 总是挑它的函数
  inv_to _ := rfl
  to_inv _ := rfl
```

### 和的指数

$$a^{b+c} = a^{b} \times a^{c}$$

在范畴论中，这是说从两个对象的余积出发的指数，同构于两个指数的积。在编程中，这个代数恒等式有非常实际的解释：
**从两个类型之和出发的函数，等价于一对分别从各个类型出发的函数**。这正是我们在为和类型定义函数时所用的分情况讨论。
与其写一个带 `match` 的函数定义，我们通常把它拆成两个（或更多）分支，每个分支处理一个构造器。
例如，考虑一个从和类型 `Int ⊕ Float` 出发的函数：

```lean no-check
f : Int ⊕ Float → String
```

它可以定义为一对函数，分别从 `Int` 和 `Float` 出发：

```lean
def f : Int ⊕ Float → String
  | .inl n => if n < 0 then "Negative int" else "Positive int"
  | .inr x => if x < 0.0 then "Negative double" else "Positive double"

#guard f (.inl (-3)) == "Negative int"
#guard f (.inr 2.5) == "Positive double"
```

这里 `n` 是一个 `Int`，`x` 是一个 `Float`。两个分支就是“那一对函数”。把这句话写成同构：

```lean
def expOfSum (a b c : Type) : (b ⊕ c → a) ≅ (b → a) × (c → a) where
  to f := (f ∘ Sum.inl, f ∘ Sum.inr)   -- 一个函数 ↦ 它的两个分支
  inv p := Sum.elim p.1 p.2            -- 两个分支 ↦ 一个分情况的函数
  inv_to f := by funext x; cases x <;> rfl
  to_inv _ := rfl
```

### 指数的指数

$$(a^{b})^{c} = a^{b \times c}$$

这只是纯粹用指数对象来表达柯里化：返回函数的函数，等价于从积出发的函数（两个参数的函数）。

```lean
def expOfExp (a b c : Type) : (c → (b → a)) ≅ (b × c → a) where
  to f := fun (y, z) => f z y
  inv g := fun z y => g (y, z)
  inv_to _ := rfl
  to_inv g := by funext ⟨y, z⟩; rfl
```

（`b × c` 中的顺序和柯里化时参数的顺序相反，所以这里顺手交换了一下——积是可交换的，`b × c ≅ c × b`。）

### 积上的指数

$$(a \times b)^{c} = a^{c} \times b^{c}$$

在编程中：返回一个对子的函数，等价于一对函数，各自产出对子的一个分量。

```lean
def expOverProd (a b c : Type) : (c → a × b) ≅ (c → a) × (c → b) where
  to f := (Prod.fst ∘ f, Prod.snd ∘ f)
  inv p := fun z => (p.1 z, p.2 z)
  inv_to _ := rfl
  to_inv _ := rfl
```

这些简单的中学代数恒等式竟然能提升到范畴论，并在函数式编程中有实际用途，真是令人惊叹。

::: tip 补充：数一数，验证这些恒等式
对有限类型，同构意味着元素个数相等。用前面的 `allTables` 可以直接数出来，比如 $2^{1+2} = 2^1 \times 2^2 = 8$、
$(2^2)^3 = 2^{2 \times 3} = 64$：

```lean
#guard (allTables [0, 1, 2] [true, false]).length ==
  (allTables [0] [true, false]).length * (allTables [1, 2] [true, false]).length
#guard (allTables [0, 1, 2] (allTables [true, false] ["x", "y"])).length ==
  (allTables [(0, true), (0, false), (1, true), (1, false), (2, true), (2, false)] ["x", "y"]).length
```

当然，计数只是同构的“影子”：两个类型元素个数相等，只能说明**存在**某个同构；而上面构造的那些同构是**具体的、自然的**，
它们不依赖于类型里有多少元素。
:::

## 柯里-霍华德同构

我已经提过逻辑与代数数据类型之间的对应。`Empty` 类型和单元类型 `Unit` 分别对应假与真。积类型与和类型分别对应逻辑合取 $\wedge$（与）
和析取 $\vee$（或）。在这个体系中，我们刚刚定义的函数类型对应于逻辑蕴涵 $\Rightarrow$。换句话说，类型 `a → b` 可以读作“如果 a 则 b”。

根据**柯里-霍华德同构**（Curry–Howard isomorphism），每个类型都可以解释为一个命题——一个可能为真也可能为假的陈述或判断。
如果类型有居民（inhabited），命题就被认为是真的；如果没有，就是假的。特别地，如果一个逻辑蕴涵对应的函数类型有居民，
也就是存在一个该类型的函数，那么这个蕴涵就为真。因此，一个函数的实现就是一个定理的证明。**写程序就等价于证明定理。**我们来看几个例子。

::: tip Lean 深入：`Prop`——让柯里-霍华德变得具体
在 Haskell 里，柯里-霍华德同构是一种“看待程序的方式”。在 Lean 里，它是语言的**地基**：Lean 有一个专门的宇宙 `Prop` 存放命题，
而一个命题的证明，就是这个命题（作为类型）的一个**值**。你在本书里写过的每一个 `theorem`，都是一个程序。

| 逻辑 | Lean 中的命题（`Prop`） | Lean 中的数据类型（`Type`） |
|---|---|---|
| 假 | `False` | `Empty` |
| 真 | `True` | `Unit` |
| $p \wedge q$（与） | `p ∧ q` | `α × β` |
| $p \vee q$（或） | `p ∨ q` | `α ⊕ β` |
| $p \Rightarrow q$（蕴涵） | `p → q` | `α → β` |
| $\neg p$（非） | `¬p`，即 `p → False` | `α → Empty` |

`Prop` 和 `Type` 的区别只有一点：`Prop` 是**证明无关**的——同一个命题的任意两个证明被视为相等。
我们只关心命题“有没有证明”，不关心“是哪个证明”；而对数据，我们当然关心“是哪个值”。
:::

拿我们在定义函数对象时引入的函数 `eval` 来说。它的签名是：

```lean no-check
eval : (α → β) × α → β
```

它接受一个由函数和它的参数组成的对子，产出相应类型的结果。它是态射

$$\mathit{eval} : (a \Rightarrow b) \times a \to b$$

的实现，而这个态射定义了函数类型 $a \Rightarrow b$（或者说指数对象 $b^{a}$）。我们用柯里-霍华德同构把这个签名翻译成逻辑命题：

$$((a \Rightarrow b) \wedge a) \Rightarrow b$$

这句话可以这样读：如果“由 $a$ 可推出 $b$”为真，并且 $a$ 为真，那么 $b$ 一定为真。这在直觉上完全说得通，
自古以来就以**肯定前件**（modus ponens）之名为人所知。我们可以通过实现这个函数来证明这个定理：

```lean
-- 数据版本：eval 本身
def eval' {α β : Type} : (α → β) × α → β := fun (f, x) => f x

-- 逻辑版本：肯定前件。证明“长得”和上面的程序一模一样
theorem modusPonens {a b : Prop} : (a → b) ∧ a → b := fun ⟨f, x⟩ => f x
```

如果你给我一个对子，其中有一个接受 `a`、返回 `b` 的函数 `f`，以及一个 `a` 类型的具体值 `x`，我只要把 `f` 应用到 `x` 上，
就能产出一个 `b` 类型的具体值。实现了这个函数，我就证明了类型 `(a → b) × a → b` 有居民。所以肯定前件在我们的逻辑里为真。

那么一个明显错误的命题呢？比如：如果 $a$ 或 $b$ 为真，那么 $a$ 一定为真。

$$a \vee b \Rightarrow a$$

这显然不对，因为你可以挑一个为假的 $a$ 和一个为真的 $b$，这就是反例。

用柯里-霍华德同构把这个命题映成函数签名，我们得到：

```lean no-check
def bad : α ⊕ β → α
  | .inl a => a
  | .inr b => ?_    -- 手上只有 b : β，要交出一个 α——做不到
```

无论你怎么努力，都实现不了这个函数——如果调用时传进来的是 `inr` 值，你就没法产出 `a` 类型的值。（记住，我们说的是**纯**函数。）

在 Lean 里，我们还能更进一步：不只是“写不出来”，而是**证明**它不可能对所有命题成立——把上面那个反例写成证明：

```lean
theorem not_or_imp_left : ¬ (∀ a b : Prop, a ∨ b → a) := by
  intro h                          -- 假设它对所有 a b 都成立
  exact h False True (Or.inr trivial)  -- 取 a := False, b := True，就推出了 False
```

最后，我们来看 `absurd` 函数的含义：

```lean no-check
absurd : Empty → α
```

考虑到 `Empty` 翻译为假，我们得到：

$$\mathit{false} \Rightarrow a$$

从谬误可以推出任何东西（**爆炸原理**，ex falso quodlibet）。在 Lean 中，它在 `Type` 和 `Prop` 两边各有一个现成的版本：

```lean
example (α : Type) : Empty → α := Empty.elim
example (p : Prop) : False → p := False.elim
-- 核心库里的 absurd：同时拿到 p 和 ¬p，就能得到任何东西
example (p q : Prop) (hp : p) (hnp : ¬p) : q := absurd hp hnp
```

下面是这个命题（函数）的一种可能的证明（实现）。原书用 Haskell 写成 `absurd (Void a) = absurd a`，
其中 `Void` 定义为 `newtype Void = Void Void`。在 Lean 中，同样的定义可以一字不差地写出来
（核心库里已经有一个不相干的 `Void`，所以我们放进命名空间）：

```lean
namespace Hs

/-- 要构造一个 Void，你得先有一个 Void —— 所以永远构造不出来 -/
inductive Void where
  | mk : Void → Void

/-- 结构递归：每次调用都剥掉一层 mk。因为不存在“最后一层”，这个函数永远不会被真正调用 -/
def Void.absurd {α : Sort _} : Void → α
  | .mk v => Void.absurd v

/-- 由此可以证明 Void 确实是空的 -/
theorem Void.empty : Void → False := fun v => v.absurd

end Hs
```

一如既往，`Void` 类型很微妙。这个定义使得构造一个值成为不可能，因为要构造一个，你得先提供一个。因此，`absurd` 函数永远无法被调用。

::: tip Lean 深入：为什么 Lean 接受这个递归？
Lean 要求所有函数都终止。`Void.absurd` 每次递归调用的参数 `v` 都是输入 `.mk v` 的**真子结构**，这叫**结构递归**，Lean 能自动确认它终止。
有趣的是，对于 Haskell，这个定义能编译只是因为 Haskell 不检查终止性；而在 Lean 里，它能编译是因为它**真的**是一个良基的定义——
恰恰是它的“良基”保证了 `Void` 没有任何值：如果有，就会有一条无穷下降的 `mk` 链。
:::

柯里-霍华德的对应远不止这几例。下面几对“程序 / 证明”，你会发现它们的写法几乎一字不差：

```lean
-- 交换律：积 / 合取
def prodSwap {α β : Type} : α × β → β × α := fun (a, b) => (b, a)
theorem and_swap' {p q : Prop} : p ∧ q → q ∧ p := fun ⟨hp, hq⟩ => ⟨hq, hp⟩

-- 交换律：和 / 析取
def sumSwap {α β : Type} : α ⊕ β → β ⊕ α
  | .inl a => .inr a
  | .inr b => .inl b
theorem or_swap' {p q : Prop} : p ∨ q → q ∨ p
  | .inl hp => .inr hp
  | .inr hq => .inl hq

-- 柯里化 = 逻辑中的“输出律”：(p ∧ q → r) ↔ (p → q → r)
theorem curry_logic {p q r : Prop} : (p ∧ q → r) ↔ (p → q → r) :=
  ⟨fun h hp hq => h ⟨hp, hq⟩, fun h ⟨hp, hq⟩ => h hp hq⟩

-- 双重否定引入：p → ¬¬p，也就是 p → ((p → False) → False)
theorem dni {p : Prop} : p → ¬¬p := fun hp hnp => hnp hp
```

::: warning 易错点：反过来的 `¬¬p → p` 写不出来
`dni` 的逆命题 `¬¬p → p`（双重否定消去）在经典逻辑中成立，却**无法**用一个纯程序实现：给你一个“如果你敢说 `p` 是假的，我就能推出矛盾”的函数，
你仍然变不出一个 `p` 的证据来。柯里-霍华德对应的逻辑是**直觉主义逻辑**（构造性逻辑）。Lean 通过公理 `Classical.choice`
额外提供了经典逻辑（`Classical.byContradiction`），但这样得到的证明不再对应可以运行的程序。
:::

这些例子都很有意思，但柯里-霍华德同构有实际用途吗？在日常编程中大概没有。但有一些编程语言，比如 Agda 和 Rocq（原名 Coq），
利用柯里-霍华德同构来证明定理。——还有你正在学的 **Lean**：数学家们用它建立了庞大的形式化数学库 Mathlib，
其中的每一个定理都是一个通过了类型检查的程序。

计算机不仅在帮助数学家完成工作，还在革新数学的根基。这个领域最新的热门研究课题叫**同伦类型论**（Homotopy Type Theory），它是从类型论中生长出来的。
它里面满是布尔值、整数、积与余积、函数类型等等。而且，仿佛是为了打消任何疑虑，这个理论正在 Rocq 和 Agda 中被形式化。
计算机正在以不止一种方式改变世界。

## 参考文献

1. Ralf Hinze, Daniel W. H. James, [Reason Isomorphically!](http://www.cs.ox.ac.uk/ralf.hinze/publications/WGP10.pdf)。
   这篇论文用范畴论证明了本章提到的所有那些中学代数恒等式。

## 挑战（本书补充）

原书本章没有挑战题。下面几道是本书补充的练习，用来巩固本章的 Lean 技巧。

1. 构造同构 `(c → b → a) ≅ (b → c → a)`。用指数记号，它说的是 $(a^b)^c = (a^c)^b$。它对应中学代数里的哪条规律？
2. 用柯里-霍华德同构证明“逆否命题”：`(p → q) → (¬q → ¬p)`。然后写出它的**数据版本**：一个类型为 `(α → β) → (β → Empty) → (α → Empty)` 的函数。
   你会发现它就是上一章的哪个操作？
3. 构造同构 `(Unit ⊕ Unit → a) ≅ a × a`，并解释它和 `boolExp` 的关系。
4. 证明从 `Empty` 出发的任意两个函数相等（不借助 `zerothPower`），以及到 `Unit` 的任意两个函数相等。
5. 在 Rust 中写一个三参数版本的 `curry3`，把 `Fn((A, B, C)) -> D` 变成 `A -> B -> C -> D` 风格的闭包。体会一下需要多少 `Clone` 和 `Box`。

::: details 参考答案 1
```lean
def flipIso (a b c : Type) : (c → b → a) ≅ (b → c → a) where
  to := flip
  inv := flip
  inv_to _ := rfl
  to_inv _ := rfl
```

它对应 $(a^b)^c = a^{b \times c} = a^{c \times b} = (a^c)^b$，也就是乘法交换律 $b \times c = c \times b$ 在指数上的体现。
程序上，它就是 `flip`：交换两个参数的顺序。
:::

::: details 参考答案 2
```lean
theorem contrapositive {p q : Prop} : (p → q) → (¬q → ¬p) :=
  fun f nq hp => nq (f hp)

def contraData {α β : Type} : (α → β) → (β → Empty) → (α → Empty) :=
  fun f k => k ∘ f
```

数据版本正是上一章的 `contramap`：`(· → Empty)` 是一个逆变函子，`contramap f k = k ∘ f`。逆否命题就是“否定”这个逆变函子作用在蕴涵上！
:::

::: details 参考答案 3
```lean
def twoExp (a : Type) : (Unit ⊕ Unit → a) ≅ a × a where
  to f := (f (.inl ()), f (.inr ()))
  inv p := fun s => match s with
    | .inl _ => p.1
    | .inr _ => p.2
  inv_to f := by funext s; rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl
  to_inv _ := rfl
```

`Unit ⊕ Unit` 就是 $1 + 1 = 2$，和 `Bool` 同构。于是这个同构就是 $a^{1+1} = a^1 \times a^1 = a \times a$——
把“和的指数”和“一次幂”两条规律连起来用，`boolExp` 是它在 `Bool` 上的版本。
:::

::: details 参考答案 4
```lean
theorem empty_funext {a : Type} (f g : Empty → a) : f = g := by
  funext e
  cases e

theorem unit_funext {a : Type} (f g : a → Unit) : f = g := by
  funext x
  rfl
```

第一个用 `cases e` 处理“不存在的输入”。第二个在 `funext x` 之后，目标是 `f x = g x`：两边都是 `Unit` 的值，
而 `Unit` 的任何值都按定义等于 `()`（结构体的 η 规则），所以 `rfl` 就够了。
（注意不能省掉 `funext`：Lean 不会主动把两个**变量** `f`、`g` 展开成 `fun x => f x` 再比较。前面 `powerOfOne` 里能直接 `rfl`，
是因为一边已经是 lambda `fun _ => ()` 了。）这两条分别是“始对象出发的态射唯一”和“到终对象的态射唯一”。
:::

::: details 参考答案 5
```rust
pub fn curry3<A, B, C, D>(
    f: impl Fn((A, B, C)) -> D + Clone + 'static,
) -> impl Fn(A) -> Box<dyn Fn(B) -> Box<dyn Fn(C) -> D>>
where
    A: Clone + 'static,
    B: Clone + 'static,
    C: 'static,
    D: 'static,
{
    move |a: A| {
        let f = f.clone();
        Box::new(move |b: B| {
            let f = f.clone();
            let a = a.clone();
            Box::new(move |c: C| f((a.clone(), b.clone(), c)))
        })
    }
}

pub fn demo() -> i32 {
    let add3 = curry3(|(x, y, z): (i32, i32, i32)| x + y + z);
    add3(1)(2)(3)
}
```

每多一层，就多一个 `Box<dyn Fn>`、多一轮 `clone`。对比 Lean：`fun a b c => f (a, b, c)`，完事。
:::

## 本章小结

- 在 $\mathbf{Set}$（以及 Lean 的 `Type`）中，hom-集本身就是一个对象，这就是函数类型；在一般范畴中 hom-集是外部的，
  能代表它的对象叫**内部 hom**。
- **函数对象** $a \Rightarrow b$ 由泛构造定义：它带着 $\mathit{eval} : (a \Rightarrow b) \times a \to b$，任何候选者 $(z, g)$ 都经由唯一的
  $h$ 分解为 $g = \mathit{eval} \circ (h \times \mathrm{id})$。构造中用到了积在态射上的作用——积的函子性。没有积就没有函数对象。
- 这个泛性质就是**柯里化**：$z \times a \to b$ 与 $z \to (a \Rightarrow b)$ 一一对应；`curry` 就是因子分解器。我们在 Lean 中证明了
  `curry` 与 `uncurry` 互逆，也证明了 `a → b` 确实是函数对象。
- Lean 的多参数函数天生就是柯里化的；Rust 中要靠返回闭包（`impl Fn` / `Box<dyn Fn>`）模拟，并受所有权与类型系统的限制。
- 函数对象也叫**指数** $b^a$：对有限类型，$b^a$ 恰好有 $|b|^{|a|}$ 个元素，函数就是查找表——函数即数据。
- **笛卡尔闭范畴**有终对象、积与指数，是简单类型 λ 演算的模型；再加上始对象、余积与分配律就是**双笛卡尔闭范畴**。
- 中学代数恒等式 $a^0 = 1$、$1^a = 1$、$a^1 = a$、$a^{b+c} = a^b \times a^c$、$(a^b)^c = a^{b \times c}$、$(a \times b)^c = a^c \times b^c$
  都是类型同构，我们在 Lean 中逐个构造并证明了它们。
- **柯里-霍华德同构**：类型即命题，程序即证明；`→` 是蕴涵，`×`/`∧` 是与，`⊕`/`∨` 是或，`Empty`/`False` 是假。
  `eval` 就是肯定前件，`absurd` 就是爆炸原理。在 Lean 里，这不是比喻，而是你每天写证明时的日常。
