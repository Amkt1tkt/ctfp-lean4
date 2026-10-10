# 3.10 端与余端

关于范畴中的态射，我们可以有很多种直觉。但有一点大家都会同意：如果从对象 $a$ 到对象 $b$ 有一个态射，那这两个对象之间就有某种“关系”。在某种意义上，态射就是这个关系的**证明**。在偏序范畴里这一点再清楚不过：在那里，态射**就是**关系本身（$a \le b$）。一般来说，同一对对象之间的同一个关系可以有很多份“证明”，这些证明组成的集合，就是我们所说的 hom-集（态射集合）。

当我们让两个对象变动起来，就得到了一个映射：把一对对象映到一个“证明的集合”。这个映射是函子性的——对第一个参数逆变，对第二个参数协变。我们可以把它看成是在整个范畴的对象之间建立了一种**全局的关系**。描述这种关系的，就是 hom-函子：

$$\mathcal{C}(-, =) : \mathcal{C}^{op} \times \mathcal{C} \to \mathbf{Set}$$

一般而言，任何长成这样的函子，都可以解释成在某个范畴的对象之间建立了一种关系。关系也可以跨越两个不同的范畴 $\mathcal{C}$ 和 $\mathcal{D}$。描述这种跨范畴关系的函子具有如下签名，它叫作**剖函子**（profunctor）：

$$p : \mathcal{D}^{op} \times \mathcal{C} \to \mathbf{Set}$$

数学家们管它叫“从 $\mathcal{C}$ 到 $\mathcal{D}$ 的剖函子”（注意方向是反过来的），并用一个带斜杠的箭头来表示它：

$$\mathcal{C} \nrightarrow \mathcal{D}$$

你可以把剖函子想成 $\mathcal{C}$ 的对象与 $\mathcal{D}$ 的对象之间的一种**带证明的关系**（proof-relevant relation），集合里的每个元素都代表这个关系的一份证明。只要 $p\ a\ b$ 是空集，就说明 $a$ 和 $b$ 之间没有关系。记住，关系不必是对称的。

::: info 数学小课堂：什么是“带证明的关系”
普通的关系只回答“是”或“否”：比如“$3 \le 5$ 吗？”——是。数学上，一个关系 $R$ 就是一个“对子 $(a, b)$ 满足不满足”的判断。

**带证明的关系**更进一步：它不只说“是”，还把“为什么是”的所有证据都交给你。例如，“城市 $a$ 能开车到城市 $b$”可以只是一句“能”；但带证明的版本会给出**所有路线**组成的集合。路线集合为空，就说明到不了；路线有好几条，就说明“能到”有好几种证明。

hom-集正是这样：$\mathcal{C}(a, b)$ 是“$a$ 关联到 $b$”的全部证据（全部态射）。在 Lean 里，这对应着一个返回 `Type` 的两参数函数 `p : Type → Type → Type`：`p a b` 里的每个值，就是一份证据。（对比：返回 `Prop` 的关系 `a → b → Prop` 只关心“有没有”，不在乎“有几份”。）
:::

另一个有用的直觉，是把“自函子是容器”的想法推广一下。类型为 $p\ a\ b$ 的剖函子值，可以看成一个装着 $b$ 的容器，这些 $b$ 是用 $a$ 类型的元素作为**键**来索引的。特别地，hom-剖函子的一个元素就是一个从 $a$ 到 $b$ 的函数——给它一个键 $a$，它就交出一个 $b$。

### 它在程序里长什么样

在 Haskell 里，剖函子被定义为一个两参数的类型构造器 `p`，外加一个叫 `dimap` 的方法：它把一对函数提升上去，其中第一个函数是“反着走”的。在 Lean 里我们照样写一个类型类（为了避免和其他章节冲突，本章所有定义都放在命名空间 `Ch310` 里）：

```lean
namespace Ch310

/-- 剖函子：对第一个参数逆变、对第二个参数协变的两参数类型构造器。 -/
class Profunctor (p : Type → Type → Type) where
  dimap : {a b c d : Type} → (c → a) → (b → d) → p a b → p c d

export Profunctor (dimap)
```

读一下 `dimap` 的签名：给我一个 `c → a`（注意方向：从**新键**翻译回**旧键**）、一个 `b → d`（修改容器里装的东西），我就能把 `p a b` 变成 `p c d`。

::: tip Lean 深入：`export` 与隐式参数
`{a b c d : Type}` 是**隐式参数**：调用 `dimap f g x` 时，Lean 会从 `f`、`g`、`x` 的类型里自己推断出 `a b c d`，不用你写。
`export Profunctor (dimap)` 的作用是：以后可以直接写 `dimap`，而不必写全名 `Profunctor.dimap`。
:::

和 Lean 的 `LawfulFunctor` 一样，我们把剖函子必须满足的**函子定律**单独写成一个类：`dimap` 必须把一对恒等函数送到恒等函数，并且保持复合。这里 `: Prop` 表示这个类里只有“命题”（定律），没有数据。

```lean
class LawfulProfunctor (p : Type → Type → Type) [Profunctor p] : Prop where
  dimap_id : ∀ {a b : Type} (x : p a b), dimap id id x = x
  dimap_comp : ∀ {a b c d c' d' : Type} (f : c → a) (g : b → d) (f' : c' → c) (g' : d → d')
    (x : p a b), dimap f' g' (dimap f g x) = dimap (f ∘ f') (g' ∘ g) x
```

注意 `dimap_comp` 里第一个参数的复合顺序 `f ∘ f'` 是“反”的——这正是“逆变”二字的含义。

最典型的剖函子就是函数类型本身——hom-剖函子。我们给它起个名字 `Fun`，`dimap` 就是“先前复合、再后复合”：

```lean
/-- hom-剖函子：`Fun a b` 就是 `a → b`。 -/
def Fun (a b : Type) : Type := a → b

instance : Profunctor Fun where
  dimap f g h := g ∘ h ∘ f

instance : LawfulProfunctor Fun where
  dimap_id _ := rfl          -- id ∘ h ∘ id 在定义上就是 h
  dimap_comp _ _ _ _ _ := rfl -- 函数复合的结合律在定义上就成立
```

另一个常见的例子，是“带效果的函数” `a → F b`（Haskell 的 profunctors 库里叫 `Star`）。只要 `F` 是函子，它就是剖函子；只要 `F` 守法，它就守法：

```lean
def Star (F : Type → Type) (a b : Type) : Type := a → F b

instance [Functor F] : Profunctor (Star F) where
  dimap f g h := Functor.map g ∘ h ∘ f
```

::: details 证明 `Star F` 满足剖函子定律
```lean
instance [Functor F] [LawfulFunctor F] : LawfulProfunctor (Star F) where
  dimap_id h := by
    funext x                     -- 两个函数相等 ⇐ 逐点相等
    simp [dimap, id_map]         -- map id = id
    rfl
  dimap_comp f g f' g' h := by
    funext x
    show g' <$> (g <$> h (f (f' x))) = (g' ∘ g) <$> h (f (f' x))
    rw [comp_map]                -- map (g' ∘ g) = map g' ∘ map g
```
:::

::: tip Rust 视角
Rust 没有高阶类型（不能把 `p` 这种“两参数类型构造器”当参数传），所以写不出一个通用的 `Profunctor` trait。但对函数这一个具体的剖函子，`dimap` 一目了然：先用 `f` 把新输入翻译成旧输入，跑原来的 `h`，再用 `g` 加工输出。

```rust
pub fn dimap<A, B, C, D>(
    f: impl Fn(C) -> A,
    g: impl Fn(B) -> D,
    h: impl Fn(A) -> B,
) -> impl Fn(C) -> D {
    move |c| g(h(f(c)))
}
```

这在 Rust 里很常见：给一个现成的处理函数“套个适配器”——前面加一层输入转换，后面加一层输出转换。
:::

剖函子的函子性告诉我们：只要有一份“`a` 关联到 `b`”的证明，并且有一个从 `c` 到 `a` 的态射、一个从 `b` 到 `d` 的态射，我们就能得到一份“`c` 关联到 `d`”的证明。或者，用容器的说法：第一个函数把新的键翻译成旧的键，第二个函数修改容器里的内容。

### 对角线元素

对于只在一个范畴内部活动的剖函子，我们可以从形如 $p\ a\ a$ 的**对角线元素**里榨取相当多的信息。只要有一对态射 $b \to a$ 和 $a \to c$，我们就能证明 $b$ 关联到 $c$。更妙的是，单单一个态射就足以让我们从对角线走到“非对角线”的位置。比如，若有态射 $f : a \to b$，我们可以提升 $\langle f, \mathrm{id}_b \rangle$，从 $p\ b\ b$ 走到 $p\ a\ b$；也可以提升 $\langle \mathrm{id}_a, f \rangle$，从 $p\ a\ a$ 走到 $p\ a\ b$：

```lean
variable {p : Type → Type → Type} [Profunctor p]

/-- 只动第一个参数（逆变的那个）。 -/
def lmap (f : c → a) : p a b → p c b := dimap f id
/-- 只动第二个参数（协变的那个）。 -/
def rmap (g : b → d) : p a b → p a d := dimap id g

-- 从对角线 p b b 走到 p a b：
example (f : a → b) (pbb : p b b) : p a b := dimap f id pbb
-- 从对角线 p a a 走到 p a b：
example (f : a → b) (paa : p a a) : p a b := dimap id f paa
```

画成图，就是两个对角线元素从两边汇聚到同一个非对角线位置：

```diagram
paa: (0, 0) "p\,a\,a"
pab: (2, 0) "p\,a\,b"
pbb: (4, 0) "p\,b\,b"
r: paa -> pab "p\,\mathrm{id}_a\,f"
l: pbb -> pab "p\,f\,\mathrm{id}_b" side=right
caption: 给定 f : a → b，两个对角线位置 p a a 和 p b b 都能走到同一个非对角线位置 p a b。这个“汇聚”是本章一切的起点。
```

::: tip Lean 深入：`variable`
`variable {p : Type → Type → Type} [Profunctor p]` 声明了一组“公共参数”：此后的定义只要用到 `p`，Lean 就自动把 `{p}` 和 `[Profunctor p]` 加为它的参数。这能省掉大量重复的签名。
:::

## 双自然变换

既然剖函子是函子，我们当然可以用标准的方式定义它们之间的自然变换。但很多时候，只需定义两个剖函子**对角线元素**之间的映射就够了。

**先看类型。** 在程序里，这样的变换就是一个多态函数：

```lean no-check
app : (a : Type) → p a a → q a a
```

**再看定义。** 设 $p$ 和 $q$ 是函子范畴 $[\mathcal{C}^{op} \times \mathcal{C}, \mathbf{Set}]$ 中的两个剖函子。一族态射

$$\alpha_a : p\ a\ a \to q\ a\ a$$

如果对任意 $f : a \to b$ 都让下面的图交换，就叫作一个**双自然变换**（dinatural transformation）。这个交换条件反映了“从对角线元素走到非对角线元素”的两种方式：

![双自然性条件（原书手绘）](/img/3.10/end.jpg "双自然变换的交换条件：从 p b a 出发，左右两条路径最终到达同一个 q a b。")

用本书的交换图重画一遍，并让你亲眼看看两条路径：

```diagram
pba: (1.5, 0) "p\,b\,a"
paa: (0.5, 1) "p\,a\,a"
pbb: (2.5, 1) "p\,b\,b"
qaa: (0.5, 2.2) "q\,a\,a"
qbb: (2.5, 2.2) "q\,b\,b"
qab: (1.5, 3.2) "q\,a\,b"
l1: pba -> paa "p\,f\,\mathrm{id}_a" side=right
r1: pba -> pbb "p\,\mathrm{id}_b\,f"
aa: paa -> qaa "\alpha_a" side=right
ab: pbb -> qbb "\alpha_b"
l2: qaa -> qab "q\,\mathrm{id}_a\,f" side=right
r2: qbb -> qab "q\,f\,\mathrm{id}_b"
path "左路：先 lmap f，再 α_a，再 rmap f": l1 aa l2
path "右路：先 rmap f，再 α_b，再 lmap f": r1 ab r2 color=green
caption: 双自然性“六边形”：从 p b a 出发，无论走左路还是右路，都必须得到同一个 q a b 中的元素。
```

**再看 Lean。** 把上面的图原样写成一个字段：

```lean
structure Dinat (p q : Type → Type → Type) [Profunctor p] [Profunctor q] where
  app : (a : Type) → p a a → q a a
  dinat : ∀ {a b : Type} (f : a → b),
    (dimap id f ∘ app a ∘ dimap f id : p b a → q a b)
      = dimap f id ∘ app b ∘ dimap id f
```

**最后看例子。** 取 $p$ 为函数 `a → b`，$q$ 为“列表上的函数” `List a → List b`。那么 `List.map` 就是一个从 $p$ 到 $q$ 的双自然变换：它把对角线上的 `h : a → a` 送到 `List.map h : List a → List a`。

```lean
def ListFun (a b : Type) : Type := List a → List b

instance : Profunctor ListFun where
  dimap f g h := List.map g ∘ h ∘ List.map f

def mapDinat : Dinat Fun ListFun where
  app _ h := List.map h
  dinat f := by
    funext h xs
    -- 左路：map f ∘ map (h ∘ f)；右路：map (f ∘ h) ∘ map f
    -- 两者都等于 map (f ∘ h ∘ f)
    show List.map f (List.map (id ∘ h ∘ f) (List.map id xs))
      = List.map id (List.map (f ∘ h ∘ id) (List.map f xs))
    simp [List.map_map]
    intros; rfl
```

注意，双自然性严格弱于自然性。如果 $\alpha$ 本来就是 $[\mathcal{C}^{op} \times \mathcal{C}, \mathbf{Set}]$ 里的一个自然变换，那么上面的六边形可以由两个自然性方块加上一个函子性条件（剖函子 $q$ 保持复合）拼出来：

![自然变换蕴含双自然性（原书手绘）](/img/3.10/end-1.jpg "中间的竖线是自然变换在非对角线位置的分量 α_ba；两个自然性方块与 q 的函子性一起，拼出了外圈的双自然性六边形。")

还要注意：$[\mathcal{C}^{op} \times \mathcal{C}, \mathbf{Set}]$ 中的自然变换 $\alpha$，其分量由**一对**对象来索引：$\alpha_{a b}$。而双自然变换的分量只由**一个**对象来索引，因为它只映射两个剖函子的对角线元素。

::: details Lean 证明：自然变换限制到对角线上，就是双自然变换
剖函子之间的自然变换，分量带两个下标，并且和 `dimap` 交换。把它限制到对角线（`app a a`）上，就得到一个双自然变换——证明正是上面那张图：两次用自然性，再用一次 `dimap_comp`。

```lean
structure ProNat (p q : Type → Type → Type) [Profunctor p] [Profunctor q] where
  app : (a b : Type) → p a b → q a b
  naturality : ∀ {a b c d : Type} (f : c → a) (g : b → d) (x : p a b),
    app c d (dimap f g x) = dimap f g (app a b x)

def ProNat.diag {q : Type → Type → Type} [Profunctor q] [LawfulProfunctor p] [LawfulProfunctor q]
    (α : ProNat p q) : Dinat p q where
  app a := α.app a a
  dinat {a b} f := by
    funext x
    show dimap id f (α.app a a (dimap f id x)) = dimap f id (α.app b b (dimap id f x))
    -- 用自然性把 α 移到最外面，再用 dimap_comp 把两次 dimap 合成一次
    rw [← α.naturality, ← α.naturality, LawfulProfunctor.dimap_comp, LawfulProfunctor.dimap_comp]
    rfl  -- 两边都是 α.app a b (dimap f f x)
```
:::

## 端

现在，我们准备从范畴论的“代数”迈向可以称为“微积分”的部分了。端（以及余端）的演算，从传统微积分那里借来了一些想法，甚至借来了一些记号。具体来说，余端可以理解成一种无穷求和或者积分，而端则类似于一个无穷乘积。我们甚至会遇到某种很像狄拉克 δ 函数的东西。

端是极限的推广：把函子换成剖函子。我们不再用锥（cone），而用**楔**（wedge）。

**先看类型。** 楔的底由剖函子 $p$ 的对角线元素组成。楔的顶点是一个对象（这里是一个集合，因为我们讨论的是取值于 $\mathbf{Set}$ 的剖函子），楔的侧边是一族把顶点映到底部各个集合的函数。你可以把这一族函数看成**一个**多态函数——一个在返回类型上多态的函数：

$$\alpha : \forall a\ .\ \mathit{apex} \to p\ a\ a$$

在 Lean 里，它的类型就是 `(a : Type) → apex → p a a`。

**再看定义。** 和锥不同，楔的底部没有任何连接各个顶点的函数。不过前面我们看到，对 $\mathcal{C}$ 中任意的态射 $f : a \to b$，都可以把 $p\ a\ a$ 和 $p\ b\ b$ 连到同一个集合 $p\ a\ b$ 上。于是我们要求下面这个图交换：

![楔条件（原书手绘）](/img/3.10/end-2.jpg "楔条件：从顶点出发，经 α_a 再 p id_a f，与经 α_b 再 p f id_b，必须到达 p a b 中的同一个元素。")

```diagram
apex: (1, 0) "\mathit{apex}"
paa: (0, 1.2) "p\,a\,a"
pbb: (2, 1.2) "p\,b\,b"
pab: (1, 2.4) "p\,a\,b"
aa: apex -> paa "\alpha_a" side=right
ab: apex -> pbb "\alpha_b"
la: paa -> pab "p\,\mathrm{id}_a\,f" side=right
lb: pbb -> pab "p\,f\,\mathrm{id}_b"
path "经过 p a a": aa la
path "经过 p b b": ab lb color=green
caption: 楔的“菱形”条件。底部没有连接 p a a 与 p b b 的箭头，但二者可以在 p a b 处“会师”。
```

这叫作**楔条件**（wedge condition）。写成公式就是：

$$p\ \mathrm{id}_a\ f \circ \alpha_a = p\ f\ \mathrm{id}_b \circ \alpha_b$$

在 Lean 里，我们把楔定义成一个结构体：一族函数 `α`，加上楔条件 `wedge`。（这里的 `Type u` 让楔的顶点可以住在任意宇宙里，下文会解释为什么需要这样。）

```lean
universe u v

/-- 以 `e` 为顶点、以 `p` 的对角线为底的楔。 -/
structure Wedge (p : Type → Type → Type) [Profunctor p] (e : Type u) where
  α : (a : Type) → e → p a a
  wedge : ∀ {a b : Type} (f : a → b), dimap id f ∘ α a = dimap f id ∘ α b
```

**动手看看。** 下面这个小工具在一个只有两个对象 $A$、$B$ 和一个态射 $f : A \to B$ 的小范畴里，让你亲手挑选楔的两条侧边 $\alpha_A$、$\alpha_B$，然后看两条路径在 $p(A, B)$ 处能否会师：

<div class="ch-widget-slot">
<Ch3_10WedgeExplorer />
</div>

现在我们可以进行泛构造了：把 $p$ 的**端**定义为**泛楔**——一个集合 $e$ 连同一族函数 $\pi$，使得对任何其他以 $e'$ 为顶点、以 $\alpha$ 为侧边的楔，都存在唯一的函数 $h : e' \to e$ 让所有三角形交换：

$$\pi_a \circ h = \alpha_a$$

![端的泛性质（原书手绘）](/img/3.10/end-21.jpg "任何楔（顶点 e′，侧边 α）都通过唯一的 h 分解到泛楔（顶点 e，侧边 π）上。")

```diagram
e': (1, 0) "e'"
e: (1, 1.3) "e"
paa: (0, 2.6) "p\,a\,a"
pbb: (2, 2.6) "p\,b\,b"
h: e' --> e "h"
aa: e' -> paa "\alpha_a" bend=35 side=right
ab: e' -> pbb "\alpha_b" bend=-35
pa: e -> paa "\pi_a"
pb: e -> pbb "\pi_b" side=right
path "直接走 α_a": aa
path "先 h 再 π_a": h pa color=green
caption: 泛性质：对每个 a，α_a = π_a ∘ h。h 是唯一的（虚线表示“唯一存在”）。
```

端的符号是积分号，“积分变量”写在下标位置：

$$\int_c p\ c\ c$$

$\pi$ 的各个分量叫作端的**投影映射**（projection maps）：

$$\pi_a : \int_c p\ c\ c \to p\ a\ a$$

注意，如果 $\mathcal{C}$ 是一个离散范畴（除了恒等态射之外没有别的态射），那么端就是 $p$ 在整个 $\mathcal{C}$ 上所有对角线元素的乘积——因为没有非恒等的 $f$，楔条件什么也没要求。稍后我会告诉你，在更一般的情形下，端与这个乘积之间通过一个等化子联系在一起。

### 在 Lean 中，端就是带楔条件的多态函数

在 Haskell 里，端的公式直接翻译成全称量词：

```lean no-check
-- Haskell：forall a. p a a
-- Lean：
(a : Type) → p a a
```

严格地说，这只是 $p$ 所有对角线元素的乘积。但在 Haskell 里，楔条件会因为[参数性](https://bartoszmilewski.com/2017/04/11/profunctor-parametricity/)（parametricity）而自动满足：对任意函数 $f : a \to b$，楔条件读作

```lean no-check
dimap f id ∘ π b = dimap id f ∘ π a     -- 两边的类型都是 p a b
```

其中 `π` 是多态投影：给它一个 `∀ a, p a a`，它就挑出 `c` 这个分量（Haskell 里类型推导会自动挑选正确的分量；Lean 里就是把类型 `c` 作为参数传进去）。

而在 Lean 里，**楔条件不会白送给你**（原因见下面的“易错点”）。所以我们老老实实地把它写进端的定义：

```lean
/-- 端 ∫_c p c c：一个多态值 `run`，外加楔条件。 -/
@[ext]
structure End (p : Type → Type → Type) [Profunctor p] : Type 1 where
  run : (a : Type) → p a a
  wedge : ∀ {a b : Type} (f : a → b), dimap id f (run a) = dimap f id (run b)
```

::: tip Lean 深入：为什么 `End p : Type 1`？——宇宙
Lean 里的类型也分“大小”。`Nat`、`Bool`、`List Nat` 这些普通类型住在 `Type`（也叫 `Type 0`）里；而 `Type` 本身是一个类型，它住在 `Type 1` 里；`Type 1` 又住在 `Type 2` 里……这一层层的 `Type n` 叫作**宇宙**（universe）。之所以要分层，是为了避免类似“所有集合的集合”的悖论（Girard 悖论）。

`run : (a : Type) → p a a` 对**所有** `a : Type` 量化。一个“对所有类型都给出一个值”的东西，必须比任何单个类型都“大”，所以 Lean 规定它住在 `Type 1`。这和数学上的情况一致：端是对 $\mathcal{C}$ 的所有对象做的“乘积”，要保证结果仍是一个（小）集合，数学家要求 $\mathcal{C}$ 是小范畴；而 `Type` 不是小的，于是结果升了一级。

Haskell 没有这个区分（它的类型系统是“非直谓”的，`forall a. p a a` 仍然是一个普通类型），所以 Haskell 程序员很少想到这个问题。Lean 把它摆在了明面上——这也解释了为什么我们的 `Wedge` 要允许顶点 `e : Type u` 住在任意宇宙：泛楔的顶点 `End p` 本身就住在 `Type 1` 里。
:::

::: warning 易错点：Lean 里没有“免费定理”
Haskell 能白拿楔条件，靠的是**参数性**：一个类型为 `forall a. a -> a` 的 Haskell 函数，不可能“偷看” `a` 究竟是什么类型，因此它只能是恒等函数（忽略 ⊥）。

Lean 的类型论允许经典逻辑（排中律、选择公理），而这恰好和参数性冲突。在 Lean 里，我们可以写出一个“偷看类型”的多态函数：遇到 `Nat` 就返回 `0`，遇到别的类型就原样返回。

```lean
open Classical in
noncomputable def weird : (a : Type) → a → a :=
  fun a x => if h : a = Nat then cast h.symm (0 : Nat) else x

theorem weird_nat (n : Nat) : weird Nat n = 0 := by
  simp [weird]

-- weird 不是自然的：取 f = Nat.succ，两条路径分别得到 1 和 0
theorem weird_not_natural :
    ¬ ∀ (a b : Type) (f : a → b) (x : a), f (weird a x) = weird b (f x) := by
  intro h
  have := h Nat Nat Nat.succ 0   -- succ (weird Nat 0) = weird Nat (succ 0)
  rw [weird_nat, weird_nat] at this  -- 化简成 succ 0 = 0
  contradiction
```

（`noncomputable` 是因为它用到了经典逻辑的判定，Lean 无法为它生成可执行代码。）

所以在 Lean 里，“多态函数”和“满足楔条件的多态函数”是两回事。我们的 `End` 结构体把楔条件作为一个字段带着走——这正是数学上端的真实定义。Lean 让原书中那个“因为参数性所以自动成立”的隐藏条件现了原形。
:::

现在可以把泛性质完整地写出来并证明。`End.π` 是投影；`End.lift` 把任何楔分解到端上；`fac` 说三角形交换；`uniq` 说这样的分解是唯一的：

```lean
namespace End

/-- 投影 π_a : ∫_c p c c → p a a -/
def π (a : Type) (e : End p) : p a a := e.run a

/-- 端本身就是一个楔（以 End p 为顶点、π 为侧边）。 -/
def universal : Wedge p (End p) where
  α := π
  wedge f := by funext e; exact e.wedge f

/-- 任何楔都唯一地分解到端上：这就是 h : e' → ∫_c p c c。 -/
def lift {e' : Type u} (w : Wedge p e') : e' → End p :=
  fun x => { run := fun a => w.α a x, wedge := fun f => congrFun (w.wedge f) x }

/-- 三角形交换：π_a ∘ h = α_a。 -/
theorem fac {e' : Type u} (w : Wedge p e') (a : Type) : π a ∘ lift w = w.α a := rfl

/-- 唯一性：任何让三角形交换的 h 都等于 lift w。 -/
theorem uniq {e' : Type u} (w : Wedge p e') (h : e' → End p)
    (hh : ∀ a, π a ∘ h = w.α a) : h = lift w := by
  funext x
  ext a                      -- 两个 End 相等 ⇐ 它们的 run 相等（楔条件是命题，自动相等）
  exact congrFun (hh a) x

end End
```

::: tip Lean 深入：`@[ext]` 与证明无关性
`End` 的定义前加了 `@[ext]`，Lean 就自动生成一条“外延性”引理：两个 `End p` 的值只要 `run` 字段相等就相等。为什么不用管 `wedge` 字段？因为它是一个**命题**的证明，而 Lean 规定同一命题的任意两个证明在定义上相等（**证明无关性**，proof irrelevance）。这样，`ext a` 就把目标化成“对每个 `a`，`run a` 相等”。
:::

### 一个例子：$\int_c (c \to c)$ 只有一个元素

让我们看看楔条件的威力。取 $p$ 为 hom-剖函子 `Fun`，它的端是 $\int_c \mathcal{C}(c, c)$——所有“对每个类型都给出一个 `c → c`、并满足楔条件”的东西。在 Haskell 里，参数性告诉我们只有 `id` 一个；在 Lean 里，`weird` 这样的函数存在，但它满足不了楔条件。我们可以**证明**端里只有一个元素：

```lean
structure Iso (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

infix:25 " ≅ " => Iso

/-- ∫_c (c → c) ≅ Unit：满足楔条件的多态函数 ∀ c, c → c 只有恒等函数。 -/
def endId : End Fun ≅ Unit where
  toFun _ := ()
  invFun _ := ⟨fun _ => id, fun _ => rfl⟩
  left_inv e := by
    ext a
    funext x
    -- 关键：对“常值函数” f : Unit → a, f _ = x 使用楔条件，
    -- 得到 f (e.run Unit ()) = e.run a (f ())，即 x = e.run a x
    have h := congrFun (e.wedge (fun (_ : Unit) => x)) ()
    exact h
  right_inv _ := rfl
```

这里我们顺手定义了一个小结构 `Iso`（同构）：一对互逆的函数。本章和下一章会反复用它来陈述“两个东西本质上一样”。`Sort u` 是比 `Type u` 更一般的写法：`Sort (u+1)` 就是 `Type u`，而 `Sort 0` 是命题的宇宙 `Prop`。用 `Sort` 可以让 `Iso` 同时适用于类型和命题，两边还可以住在不同的宇宙（`u` 与 `v`）。

证明的思路值得细品：要知道 `e.run a` 在任意 `x : a` 上做什么，就找一个能“指向” `x` 的函数——常值函数 `fun _ : Unit => x`——然后用楔条件把 `e.run a x` 和 `e.run Unit ()` 联系起来。`Unit` 只有一个元素，`e.run Unit ()` 别无选择只能是 `()`，于是 `e.run a x = x`。这个“用一个单点指向任意元素”的招数，是米田引理的雏形。

### 用双自然变换来看楔

我们曾经把锥的所有交换条件打包成一个自然变换；同样，我们也可以把所有楔条件打包成一个双自然变换。为此需要把常函子 $\Delta_c$ 推广成**常剖函子**：它把所有的对象对都映到同一个对象 $c$，把所有的态射对都映到 $c$ 上的恒等态射。于是，楔就是一个从这个常剖函子到 $p$ 的双自然变换。确实，一旦意识到 $\Delta_c$ 把所有态射都提升成同一个恒等函数，双自然性的六边形就缩成了楔的菱形。

端也可以针对 $\mathbf{Set}$ 以外的目标范畴来定义，但这里我们只考虑取值于 $\mathbf{Set}$ 的剖函子以及它们的端。

## 端作为等化子

端定义中的交换条件可以用等化子来表达。首先定义两个函数（这里我用代码来写，因为在这种情形下数学记号反而不太友好）。它们对应楔条件中汇聚到一处的两条分支：

```lean
def lambda (paa : p a a) (f : a → b) : p a b := dimap id f paa
def rho (pbb : p b b) (f : a → b) : p a b := dimap f id pbb
```

两个函数都把剖函子 `p` 的对角线元素映到如下类型的多态函数：

```lean
def ProdP (p : Type → Type → Type) : Type 1 := (a b : Type) → (a → b) → p a b
```

这两个函数的类型不同。不过，只要组成一个巨大的乘积类型，把 `p` 的所有对角线元素收集在一起，就能统一它们的类型：

```lean
def DiaProd (p : Type → Type → Type) : Type 1 := (a : Type) → p a a
```

函数 `lambda` 和 `rho` 诱导出从这个乘积类型出发的两个映射：

```lean
def lambdaP : DiaProd p → ProdP p := fun e _ _ f => lambda (e _) f
def rhoP : DiaProd p → ProdP p := fun e _ _ f => rho (e _) f
```

`p` 的端就是这两个函数的等化子。回忆一下，等化子挑出使两个函数相等的最大子集。在这里，它从所有对角线元素的乘积中，挑出那些让楔图交换的元素。

::: info 数学小课堂：等化子就是“满足方程的子集”
给两个函数 $f, g : X \to Y$，它们的**等化子**是 $X$ 的子集 $\{x \in X \mid f(x) = g(x)\}$，连同把它嵌入 $X$ 的包含映射。比如 $X = Y = \mathbb{Z}$、$f(x) = x^2$、$g(x) = x$，等化子就是 $\{0, 1\}$。

在 Lean 里，“满足某个性质的子集”就是**子类型** `{ x : X // P x }`：它的值是一对 `⟨x, 证明 P x⟩`。所以 $\mathbf{Set}$ 中的等化子就是 `{ x : X // f x = g x }`。
:::

在 Lean 里，我们可以把“端就是等化子”写成一个同构，而且证明几乎是平凡的——两边装的是同样的数据和同样的条件：

```lean
def endAsEqualizer : End p ≅ { e : DiaProd p // lambdaP e = rhoP e } where
  toFun e := ⟨e.run, by funext a b f; exact e.wedge f⟩
  invFun s := ⟨s.1, fun {a b} f => congrFun (congrFun (congrFun s.2 a) b) f⟩
  left_inv _ := rfl
  right_inv _ := rfl
```

## 自然变换作为端

端最重要的例子，是自然变换的集合。两个函子 $F$ 和 $G$ 之间的自然变换，是从形如 $\mathcal{C}(F a, G a)$ 的 hom-集中挑出的一族态射。如果没有自然性条件，自然变换的集合就只是所有这些 hom-集的乘积。事实上，在 Haskell 里它就是：

```lean no-check
-- Haskell：forall a. f a -> g a
(a : Type) → F a → G a
```

在 Haskell 里这行得通，是因为自然性可以从参数性推出来。但出了 Haskell（包括在 Lean 里！），并不是这些 hom-集上的每一个“对角线截面”都能给出自然变换。不过请注意，映射

$$\langle a, b \rangle \to \mathcal{C}(F a, G b)$$

是一个剖函子，所以研究它的端是有意义的：

```lean
def HomFG (F G : Type → Type) (a b : Type) : Type := F a → G b

instance [Functor F] [Functor G] : Profunctor (HomFG F G) where
  dimap f g h := Functor.map g ∘ h ∘ Functor.map f
```

它的楔条件是：

![自然变换的楔条件（原书手绘）](/img/3.10/end1.jpg "∫_c C(F c, G c) 的楔条件：两条路径分别是“先 τ_a 再 G f”与“先 F f 再 τ_b”。")

```diagram
top: (1.2, 0) "\int_c \mathcal{C}(F c, G c)"
a: (0, 1.3) "\mathcal{C}(F a, G a)"
b: (2.4, 1.3) "\mathcal{C}(F b, G b)"
ab: (1.2, 2.6) "\mathcal{C}(F a, G b)"
pa: top -> a "\pi_a" side=right
pb: top -> b "\pi_b"
la: a -> ab ""
lb: b -> ab ""
laL: (0.05, 2.15) "\mathcal{C}(\mathrm{id}_a, G f)"
lbL: (2.35, 2.15) "\mathcal{C}(F f, \mathrm{id}_b)"
path "G f ∘ τ_a": pa la
path "τ_b ∘ F f": pb lb color=green
caption: 自然变换作为端：楔条件恰好就是自然性条件。
```

我们从集合 $\int_c \mathcal{C}(F c, G c)$ 中随便挑一个元素。两个投影把它映到某个变换的两个分量，记作：

$$\tau_a : F a \to G a \qquad \tau_b : F b \to G b$$

在左边的分支里，我们用 hom-函子提升一对态射 $\langle \mathrm{id}_a, G f \rangle$。你也许还记得，这种提升就是同时进行前复合与后复合。作用在 $\tau_a$ 上，提升后的这对态射给出：

$$G f \circ \tau_a \circ \mathrm{id}_a$$

图的另一条分支给出：

$$\mathrm{id}_b \circ \tau_b \circ F f$$

楔条件要求两者相等——而这恰恰就是 $\tau$ 的自然性条件。

在 Lean 里，我们可以把这段论证写成一个同构：`HomFG F G` 的端，与我们熟悉的“带自然性条件的自然变换”结构一一对应。

```lean
structure NatT (F G : Type → Type) [Functor F] [Functor G] where
  app : (a : Type) → F a → G a
  naturality : ∀ {a b : Type} (f : a → b), Functor.map f ∘ app a = app b ∘ Functor.map f

def natAsEnd (F G : Type → Type) [Functor F] [Functor G] [LawfulFunctor F] [LawfulFunctor G] :
    End (HomFG F G) ≅ NatT F G where
  toFun e := {
    app := e.run
    naturality := fun {a b} f => by
      -- 楔条件：map f ∘ run a ∘ map id = map id ∘ run b ∘ map f
      funext x
      have hx := congrFun (e.wedge f) x
      simpa [dimap, Function.comp, id_map] using hx }   -- 用 map id = id 化简，就是自然性
  invFun τ := {
    run := τ.app
    wedge := fun {a b} f => by
      funext x
      have hx := congrFun (τ.naturality f) x
      simpa [dimap, Function.comp, id_map] using hx }
  left_inv _ := rfl
  right_inv _ := rfl
```

::: tip Lean 深入：`simpa ... using h`
`simpa [引理们] using h` 的意思是：用这些引理同时化简假设 `h` 和目标，然后用化简后的 `h` 关闭目标。在这里，楔条件和自然性条件只差几个 `map id`，化简掉之后就一模一样了。
:::

## 余端

不出所料，端的对偶叫作**余端**（coend）。它是由楔的对偶——**余楔**（cowedge）——构造出来的。（cowedge 念作 co-wedge，可别念成 cow-edge“牛的边缘”。）

![一头很有“棱角”的牛（原书手绘）](/img/3.10/end-31.jpg "一头很有棱角（edgy）的牛？——cow-edge 的谐音梗。")

余端的符号是积分号，“积分变量”写在上标位置：

$$\int^c p\ c\ c$$

**先看类型。** 端与乘积有关，余端则与余积（也就是和）有关——在这一点上它很像积分，因为积分就是求和的极限。余端不再有投影，而是有从剖函子的对角线元素**进入**余端的内射。如果没有余楔条件，我们就可以说：$p$ 的余端要么是 $p\ a\ a$，要么是 $p\ b\ b$，要么是 $p\ c\ c$，等等。或者说：**存在**某个 $a$，使得余端就是集合 $p\ a\ a$。端定义中的全称量词，在余端这里变成了存在量词。

所以，用伪代码来写，余端是：

```lean no-check
exists a. p a a      -- 伪代码
```

Haskell 编码存在量词的标准做法，是使用带全称量化的数据构造器：`data Coend p = forall a. Coend (p a a)`。背后的逻辑是：无论选了哪个 `a`，都应该能用 $p\ a\ a$ 这一族类型中任意一个类型的值来构造余端。

在 Lean 里，存在类型有一个更直接的写法：**依值对**（Sigma 类型）`(a : Type) × p a a`。它的值是一对 `⟨a, x⟩`：第一个分量是某个类型 `a`，第二个分量是 `p a a` 中的值。这正是“所有对角线元素的和”：

```lean
/-- 所有对角线元素的不交并：Σ a, p a a。 -/
abbrev DiagSum (p : Type → Type → Type) : Type 1 := (a : Type) × p a a
```

::: tip Rust 视角：`dyn Trait` 就是存在类型
在 Rust 里，`Box<dyn Trait>` 的意思是“**存在**某个实现了 `Trait` 的具体类型，值就是它，但我不告诉你它是谁”。这正是存在量词。下面的 `Box<dyn Observe>` 封装了“某个类型 `A` 的值，以及把 `A` 变成字符串的方法”——也就是 $\exists a.\ a \times (a \to \text{String})$：

```rust
pub trait Observe {
    fn observe(&self) -> String;
}

struct Packed<A, F: Fn(&A) -> String> {
    value: A,
    view: F,
}

impl<A, F: Fn(&A) -> String> Observe for Packed<A, F> {
    fn observe(&self) -> String {
        (self.view)(&self.value)
    }
}

pub fn pack<A: 'static>(value: A, view: impl Fn(&A) -> String + 'static) -> Box<dyn Observe> {
    Box::new(Packed { value, view })
}

pub fn demo() -> Vec<String> {
    let xs: Vec<Box<dyn Observe>> = vec![pack(42_i32, |n| n.to_string()), pack("42", |s| s.to_string())];
    xs.iter().map(|x| x.observe()).collect() // 两个都是 "42"
}
```

拿到一个 `Box<dyn Observe>`，你**唯一**能做的就是调用 `observe`。所以，封装着 `42_i32` 的那个和封装着 `"42"` 的那个，在外界看来毫无区别——它们“应该被视为相等”。余端的商，就是把这种“外界区分不了”正式化。
:::

就像端可以用等化子来定义一样，余端也可以用**余等化子**（coequalizer）来描述。所有余楔条件可以这样概括：取所有可能的函数 $b \to a$ 上 $p\ a\ b$ 的一个巨大余积。在 Haskell 里，这表达为一个存在类型 `data SumP p = forall a b. SumP (b -> a) (p a b)`；在 Lean 里，它同样是一个 Sigma 类型：

```lean
/-- Σ a b, (b → a) × p a b -/
def SumP (p : Type → Type → Type) : Type 1 := (a : Type) × (b : Type) × (b → a) × p a b
```

求值这个和类型有两种方式：用 `dimap` 提升那个函数，再作用到剖函子上：

```lean
def lambdaS : SumP p → DiagSum p := fun ⟨_, b, f, pab⟩ => ⟨b, dimap f id pab⟩
def rhoS : SumP p → DiagSum p := fun ⟨a, _, f, pab⟩ => ⟨a, dimap id f pab⟩
```

其中 `DiagSum p` 是 $p$ 的对角线元素之和（上面已经定义过）。

这两个函数的余等化子就是余端。余等化子是从 `DiagSum p` 中，把“对同一个参数分别用 `lambdaS` 和 `rhoS` 得到的值”**认同**（identify）起来得到的。在这里，参数是一对东西：一个函数 $b \to a$，加上 $p\ a\ b$ 中的一个元素。用 `lambdaS` 和 `rhoS` 作用之后，得到 `DiagSum p` 中两个可能不同的值。在余端里，这两个值被认同为一个，于是余楔条件自动满足。

把集合中“有关系的”元素认同起来，这个过程的正式名称是**取商**（taking a quotient）。要定义商，我们需要一个**等价关系**（equivalence relation）$\sim$，也就是一个满足自反性、对称性、传递性的关系：

$$a \sim a$$
$$\text{若}\ a \sim b\ \text{则}\ b \sim a$$
$$\text{若}\ a \sim b\ \text{且}\ b \sim c\ \text{则}\ a \sim c$$

这样的关系会把集合切分成若干个**等价类**，每个类由互相关联的元素组成。从每个类中挑一个代表，就组成了**商集**。一个经典的例子是有理数的定义：有理数被定义为整数对，其中第二个数非零，等价关系是：

$$(a, b) \sim (c, d)\ \text{当且仅当}\ a \cdot d = b \cdot c$$

很容易验证这是一个等价关系。整数对 $(a, b)$ 被解释为分数 $\frac{a}{b}$，分子分母有公因子的分数被认同在一起。一个有理数，就是这样的分数构成的一个等价类。

::: info 数学小课堂：商——“把看作相同的东西粘在一起”
想象一个钟表：13 点和 1 点在表盘上是同一个位置。数学上，这就是把整数按“相差 12 的倍数”这个等价关系取商，得到 12 个等价类。

- **自反**：每个东西和自己等价。
- **对称**：$a$ 等价于 $b$，那 $b$ 也等价于 $a$。
- **传递**：$a$ 等价于 $b$、$b$ 等价于 $c$，那 $a$ 等价于 $c$。

**商集**的元素是等价类。在商集上定义函数，有一个必须遵守的规矩：函数值不能依赖于你挑了类里的哪个代表——这叫**良定义**（well-defined）。比如“分数的分子”就不是有理数上良定义的函数（$\frac12$ 与 $\frac24$ 是同一个有理数，分子却不同），而“是否为零”就是良定义的。
:::

Lean 内建了取商的机制：`Quot r`。给它任何一个关系 `r : α → α → Prop`，`Quot r` 就是把 `r` 关联的元素粘在一起后得到的类型。它附带三件工具：

- `Quot.mk r x`：把 `x` 放进它的等价类；
- `Quot.sound : r x y → Quot.mk r x = Quot.mk r y`：有关系的元素，在商里**真的相等**；
- `Quot.lift f h`：在商上定义函数，前提是你证明了 `f` 尊重 `r`（即良定义性 `h`）。

下面用它把原书的有理数例子真的写出来。传递性的证明要用到一点代数：两边同乘 $y$ 的分母再消去。

```lean
namespace Rational

structure Frac where
  num : Int
  den : Int
  den_ne : den ≠ 0

def Frac.Rel (x y : Frac) : Prop := x.num * y.den = y.num * x.den

-- 原书说“很容易验证”这是等价关系；自反、对称确实一眼可见，传递性要动点脑筋：
theorem Frac.rel_trans {x y z : Frac} (h₁ : Frac.Rel x y) (h₂ : Frac.Rel y z) : Frac.Rel x z := by
  unfold Frac.Rel at *
  apply Int.eq_of_mul_eq_mul_right y.den_ne   -- 只需证明两边乘上 y.den 后相等
  calc x.num * z.den * y.den
      = (x.num * y.den) * z.den := by ac_rfl   -- ac_rfl：按交换律、结合律重排
    _ = (y.num * x.den) * z.den := by rw [h₁]
    _ = (y.num * z.den) * x.den := by ac_rfl
    _ = (z.num * y.den) * x.den := by rw [h₂]
    _ = z.num * x.den * y.den := by ac_rfl

def Q : Type := Quot Frac.Rel
def Q.mk (n d : Int) (h : d ≠ 0 := by decide) : Q := Quot.mk _ ⟨n, d, h⟩

-- 1/2、2/4、(-3)/(-6) 是同一个有理数：
example : Q.mk 1 2 = Q.mk 2 4 := Quot.sound (by unfold Frac.Rel; decide)
example : Q.mk 1 2 = Q.mk (-3) (-6) := Quot.sound (by unfold Frac.Rel; decide)

-- “是否为零”是良定义的：若 a·d = c·b 且 b, d ≠ 0，则 a = 0 ↔ c = 0
def Q.isZero : Q → Bool :=
  Quot.lift (fun x => decide (x.num = 0)) (by
    intro x y (h : x.num * y.den = y.num * x.den)
    simp only [decide_eq_decide]
    constructor
    · intro hx0
      rw [hx0, Int.zero_mul] at h
      rcases Int.mul_eq_zero.mp h.symm with h' | h'
      · exact h'
      · exact absurd h' x.den_ne
    · intro hy0
      rw [hy0, Int.zero_mul] at h
      rcases Int.mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' y.den_ne)

#guard (Q.mk 0 5).isZero
#guard !(Q.mk 3 (-7)).isZero

end Rational
```

::: tip Lean 深入：`Quot` 不要求等价关系
注意，我们构造 `Q` 时根本**没有用到**传递性的证明！`Quot r` 接受任意关系 `r`，它会自动取包含 `r` 的**最小**等价关系（称为 `r` 生成的等价关系）来粘合。如果你手上已经有一个证明过的等价关系（Lean 里叫 `Setoid`），也可以用 `Quotient`，它是 `Quot` 的一个包装，额外提供“相等 ⇒ 有关系”的方向（`Quotient.exact`）。

这对余端来说是个好消息：余楔条件给出的关系本身并不是等价关系，但我们根本不需要手动去取它的闭包——`Quot` 替我们做了。
:::

### Lean 胜出：真正构造余端

在 Haskell 里，`data Coend p = forall a. Coend (p a a)` 只是 `DiagSum`——那个“商”只存在于程序员的约定里（靠参数性保证你观察不出区别）。在 Lean 里，我们可以**真的**构造出余等化子。关系由余楔条件生成：对每个 `f : b → a` 和 `pab : p a b`，把 `⟨b, dimap f id pab⟩` 和 `⟨a, dimap id f pab⟩` 粘在一起：

```lean
inductive CoendRel (p : Type → Type → Type) [Profunctor p] : DiagSum p → DiagSum p → Prop where
  | glue {a b : Type} (f : b → a) (pab : p a b) :
      CoendRel p ⟨b, dimap f id pab⟩ ⟨a, dimap id f pab⟩

/-- 余端 ∫^c p c c：对角线元素之和，按余楔条件取商。 -/
def Coend (p : Type → Type → Type) [Profunctor p] : Type 1 := Quot (CoendRel p)
```

::: tip Lean 深入：用 `inductive` 定义一个关系
`inductive CoendRel ... : DiagSum p → DiagSum p → Prop` 定义了一个关系，它只有一条“生成规则” `glue`：凡是能写成这种形状的一对元素，就有关系，除此之外都没有。用 `inductive` 定义关系是 Lean 的惯用法——你只需列出“产生关系的方式”，而在使用时可以用 `cases` 对它做分情况讨论。
:::

内射 `inj` 把对角线元素送进余端；`cowedge` 说余楔条件成立——它直接来自 `Quot.sound`：

```lean
namespace Coend

/-- 内射 i_a : p a a → ∫^c p c c -/
def inj (a : Type) (x : p a a) : Coend p := Quot.mk _ ⟨a, x⟩

/-- 余楔条件：对 f : b → a，两条路径进入余端后相等。 -/
theorem cowedge {a b : Type} (f : b → a) (pab : p a b) :
    inj b (dimap f id pab) = inj a (dimap id f pab) :=
  Quot.sound (CoendRel.glue f pab)
```

余楔条件画出来是这样（是楔的菱形倒过来）：

```diagram
pab: (1, 0) "p\,a\,b"
pbb: (0, 1.2) "p\,b\,b"
paa: (2, 1.2) "p\,a\,a"
co: (1, 2.4) "\int^c p\,c\,c"
l: pab -> pbb "p\,f\,\mathrm{id}_b" side=right
r: pab -> paa "p\,\mathrm{id}_a\,f"
ib: pbb -> co "i_b" side=right
ia: paa -> co "i_a"
path "经过 p b b": l ib
path "经过 p a a": r ia color=green
caption: 余楔条件（f : b → a）：从 p a b 出发的两条路径，进入余端之后必须相等。在 Lean 中，这正是 Quot.sound 给我们的。
```

余端的泛性质：任何余楔（顶点 `c`，侧边 `β`）都唯一地经由余端分解。分解映射 `desc` 用 `Quot.lift` 定义，良定义性正是余楔条件；唯一性用 `Quot.ind`（“要证明关于商的所有元素的命题，只需对代表元证明”）：

```lean
structure Cowedge (p : Type → Type → Type) [Profunctor p] (c : Type u) where
  β : (a : Type) → p a a → c
  cowedge : ∀ {a b : Type} (f : b → a) (pab : p a b), β b (dimap f id pab) = β a (dimap id f pab)

/-- 泛余楔的分解映射 h : ∫^c p c c → c -/
def desc {c : Type u} (w : Cowedge p c) : Coend p → c :=
  Quot.lift (fun s => w.β s.1 s.2) (by
    intro x y r
    cases r with
    | glue f pab => exact w.cowedge f pab)

theorem fac {c : Type u} (w : Cowedge p c) (a : Type) (x : p a a) :
    desc w (inj a x) = w.β a x := rfl

theorem uniq {c : Type u} (w : Cowedge p c) (h : Coend p → c)
    (hh : ∀ a x, h (inj a x) = w.β a x) : h = desc w := by
  funext q
  induction q using Quot.ind with
  | mk s => exact hh s.1 s.2

/-- 从余端出发的函数 ≅ 余楔。 -/
def homIso (c : Type) : (Coend p → c) ≅ Cowedge p c where
  toFun h := ⟨fun a x => h (inj a x), fun f pab => congrArg h (cowedge f pab)⟩
  invFun w := desc w
  left_inv h := (uniq _ h (fun _ _ => rfl)).symm
  right_inv _ := rfl

end Coend
```

### 从余端出去的函数，就是端

你也许还记得在讨论极限与余极限时说过：hom-函子是**连续的**，即它保持极限。对偶地，逆变的 hom-函子把余极限变成极限。这些性质可以推广到端和余端——它们分别是极限和余极限的推广。特别地，我们得到一个把余端转换成端的非常有用的恒等式：

$$\mathbf{Set}\Big(\int^x p\ x\ x,\ c\Big) \cong \int_x \mathbf{Set}(p\ x\ x,\ c)$$

用伪代码看一下：

```lean no-check
(exists x. p x x) → c   ≅   ∀ x, p x x → c     -- 伪代码
```

它告诉我们：一个接受存在类型的函数，等价于一个多态函数。这完全合乎情理：这样的函数必须准备好处理存在类型中可能封装的**任何一个**类型。这和“接受和类型的函数必须写成 `match`、为和类型中每一种情况各配一个处理器”是同一个道理。在这里，和类型换成了余端，一组处理器换成了一个端——也就是一个多态函数。

在 Lean 里，我们可以把右边真的写成一个端。被积的剖函子是 $\langle x, y \rangle \mapsto (p\ y\ x \to c)$——注意 `p` 的两个参数被交换了，这样它才对第一个参数逆变、对第二个参数协变：

```lean
def CoHom (p : Type → Type → Type) (c : Type) (x y : Type) : Type := p y x → c

instance (c : Type) : Profunctor (CoHom p c) where
  dimap f g h := h ∘ dimap g f

/-- Set(∫^x p x x, c) ≅ ∫_x Set(p x x, c) -/
def coendToEnd (c : Type) : (Coend p → c) ≅ End (CoHom p c) where
  toFun h := {
    run := fun a x => h (Coend.inj a x)
    wedge := fun f => by
      funext pba
      exact congrArg h (Coend.cowedge f pba) }   -- 端的楔条件 = 余端的余楔条件
  invFun e := Coend.desc ⟨e.run, fun f pab => congrFun (e.wedge f) pab⟩
  left_inv h := (Coend.uniq _ h (fun _ _ => rfl)).symm
  right_inv _ := rfl
```

## 忍者米田引理

米田引理里出现的自然变换集合，可以用端来编码，于是得到如下表述：

$$\int_z \mathbf{Set}(\mathcal{C}(a, z), F z) \cong F a$$

还有一个对偶的公式：

$$\int^z \mathcal{C}(z, a) \times F z \cong F a$$

这个恒等式让人强烈地联想到狄拉克 δ 函数的公式（一个函数 $\delta(a - z)$，确切地说是一个分布，在 $a = z$ 处有一个无穷高的尖峰）：$\int \delta(a - z) f(z)\, dz = f(a)$。在这里，hom-函子扮演了 δ 函数的角色——它把“积分”压缩到 $z = a$ 这一点上。

这两个恒等式合起来，有时被称为**忍者米田引理**（Ninja Yoneda lemma）。

::: info 数学小课堂：δ 函数的直觉
在物理里，$\delta(x)$ 是一个“只在 $x = 0$ 处有值、而且总面积为 1”的理想化尖峰。它最重要的性质是“筛选”：$\int \delta(a - z) f(z)\, dz = f(a)$——把 $f$ 和尖峰相乘再积分，就挑出了 $f$ 在 $a$ 处的值。

忍者米田引理说的是同一件事：$\mathcal{C}(z, a)$ 只在“$z$ 能到达 $a$”时非空，把它和 $F z$ 相乘、再对所有 $z$ “积分”（取余端），结果正好挑出 $F a$。
:::

### 在 Lean 中证明两个公式

我们先用 Lean 把两个公式都证明一遍，然后再看原书的推导。第一个公式（端的形式）里，被积剖函子是 $\langle x, y \rangle \mapsto ((a \to x) \to F y)$：

```lean
def YoP (F : Type → Type) (a : Type) (x y : Type) : Type := (a → x) → F y

instance [Functor F] : Profunctor (YoP F a) where
  dimap f g h := fun k => Functor.map g (h (f ∘ k))

/-- ∫_z Set(C(a, z), F z) ≅ F a -/
def ninjaYoneda (F : Type → Type) [Functor F] [LawfulFunctor F] (a : Type) :
    End (YoP F a) ≅ F a where
  toFun e := e.run a id
  invFun fa := {
    run := fun _ k => Functor.map k fa
    wedge := fun {x y} f => by
      funext k
      show Functor.map f (Functor.map (id ∘ k) fa) = Functor.map id (Functor.map (f ∘ k) fa)
      simp [Functor.map_map] }
  left_inv e := by
    ext z
    funext k
    -- 楔条件在 f := k 处、作用于 id：map k (run a id) = run z k
    have h := congrFun (e.wedge k) id
    simp only [dimap, id_map] at h
    exact h
  right_inv fa := id_map fa
```

第二个公式（余端的形式）里，被积剖函子是 $\langle x, y \rangle \mapsto (x \to a) \times F y$。这一次我们用的是货真价实的商——`Coend`：

```lean
def CoYoP (F : Type → Type) (a : Type) (x y : Type) : Type := (x → a) × F y

instance [Functor F] : Profunctor (CoYoP F a) where
  dimap f g := fun (k, fy) => (k ∘ f, Functor.map g fy)

/-- ∫^z C(z, a) × F z ≅ F a -/
def ninjaCoYoneda (F : Type → Type) [Functor F] [LawfulFunctor F] (a : Type) :
    Coend (CoYoP F a) ≅ F a where
  toFun := Coend.desc {
    β := fun _ kf => Functor.map kf.1 kf.2      -- ⟨z, (k, fz)⟩ ↦ map k fz
    cowedge := fun {x y} f pab => by
      obtain ⟨k, fy⟩ := pab
      show Functor.map (k ∘ f) (Functor.map id fy) = Functor.map k (Functor.map f fy)
      rw [id_map, Functor.map_map]
      rfl }
  invFun fa := Coend.inj a (id, fa)
  left_inv q := by
    induction q using Quot.ind with
    | mk s =>
      obtain ⟨z, k, fz⟩ := s
      -- 关键一步：余楔条件把 ⟨z, (k, fz)⟩ 和 ⟨a, (id, map k fz)⟩ 粘在一起
      have h : Coend.inj (p := CoYoP F a) z (k, id <$> fz)
             = Coend.inj (p := CoYoP F a) a (id, k <$> fz) :=
        Coend.cowedge (p := CoYoP F a) k (show CoYoP F a a z from (id, fz))
      rw [id_map] at h
      exact h.symm
  right_inv fa := id_map fa
```

::: tip 补充：你其实早就见过它
`Coend (CoYoP F a)` 的元素是“某个 `z`，一个函数 `z → a`，以及一个 `F z`”——这就是 Haskell 社区所说的 **Coyoneda**：把 `fmap` “延后执行”，先把函数记下来。左边的同构告诉我们，只要 `F` 是函子，延后执行和立刻执行没有区别。下一章的“自由函子”会把这个想法推得更远。

注意 `left_inv` 那一步：如果没有取商，`⟨z, (k, fz)⟩` 和 `⟨a, (id, map k fz)⟩` 是两个不同的值，同构就不成立。正是余楔条件让它们相等——这就是“商”的意义。
:::

### 原书的推导

为了证明第二个公式，我们要用到米田嵌入的一个推论：两个对象同构，当且仅当它们的 hom-函子同构。换句话说，$a \cong b$ 当且仅当存在一个类型为

$$[\mathcal{C}, \mathbf{Set}](\mathcal{C}(a, -), \mathcal{C}(b, =))$$

的自然变换，并且它是一个同构。

我们先把要证明的恒等式的左边，放进一个通往任意对象 $c$ 的 hom-函子里：

$$\mathbf{Set}\Big(\int^z \mathcal{C}(z, a) \times F z,\ c\Big)$$

利用连续性，可以把余端换成端：

$$\int_z \mathbf{Set}\big(\mathcal{C}(z, a) \times F z,\ c\big)$$

现在可以利用积与指数之间的伴随（也就是柯里化）：

$$\int_z \mathbf{Set}\big(\mathcal{C}(z, a),\ c^{F z}\big)$$

用米田引理来“完成积分”，得到：

$$c^{F a}$$

（注意我们用的是米田引理的逆变版本，因为函子 $c^{F z}$ 对 $z$ 是逆变的。）这个指数对象同构于 hom-集：

$$\mathbf{Set}(F a, c)$$

最后，借助米田嵌入得到同构：

$$\int^z \mathcal{C}(z, a) \times F z \cong F a$$

## 剖函子的复合

让我们沿着“剖函子描述一种关系”的思路继续往下走——更准确地说，是一种带证明的关系：集合 $p\ a\ b$ 代表“$a$ 关联到 $b$”的全部证明。如果有两个关系 $p$ 和 $q$，我们可以尝试复合它们。我们说 $a$ 通过“$q$ 在 $p$ 之后”的复合关联到 $b$，如果存在一个中间对象 $c$，使得 $q\ b\ c$ 和 $p\ c\ a$ 都非空。这个新关系的证明，就是两个单独关系的证明组成的所有对子。因此，理解了“存在量词对应余端”、“笛卡尔积对应证明的对子”之后，我们就可以用下面的公式定义剖函子的复合：

$$(q \circ p)\ a\ b = \int^c p\ c\ a \times q\ b\ c$$

下面是 Haskell 的 `Data.Profunctor.Composition` 里等价的定义（略作改名），它用的是广义代数数据类型（GADT）语法：

```lean no-check
-- Haskell：
-- data Procompose q p a b where
--     Procompose :: q a c -> p c b -> Procompose q p a b
```

在 GADT 语法里，自由类型变量（这里是 `c`）会被自动存在量化。所以（去柯里化后的）数据构造器 `Procompose` 等价于：

```lean no-check
exists c. (q a c, p c b)      -- 伪代码
```

::: warning 易错点：两种书写顺序
公式里写的是 $p\ c\ a \times q\ b\ c$，Haskell 代码里写的是 `q a c × p c b`——两者的参数顺序约定不同（相当于把 $a$、$b$ 的角色对调了一下），但描述的是同一种构造：一条经过中间对象 `c` 的“证明链”。下面的 Lean 代码跟随 Haskell 的约定。
:::

在 Lean 里，我们直接用上面构造好的 `Coend` 来定义复合。对固定的 `a`、`b`，被积剖函子是 $\langle c_1, c_2 \rangle \mapsto q\ a\ c_2 \times p\ c_1\ b$（`q` 的第二个参数是协变的，`p` 的第一个参数是逆变的，正好凑成一个剖函子）：

```lean
def PComp (q p : Type → Type → Type) (a b : Type) (c₁ c₂ : Type) : Type := q a c₂ × p c₁ b

instance [Profunctor q] [Profunctor p] : Profunctor (PComp q p a b) where
  dimap f g := fun (x, y) => (dimap id g x, dimap f id y)

/-- 剖函子的复合 (q ∘ p) a b = ∫^c q a c × p c b -/
def ProComp (q p : Type → Type → Type) [Profunctor q] [Profunctor p] (a b : Type) : Type 1 :=
  Coend (PComp q p a b)

def ProComp.mk [Profunctor q] {c : Type} (x : q a c) (y : p c b) : ProComp q p a b :=
  Coend.inj c (x, y)
```

::: warning 易错点：复合的结果“变大”了
注意 `ProComp q p a b : Type 1`，而不是 `Type`。因为中间对象 `c` 跑遍**所有**类型，结果就升了一个宇宙。这意味着 `ProComp q p` 不再是一个 `Type → Type → Type`，没法直接再喂给我们的 `Profunctor` 类。数学上也有同样的问题：只有当范畴是**小**的，剖函子的复合才保证仍然取值于 $\mathbf{Set}$。Lean 只是诚实地把这个“大小问题”摆到了你面前。
:::

这样定义的复合，单位元是 hom-函子——这直接来自忍者米田引理。在 Lean 里，左单位律的证明和 `ninjaCoYoneda` 如出一辙：

```lean
/-- 左单位律：Fun ∘ p ≅ p -/
def procompUnitLeft (p : Type → Type → Type) [Profunctor p] [LawfulProfunctor p] (a b : Type) :
    ProComp Fun p a b ≅ p a b where
  toFun := Coend.desc {
    β := fun _ xy => dimap xy.1 id xy.2           -- ⟨c, (k, y)⟩ ↦ lmap k y
    cowedge := fun {c₁ c₂} f pab => by
      obtain ⟨k, y⟩ := pab
      show dimap (id ∘ k ∘ id) id (dimap f id y) = dimap (f ∘ k ∘ id) id (dimap id id y)
      rw [LawfulProfunctor.dimap_comp, LawfulProfunctor.dimap_id]
      rfl }
  invFun pab := ProComp.mk (show Fun a a from id) pab
  left_inv q := by
    induction q using Quot.ind with
    | mk s =>
      obtain ⟨c, k, y⟩ := s
      have h : Coend.inj (p := PComp Fun p a b) a ((id : Fun a a), dimap k id y)
             = Coend.inj (p := PComp Fun p a b) c (k, dimap id id y) :=
        Coend.cowedge (p := PComp Fun p a b) k (show PComp Fun p a b c a from ((id : Fun a a), y))
      rw [LawfulProfunctor.dimap_id] at h
      exact h
  right_inv pab := LawfulProfunctor.dimap_id pab
```

于是很自然地会问：是否存在一个以剖函子为态射的范畴？答案是肯定的，但有个附加说明：剖函子复合的结合律和单位律都只在**自然同构**的意义下成立（就像上面的 `procompUnitLeft` 是一个 `≅`，而不是 `=`）。这种定律只在同构意义下成立的范畴，叫作**双范畴**（bicategory），它比 2-范畴更一般。于是我们有一个双范畴 $\mathbf{Prof}$：对象是范畴，态射是剖函子，态射之间的态射（也叫 **2-胞腔**，two-cells）是自然变换。事实上还可以走得更远：除了剖函子，范畴之间还有普通的函子作为态射。拥有两种态射的范畴，叫作**双重范畴**（double category）。

剖函子在 Haskell 的 lens 库和 arrow 库里扮演着重要角色。（例如，“剖函子光学”把透镜（lens）、棱镜（prism）等统一描述为“对所有满足某种约束的剖函子 `p`，`p a b → p s t`”——又是一个对剖函子的全称量化，也就是一个端。）

```lean hidden
end Ch310
```

## 挑战

原书本章没有挑战题。下面是本书新增的练习，帮助你巩固本章的 Lean 构造。

1. 证明剖函子复合的**右单位律**：`ProComp q Fun a b ≅ q a b`。
2. 设 `X` 是一个固定的类型，**常剖函子** `Const X a b := X` 的 `dimap` 什么也不做。证明 `End (Const X) ≅ X`。提示：楔条件对任意 `f : a → b` 都要求 `run a = run b`；对任意类型 `b`，有没有一个类型能“通往”它？
3. 剖函子 `Snd a b := b`（忽略第一个参数）的余端是什么？证明 `Coend Snd ≅ Unit`。
4. 证明 `Costar F a b := F a → b` 是剖函子，并在 `F` 守法时满足剖函子定律。
5. 在 `End Fun` 中，`weird` 为什么不能作为一个元素？用 Lean 证明：`weird` 不满足 `Fun` 的楔条件。

::: details 参考答案
```lean
namespace Ch310

-- 1. 右单位律：q ∘ Fun ≅ q。被积元素是 ⟨c, (x : q a c, k : c → b)⟩，把它送到 rmap k x。
def procompUnitRight (q : Type → Type → Type) [Profunctor q] [LawfulProfunctor q] (a b : Type) :
    ProComp q Fun a b ≅ q a b where
  toFun := Coend.desc {
    β := fun _ xy => dimap id xy.2 xy.1
    cowedge := fun {c₁ c₂} f pab => by
      obtain ⟨x, k⟩ := pab
      show dimap id (id ∘ (k ∘ f) ∘ id) (dimap id id x) = dimap id (id ∘ k ∘ id) (dimap id f x)
      rw [LawfulProfunctor.dimap_id, LawfulProfunctor.dimap_comp]
      rfl }
  invFun x := ProComp.mk x (show Fun b b from id)
  left_inv r := by
    induction r using Quot.ind with
    | mk s =>
      obtain ⟨c, x, k⟩ := s
      have h : Coend.inj (p := PComp q Fun a b) c (dimap id id x, k)
             = Coend.inj (p := PComp q Fun a b) b (dimap id k x, (id : Fun b b)) :=
        Coend.cowedge (p := PComp q Fun a b) k (show PComp q Fun a b b c from (x, (id : Fun b b)))
      rw [LawfulProfunctor.dimap_id] at h
      exact h.symm
  right_inv x := LawfulProfunctor.dimap_id x

-- 2. 常剖函子的端。空类型 Empty 能“通往”任何类型（Empty.elim），
--    所以楔条件迫使每个 run b 都等于 run Empty。
def Const (X : Type) (_ _ : Type) : Type := X

instance : Profunctor (Const X) where
  dimap _ _ x := x

def endConst (X : Type) : End (Const X) ≅ X where
  toFun e := e.run Empty
  invFun x := ⟨fun _ => x, fun _ => rfl⟩
  left_inv e := by
    ext a
    exact e.wedge (fun (v : Empty) => nomatch v)
  right_inv _ := rfl

-- 3. ∫^c c ≅ Unit：任何 ⟨b, x⟩ 都通过 f : b → Unit 被粘到 ⟨Unit, ()⟩ 上。
def Snd (_ b : Type) : Type := b

instance : Profunctor Snd where
  dimap _ g x := g x

def coendSnd : Coend Snd ≅ Unit where
  toFun _ := ()
  invFun _ := Coend.inj Unit ()
  left_inv r := by
    induction r using Quot.ind with
    | mk s =>
      obtain ⟨b, x⟩ := s
      exact (Coend.cowedge (p := Snd) (fun (_ : b) => ()) (show Snd Unit b from x)).symm
  right_inv _ := rfl

-- 4. Costar
def Costar (F : Type → Type) (a b : Type) : Type := F a → b

instance [Functor F] : Profunctor (Costar F) where
  dimap f g h := g ∘ h ∘ Functor.map f

instance [Functor F] [LawfulFunctor F] : LawfulProfunctor (Costar F) where
  dimap_id h := by
    funext x
    show h (id <$> x) = h x
    rw [id_map]
  dimap_comp f g f' g' h := by
    funext x
    show g' (g (h (f <$> (f' <$> x)))) = g' (g (h ((f ∘ f') <$> x)))
    rw [comp_map]

-- 5. weird 不满足楔条件：取 f = Nat.succ : Nat → Nat，在 0 处两边分别是 1 和 0。
theorem weird_not_wedge :
    ¬ ∀ {a b : Type} (f : a → b), dimap (p := Fun) id f (weird a) = dimap f id (weird b) := by
  intro h
  have := congrFun (h Nat.succ) 0
  -- this : succ (weird Nat 0) = weird Nat (succ 0)
  change Nat.succ (weird Nat 0) = weird Nat (Nat.succ 0) at this
  rw [weird_nat, weird_nat] at this
  contradiction

end Ch310
```

第 2 题的直觉：楔条件把“能用箭头连起来的对角线位置”捆绑在一起。在 $\mathbf{Set}$ 里空集是始对象，它有箭头通往一切，所以所有位置都被捆在一起，端就只剩下一个 $X$。第 3 题是对偶的直觉：单点集是终对象，一切都有箭头通往它，于是余端里的所有元素都被粘成了一个。
:::

## 本章小结

- **剖函子** $p : \mathcal{C}^{op} \times \mathcal{C} \to \mathbf{Set}$ 是“带证明的关系”，在 Lean 中是带 `dimap` 的 `p : Type → Type → Type`；hom-函子 `Fun a b = a → b` 是最典型的例子。
- 一个态射 $f : a \to b$ 能把对角线元素 $p\ a\ a$ 和 $p\ b\ b$ 都送到 $p\ a\ b$。**双自然变换**和**楔**的条件，都是在说“两条路在这里会师”。
- **端** $\int_c p\ c\ c$ 是泛楔，推广了极限；在 Lean 中它是“带楔条件的多态函数” `End p`，住在 `Type 1`。Haskell 靠参数性白拿楔条件，Lean 要把它写出来（`weird` 说明了为什么）。
- 端是对角线乘积 `∀ a, p a a` 中满足楔条件的子集——一个**等化子**，在 Lean 中就是子类型。
- **自然变换就是端**：$\mathrm{Nat}(F, G) = \int_c \mathcal{C}(F c, G c)$，楔条件恰好就是自然性条件。
- **余端** $\int^c p\ c\ c$ 是存在类型 `Σ a, p a a` 按余楔条件取的**商**；Lean 的 `Quot` 让我们真的把它构造了出来，并证明了它的泛性质。
- 从余端出去的函数就是端：$\mathbf{Set}(\int^x p\ x\ x, c) \cong \int_x \mathbf{Set}(p\ x\ x, c)$——接受存在类型的函数等价于多态函数。
- **忍者米田引理**：$\int_z \mathbf{Set}(\mathcal{C}(a, z), F z) \cong F a$，$\int^z \mathcal{C}(z, a) \times F z \cong F a$；hom-函子像 δ 函数一样“筛选”出 $F a$。两条我们都在 Lean 中证明了。
- **剖函子的复合**用余端定义，hom-函子是它的单位（在同构意义下）；剖函子构成双范畴 $\mathbf{Prof}$。
