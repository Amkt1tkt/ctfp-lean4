# 3.12 富集范畴

如果一个范畴的对象构成一个集合，我们就说它是**小范畴**（small category）。可我们知道，世上有比集合更“大”的东西。
最有名的例子是：在标准集合论（Zermelo–Fraenkel 集合论，可以再加上选择公理）里，“所有集合构成的集合”根本造不出来。
所以“所有集合构成的范畴”必定是一个**大范畴**（large category）。数学家有一些技巧，比如 Grothendieck 宇宙（Grothendieck universe），
可以用来定义超出集合范围的“搜集”（collection）。借助这些技巧，我们才能心安理得地谈论大范畴。

::: info 数学小课堂：为什么“所有集合的集合”不存在？
这就是著名的**罗素悖论**。假设真有一个装下所有集合的集合 $U$，那么我们可以从中挑出所有“不包含自己”的集合：
$R = \{x \in U \mid x \notin x\}$。现在问：$R \in R$ 吗？

- 如果 $R \in R$，按 $R$ 的定义，$R \notin R$；
- 如果 $R \notin R$，那 $R$ 满足挑选条件，于是 $R \in R$。

两头都是矛盾。所以“所有集合”太大了，不能再被当作一个集合。这类“太大的搜集”数学上叫**真类**（proper class）。
范畴论里大量出现这样的东西：$\mathbf{Set}$ 的对象就是所有集合。
:::

::: tip Lean 深入：宇宙层级就是 Lean 版的 Grothendieck 宇宙
Lean 用**宇宙层级**（universe）回避了罗素悖论：`Nat : Type`，`Type : Type 1`，`Type 1 : Type 2`……
没有任何类型满足 `Type : Type`。“所有（第 0 层）类型”构成的东西 `Type` 本身住在更高一层的 `Type 1` 里。

这正好对应“大范畴”：全书统一的 `CTFP.typeCategory : Category (Type u)` 的对象类型是 `Type u`，
它自己住在 `Type (u+1)` 中——从 `Type u` 的视角看，这个范畴是“大”的；但它的每个 hom-集 `a → b` 仍然是 `Type u` 里的一个类型，
也就是“局部小”（马上就讲）。
:::

如果任意两个对象之间的态射都构成一个集合，这个范畴就叫**局部小**（locally small）的。
如果连这一点都做不到，有几个定义就得重新想一想。特别是：如果我们连“从一个集合里把态射挑出来”都做不到，复合态射又是什么意思？
解决办法是“自举”（bootstrap）：把 hom-集——它们本是 $\mathbf{Set}$ 中的对象——换成另一个范畴 $\mathcal{V}$ 中的**对象**。
区别在于：一般而言，对象是没有“元素”的，所以我们不再能谈论一个个单独的态射。
**富集**（enriched）范畴的一切性质，都必须用作用在“hom-对象整体”上的运算来定义。
为了做到这一点，提供 hom-对象的那个范畴必须带有额外的结构——它必须是一个幺半范畴。
如果把这个幺半范畴记作 $\mathcal{V}$，我们就可以谈论**在 $\mathcal{V}$ 上富集的范畴** $\mathcal{C}$（a category enriched over $\mathcal{V}$）。

除了“大小”方面的原因，我们也可能只是想把 hom-集推广成比裸集合有更多结构的东西。
比如，传统的范畴里没有对象之间“距离”的概念：两个对象之间要么有态射相连，要么没有。
凡是与某个对象相连的对象都是它的邻居。这和现实生活不一样：在范畴里，朋友的朋友的朋友，和我的铁哥们儿离我一样近。
而在一个适当富集的范畴里，我们就可以定义对象之间的距离了。

还有一个非常实际的理由，值得你积累一点富集范畴的经验：网上有个非常有用的范畴论知识库——[nLab](https://ncatlab.org/)，
它的大部分条目都是用富集范畴的语言写的。

::: tip 本章的 Lean 策略
完整的富集范畴定义（对任意幺半范畴 $\mathcal{V}$）在 Lean 里写出来很重：要先形式化幺半范畴、相干条件，再写富集。
本章的做法是：

1. 用 Lean 的 `Type` 与 `×` 具体验证幺半范畴的相干条件（五边形、三角形）以及“自富集”的构造；
2. 把富集的定义写成一个**简化版** `EnrichedOverPreorder`：只考虑 $\mathcal{V}$ 是一个“幺半预序”（瘦的幺半范畴）的情形。
   这时所有交换图自动交换，定义只剩下两行，但已经足以把“预序”和“度量空间”这两个最漂亮的例子讲透、证透。
:::

## 为什么是幺半范畴？

构造富集范畴时我们要记住一条：当我们把幺半范畴换成 $\mathbf{Set}$、把 hom-对象换成 hom-集（态射集合）时，必须能恢复出通常的定义。
最好的办法是从通常的定义出发，不断把它改写成**无点**（point-free）的形式——也就是说，不提集合中的任何元素。

先看复合的定义。通常，复合接受一对态射，一个来自 $\mathcal{C}(b, c)$、一个来自 $\mathcal{C}(a, b)$，把它们映到 $\mathcal{C}(a, c)$ 中的一个态射。
换句话说，复合是一个映射：

$$\mathcal{C}(b, c) \times \mathcal{C}(a, b) \to \mathcal{C}(a, c)$$

这是集合之间的函数——其中一个集合是两个 hom-集的笛卡尔积。这个式子很容易推广：把笛卡尔积换成更一般的东西就行。
范畴积就可以，但我们还能走得更远，用一个完全一般的张量积。

::: tip Lean 深入：复合本来就是这样一个函数
回忆全书公共前导里的 `Category` 类：`comp : Hom b c → Hom a b → Hom a c`。这是**柯里化**的写法；
把它“反柯里化”就得到一个从积出发的函数 `Hom b c × Hom a b → Hom a c`，正是上面的公式。下面把它写出来：
:::

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

end CTFP

open CTFP
```

```lean
-- 复合：从两个 hom-集的“积”到第三个 hom-集的函数
def compUncurried {C : Type u} [Category.{u, v} C] {a b c : C} :
    (b ⟶ c) × (a ⟶ b) → (a ⟶ c) :=
  fun (g, f) => g ⊚ f

-- 恒等：从单元素集合（Lean 里是 Unit）出发、“挑出”恒等态射的函数
def pickId {C : Type u} [Category.{u, v} C] (a : C) : Unit → (a ⟶ a) :=
  fun () => 𝟙 a
```

接下来是恒等态射。与其从 hom-集里挑出单个元素，不如用从单元素集合 $1$ 出发的函数来定义它们：

$$j_a \colon 1 \to \mathcal{C}(a, a)$$

同样，我们可以把单元素集合换成终对象；但还可以走得更远：把它换成张量积的单位 $i$。

可以看到，取自某个幺半范畴 $\mathcal{V}$ 的对象，是替代 hom-集的好候选。

## 幺半范畴

我们之前讨论过幺半范畴，不过值得把定义再复述一遍。幺半范畴定义了一个张量积，它是一个双函子：

$$\otimes \colon \mathcal{V} \times \mathcal{V} \to \mathcal{V}$$

我们希望张量积满足结合律，但只要在自然同构的意义下满足就够了。这个同构叫**结合子**（associator），它的分量是：

$$\alpha_{a b c} \colon (a \otimes b) \otimes c \to a \otimes (b \otimes c)$$

它必须在三个参数上都是自然的。

幺半范畴还必须定义一个特殊的单位对象 $i$，充当张量积的单位——同样是在自然同构的意义下。这两个同构分别叫**左单位子**和**右单位子**
（left / right unitor），它们的分量是：

$$\lambda_a \colon i \otimes a \to a \qquad\qquad \rho_a \colon a \otimes i \to a$$

结合子和单位子必须满足以下**相干条件**（coherence conditions）。第一个是著名的“五边形”：把四个对象的括号从最左挪到最右，有两条路，它们必须相等。

```diagram
L: (1.7, 0) "((a \otimes b) \otimes c) \otimes d"
R: (3.4, 1.35) "(a \otimes (b \otimes c)) \otimes d"
MR: (3.4, 2.75) "a \otimes ((b \otimes c) \otimes d)"
ML: (0, 2.05) "(a \otimes b) \otimes (c \otimes d)"
B: (1.7, 4.1) "a \otimes (b \otimes (c \otimes d))"
top: L -> R "\alpha_{abc} \otimes \mathrm{id}_d"
l1: L -> ML "\alpha_{(a \otimes b)cd}" side=right
r1: R -> MR "\alpha_{a(b \otimes c)d}"
l2: ML -> B "\alpha_{ab(c \otimes d)}" side=right
r2: MR -> B "\mathrm{id}_a \otimes \alpha_{bcd}"
path "左边两步": l1 l2 color=green
path "右边三步": top r1 r2
caption: 五边形相干条件：把括号从最左挪到最右，两条路线得到的同构必须相同。
```

第二个是“三角形”：单位对象夹在中间时，先挪括号再消掉 $i$，与直接从左边消掉 $i$，结果相同。

```diagram
L: (0, 0) "(a \otimes i) \otimes b"
R: (1.7, 1.4) "a \otimes (i \otimes b)"
B: (0, 2.8) "a \otimes b"
al: L -> R "\alpha_{aib}"
rho: L -> B "\rho_a \otimes \mathrm{id}_b" side=right
lam: R -> B "\mathrm{id}_a \otimes \lambda_b"
path "先结合再消左单位": al lam
path "直接消右单位": rho color=green
caption: 三角形相干条件。
```

::: info 数学小课堂：什么叫“在自然同构意义下满足结合律”？
普通的乘法满足 $(2 \times 3) \times 4 = 2 \times (3 \times 4)$，两边是**同一个数**。但对类型而言，`(A × B) × C` 和 `A × (B × C)`
是**两个不同的类型**：一个值长这样 `((a, b), c)`，另一个长这样 `(a, (b, c))`。它们并不相等，但可以无损地互相转换——它们**同构**。

“自然”的意思是：这个转换不依赖 `A`、`B`、`C` 具体是什么类型，对所有类型都“用同一套公式”。
相干条件则要求这些转换彼此“协调一致”：无论你用什么顺序挪括号，最后得到的转换都一样。
:::

在 $\mathbf{Set}$（或者 Lean 的 `Type`）里，取笛卡尔积作张量积、单元素类型 `Unit` 作单位，就得到一个幺半范畴。
下面用 Lean 写出结合子和单位子，并**证明**五边形与三角形确实交换：

```lean
section TypeMonoidal
variable {a b c d : Type}

/-- 结合子 α：把括号从左挪到右 -/
def assocT : (a × b) × c → a × (b × c) := fun ((x, y), z) => (x, (y, z))
/-- 左、右单位子 λ、ρ -/
def unitorL : Unit × a → a := fun (_, x) => x
def unitorR : a × Unit → a := fun (x, _) => x
/-- 张量积作用在态射上：f ⊗ g（双函子的“map”） -/
def tensorMap {a a' b b' : Type} (f : a → a') (g : b → b') : a × b → a' × b' :=
  fun (x, y) => (f x, g y)

/-- 五边形：左边两步 = 右边三步 -/
theorem pentagon :
    (assocT : (a × b) × (c × d) → a × (b × (c × d))) ∘ (assocT : ((a × b) × c) × d → _)
      = tensorMap id (assocT : (b × c) × d → _) ∘ assocT
          ∘ tensorMap (assocT : (a × b) × c → _) id := by
  -- 把输入拆成 (((x, y), z), w)，两边都算出 (x, (y, (z, w)))
  funext ⟨⟨⟨x, y⟩, z⟩, w⟩
  rfl

/-- 三角形 -/
theorem triangle :
    tensorMap (unitorR : a × Unit → a) (id : b → b) = tensorMap id unitorL ∘ assocT := by
  funext ⟨⟨x, ⟨⟩⟩, y⟩
  rfl

end TypeMonoidal
```

::: tip Lean 深入：模式匹配式的 `funext`
`funext ⟨⟨⟨x, y⟩, z⟩, w⟩` 一次做了两件事：先用函数外延性（两个函数在每个输入上相等，它们就相等）引入输入，
再立刻用匿名构造子记号 `⟨…⟩` 把嵌套的元组拆开。拆开之后两边都是具体的元组，`rfl`（按定义计算后相等）就能收尾。
`⟨⟩` 拆的是 `Unit` 的唯一元素 `()`。
:::

一个幺半范畴如果有一个自然同构，分量为

$$\gamma_{a b} \colon a \otimes b \to b \otimes a$$

并且它的“平方是恒等”：

$$\gamma_{b a} \circ \gamma_{a b} = \mathrm{id}_{a \otimes b}$$

而且与幺半结构相容，就称它为**对称的**（symmetric）幺半范畴。在 `Type` 中，$\gamma$ 就是交换元组的两个分量：

```lean
def swapT {a b : Type} : a × b → b × a := fun (x, y) => (y, x)

theorem swap_swap {a b : Type} : (swapT : b × a → a × b) ∘ swapT = id := by
  funext ⟨x, y⟩
  rfl
```

幺半范畴有一个有趣之处：你也许可以把**内部 hom**（internal hom，也就是函数对象）定义为张量积的右伴随。
你可能还记得，函数对象（也叫指数对象）的标准定义，是范畴积的右伴随。对任意一对对象都存在这样的对象的范畴，叫做笛卡尔闭范畴。
下面是在幺半范畴中定义内部 hom 的伴随：

$$\mathcal{V}(a \otimes b, c) \sim \mathcal{V}(a, [b, c])$$

我沿用 [G. M. Kelly](http://www.tac.mta.ca/tac/reprints/articles/10/tr10.pdf) 的记号，用 $[b, c]$ 表示内部 hom。
这个伴随的余单位是一个自然变换，它的分量叫**求值态射**（evaluation morphism）：

$$\varepsilon_{a b} \colon ([a, b] \otimes a) \to b$$

::: tip Lean 深入：这个伴随就是柯里化
在 `Type` 中，$[b, c]$ 就是函数类型 `b → c`，伴随 $\mathcal{V}(a \times b, c) \cong \mathcal{V}(a, b \to c)$ 就是柯里化与反柯里化，
余单位 $\varepsilon$ 就是“把函数作用到参数上”。来回转换都不丢信息：
:::

```lean
section Closed
variable {a b c : Type}

def curryT : (a × b → c) → (a → b → c) := fun h x y => h (x, y)
def uncurryT : (a → b → c) → (a × b → c) := fun k (x, y) => k x y
/-- 余单位 ε：求值 -/
def evalT : (a → b) × a → b := fun (f, x) => f x

theorem uncurry_curry (h : a × b → c) : uncurryT (curryT h) = h := by
  funext ⟨x, y⟩; rfl
theorem curry_uncurry (k : a → b → c) : curryT (uncurryT k) = k := rfl

end Closed
```

注意，如果张量积不对称，我们还可以用下面这个伴随定义另一种内部 hom，记作 $[[a, c]]$：

$$\mathcal{V}(a \otimes b, c) \sim \mathcal{V}(b, [[a, c]])$$

两者都有定义的幺半范畴叫做**双闭的**（biclosed）。不是双闭范畴的一个例子是：$\mathbf{Set}$ 上的自函子范畴，以函子复合作为张量积。
我们正是用这个范畴来定义单子的。

::: details 补充：为什么自函子范畴不是双闭的？
在自函子范畴里，$F \otimes G = F \circ G$。“右闭”要求每个 $- \circ G$ 都有右伴随——这没问题，它就是上一章的右 Kan 扩张 $\mathrm{Ran}_G$。
“左闭”则要求每个 $F \circ -$ 也都有右伴随。可左伴随必须保持余极限（例如余积），而 $\mathbf{Set}$ 上函子范畴里的余积是逐点计算的，
所以 $F \circ -$ 保持余积，要求 $F$ 自己就保持余积。取 $F\,x = x \times x$（Lean 里的 `fun α => α × α`）：
$(x + y) \times (x + y)$ 有四块，而 $x \times x + y \times y$ 只有两块，$F$ 不保持余积。于是 $F \circ -$ 没有右伴随，自函子范畴不是双闭的。
:::

## 富集范畴

在幺半范畴 $\mathcal{V}$ 上富集的范畴 $\mathcal{C}$，用 hom-对象代替了 hom-集。对 $\mathcal{C}$ 中的每一对对象 $a$ 和 $b$，
我们指定 $\mathcal{V}$ 中的一个对象 $\mathcal{C}(a, b)$。hom-对象沿用 hom-集的记号，但要记住：它们里面不“装着”态射。
另一方面，$\mathcal{V}$ 本身是一个普通的（未富集的）范畴，有 hom-集，有态射。所以我们并没有彻底摆脱集合——只是把它们扫到了地毯底下。

既然不能谈论 $\mathcal{C}$ 中单个的态射，态射的复合就换成了 $\mathcal{V}$ 中的一族态射：

$$\circ \colon \mathcal{C}(b, c) \otimes \mathcal{C}(a, b) \to \mathcal{C}(a, c)$$

![富集范畴中的复合](/img/3.12/composition.jpg "富集范畴里的复合：hom-对象 C(b,c) 与 C(a,b) 的张量积（中间的蓝色方块），经由 V 中的态射 ∘ 被送到 hom-对象 C(a,c)。")

类似地，恒等态射换成了 $\mathcal{V}$ 中的一族态射：

$$j_a \colon i \to \mathcal{C}(a, a)$$

这里 $i$ 是 $\mathcal{V}$ 中的张量单位。

![富集范畴中的恒等](/img/3.12/id.jpg "富集范畴里的恒等：V 中的态射 j_a 从张量单位 i 指向 hom-对象 C(a,a)。")

复合的结合律用 $\mathcal{V}$ 中的结合子来表述（为了让图放得下，下面记 $C_{xy} = \mathcal{C}(x, y)$）：

```diagram
TL: (1.5, 0) "(C_{cd} \otimes C_{bc}) \otimes C_{ab}"
TR: (3, 2) "C_{bd} \otimes C_{ab}"
BL: (0, 1.35) "C_{cd} \otimes (C_{bc} \otimes C_{ab})"
BR: (0, 2.7) "C_{cd} \otimes C_{ac}"
R: (1.5, 4) "C_{ad}"
c1: TL -> TR "\circ \otimes \mathrm{id}"
c2: TR -> R "\circ"
al: TL -> BL "\alpha" side=right
d1: BL -> BR "\mathrm{id} \otimes \circ" side=right
d2: BR -> R "\circ" side=right
path "先复合前两个": c1 c2
path "先挪括号再复合后两个": al d1 d2 color=green
caption: 富集范畴中的结合律：(h∘g)∘f 与 h∘(g∘f) 这两种复合方式，经结合子对齐后相同。
```

单位律同样用单位子来表达：

```diagram
L: (0, 0) "C_{ab} \otimes i"
R: (1.6, 1.4) "C_{ab} \otimes C_{aa}"
B: (0, 2.8) "C_{ab}"
top: L -> R "\mathrm{id} \otimes j_a"
rho: L -> B "\rho" side=right
cmp: R -> B "\circ"
path "接上恒等再复合": top cmp
path "直接消去单位": rho color=green
caption: 右单位律：f ∘ id_a = f。
```

```diagram
L: (0, 0) "i \otimes C_{ab}"
R: (1.6, 1.4) "C_{bb} \otimes C_{ab}"
B: (0, 2.8) "C_{ab}"
top: L -> R "j_b \otimes \mathrm{id}"
lam: L -> B "\lambda" side=right
cmp: R -> B "\circ"
path "接上恒等再复合": top cmp
path "直接消去单位": lam color=green
caption: 左单位律：id_b ∘ f = f。
```

::: tip Rust 视角
可以把 hom-对象想成一个“关联类型”：普通范畴里，`Hom<A, B>` 是“所有从 A 到 B 的箭头构成的集合”，你可以一个一个地拿出箭头来；
富集范畴里，`Hom<A, B>` 只是 $\mathcal{V}$ 里的某个“值”，可能是一个布尔、一个数、一个向量空间、甚至一个范畴。
复合不再是“拿两支箭头拼一支”，而是 $\mathcal{V}$ 里一个从 `Hom<B, C> ⊗ Hom<A, B>` 到 `Hom<A, C>` 的态射。
:::

### 在 Lean 中：一个简化版的富集范畴

当 $\mathcal{V}$ 是一个**瘦**范畴（任意两个对象之间至多一个态射，也就是一个预序）时，事情变得极其简单：

- $\mathcal{V}$ 中“从 $x$ 到 $y$ 有一个态射”只是一个命题 $x \le y$（在 Lean 里就是一个 `Prop`）；
- 任意两条平行路线必然相等（反正至多一个态射），所以**所有交换图自动交换**，结合律与单位律无需再验证；
- 富集范畴的复合与恒等，就退化成“某些态射**存在**”这样的命题。

我们先把“幺半预序”写成一个结构体。为了简单，我们要求结合律与单位律严格成立（等式而非同构）——本章的例子都满足这一点：

```lean
/-- 瘦的（预序）幺半范畴：对象类型 V，“态射存在”关系 Le，张量积 tensor 与单位 unit。 -/
structure ThinMonoidal where
  V : Type
  Le : V → V → Prop
  le_refl : ∀ x, Le x x                                      -- 恒等态射
  le_trans : ∀ {x y z}, Le x y → Le y z → Le x z            -- 态射的复合
  tensor : V → V → V
  unit : V
  -- 张量积是双函子：对态射也能“作用”
  tensor_mono : ∀ {x x' y y'}, Le x x' → Le y y' → Le (tensor x y) (tensor x' y')
  -- 严格的结合律与单位律（结合子、单位子都是恒等）
  assoc : ∀ x y z, tensor (tensor x y) z = tensor x (tensor y z)
  unit_tensor : ∀ x, tensor unit x = x
  tensor_unit : ∀ x, tensor x unit = x

/-- 在幺半预序 M 上富集的范畴：每对对象一个 hom-对象（M.V 中的元素），
    外加“复合态射存在”和“恒等态射存在”。 -/
structure EnrichedOverPreorder (M : ThinMonoidal) (Obj : Type) where
  hom : Obj → Obj → M.V
  /-- j_a : i → C(a, a) -/
  ident : ∀ a, M.Le M.unit (hom a a)
  /-- ∘ : C(b, c) ⊗ C(a, b) → C(a, c) -/
  comp : ∀ a b c, M.Le (M.tensor (hom b c) (hom a b)) (hom a c)
```

::: tip Lean 深入：字段是证明的结构体
`ThinMonoidal` 的有些字段是**数据**（`V`、`tensor`、`unit`），有些字段是**证明**（类型为 `Prop` 的 `le_refl`、`assoc`……）。
构造一个 `ThinMonoidal` 值时，你必须把数据和证明一起交出来——Lean 不会让你造出一个“不满足定律”的幺半预序。
这正是 Rust 的 trait 做不到的：Rust 只能在文档里写“实现者必须保证结合律”，Lean 把它写进了类型。

注意 `EnrichedOverPreorder` 里，`ident` 与 `comp` 的类型 `M.Le …` 是 `Prop`：在瘦的 $\mathcal{V}$ 里，
“给出一个 $\mathcal{V}$ 中的态射”与“证明这个态射存在”是一回事。
:::

## 预序

预序被定义为一个瘦范畴：每个 hom-集要么是空集，要么是单元素集合。我们把非空的 $\mathcal{C}(a, b)$ 解读为“$a$ 小于等于 $b$”的证明。
这样的范畴可以解读为在一个非常简单的幺半范畴上富集：这个幺半范畴只有两个对象 $0$ 和 $1$（有时也叫 *False* 和 *True*）。
除了必需的恒等态射，它只有一个态射，从 $0$ 指向 $1$，我们就叫它 $0 \to 1$。
它上面可以建立一个简单的幺半结构：张量积模仿 $0$ 和 $1$ 的简单算术（也就是说，唯一非零的乘积是 $1 \otimes 1$）。
这个范畴的单位对象是 $1$。它是一个**严格**幺半范畴：结合子和单位子都是恒等态射。

```diagram
Z: (0, 0) "0"
O: (2, 0) "1"
zo: Z -> O "0 \to 1"
idz: Z -> Z "\mathrm{id}_0" loop=left
ido: O -> O "\mathrm{id}_1" loop=right
caption: 只有两个对象的幺半范畴：0（假）与 1（真）。张量积是乘法（即逻辑“与”），单位是 1。
```

在 Lean 里，这就是 `Bool`：对象是 `false`、`true`；“从 $x$ 到 $y$ 有态射”就是“$x$ 为真蕴含 $y$ 为真”；张量积是 `&&`，单位是 `true`：

```lean
abbrev BoolV : ThinMonoidal where
  V := Bool
  Le x y := x = true → y = true        -- 只有 false → true 这一个非恒等态射
  le_refl _ := id
  le_trans h₁ h₂ := h₂ ∘ h₁
  tensor x y := x && y                  -- 0 ⊗ 0 = 0 ⊗ 1 = 1 ⊗ 0 = 0，1 ⊗ 1 = 1
  unit := true
  tensor_mono {x x' y y'} h₁ h₂ := by
    cases x <;> cases y <;> simp_all
  assoc x y z := by cases x <;> cases y <;> cases z <;> rfl
  unit_tensor x := by cases x <;> rfl
  tensor_unit x := by cases x <;> rfl

-- “态射 0 → 1 存在，1 → 0 不存在”
example : BoolV.Le false true := by decide
example : ¬ BoolV.Le true false := by decide
-- 张量积就是 0、1 的乘法表（逻辑与的真值表）
example : ∀ x y : Bool, (x && y) = true ↔ (x = true ∧ y = true) := by decide
```

::: tip Lean 深入：`abbrev`、`cases … <;> …` 与 `decide`
- `abbrev` 和 `def` 一样定义一个常量，但告诉 Lean“可以随时展开它”。这样 Lean 才能看穿 `BoolV.V` 其实就是 `Bool`，
  让数字字面量、`decide` 之类的机制正常工作。
- `cases x <;> cases y <;> simp_all`：`cases x` 把 `Bool` 拆成 `false`、`true` 两种情形；`<;>` 表示“对上一步产生的**每个**目标都执行下一步”。
  所以这一行就是“穷举所有真值组合，每种都交给 `simp_all` 化简”。
- `decide`：对“有限、可判定”的命题，让 Lean 直接**计算**出真假。真值表类的命题都可以这样秒杀。
:::

预序中 hom-集要么空、要么单元素，所以很容易把它换成我们这个小小范畴里的 hom-对象。
富集的预序 $\mathcal{C}$ 对任意一对对象 $a$、$b$ 都有一个 hom-对象 $\mathcal{C}(a, b)$：若 $a$ 小于等于 $b$，这个对象就是 $1$，否则就是 $0$。

来看复合。任意两个对象的张量积都是 $0$，除非两者都是 $1$，那时它才是 $1$。如果张量积是 $0$，复合态射有两种可能：
可以是 $\mathrm{id}_0$，也可以是 $0 \to 1$。但如果它是 $1$，唯一的选择就是 $\mathrm{id}_1$。
翻译回关系的语言，这就是说：若 $a \le b$ 且 $b \le c$，则 $a \le c$——这恰恰是我们需要的传递律。

恒等呢？它是一个从 $1$ 到 $\mathcal{C}(a, a)$ 的态射。从 $1$ 出发的态射只有一个，就是恒等 $\mathrm{id}_1$，所以 $\mathcal{C}(a, a)$ 必须是 $1$。
这意味着 $a \le a$——预序的自反律。所以，只要把预序实现为富集范畴，传递律和自反律就都**自动**成立了。

我们在 Lean 里把这两个方向都做一遍。先把自然数的 `≤` 包装成一个在 `BoolV` 上富集的范畴：

```lean
/-- 自然数的 ≤：hom-对象是一个布尔值 decide (a ≤ b) -/
def natLe : EnrichedOverPreorder BoolV Nat where
  hom a b := decide (a ≤ b)
  ident a := by simp          -- 目标：true = true → decide (a ≤ a) = true
  comp a b c := by
    simp                      -- 目标化为：b ≤ c → a ≤ b → a ≤ c
    omega

example : natLe.hom 3 5 = true := rfl
example : natLe.hom 5 3 = false := rfl
```

反过来，**任何**在 `BoolV` 上富集的范畴都给出一个预序——自反律来自 `ident`，传递律来自 `comp`，一行都不用多写：

```lean
/-- 从富集范畴读出关系：a ≤ b 当且仅当 hom-对象是 1（true） -/
def leOf {Obj : Type} (E : EnrichedOverPreorder BoolV Obj) (a b : Obj) : Prop :=
  E.hom a b = true

/-- 自反律 = 恒等态射 j_a : 1 → C(a, a) -/
theorem leOf_refl {Obj : Type} (E : EnrichedOverPreorder BoolV Obj) (a : Obj) :
    leOf E a a :=
  E.ident a rfl

/-- 传递律 = 复合 C(b, c) ⊗ C(a, b) → C(a, c) -/
theorem leOf_trans {Obj : Type} (E : EnrichedOverPreorder BoolV Obj) {a b c : Obj}
    (h₁ : leOf E a b) (h₂ : leOf E b c) : leOf E a c :=
  E.comp a b c (by simp [leOf] at *; simp [h₁, h₂])
```

::: tip Lean 深入：`omega`
`omega` 是 Lean 内置的**线性算术判定过程**：只要目标是关于整数/自然数的、由 `+`、`-`（自然数的截断减法）、乘以常数、
除以/模常数、`≤`、`<`、`=`、`∧`、`∨`、`¬` 组成的命题，它就能自动证明（或者告诉你不成立）。下一节的三角不等式全靠它。
:::

## 度量空间

一个有趣的例子来自 [William Lawvere](http://www.tac.mta.ca/tac/reprints/articles/1/tr1.pdf)。他注意到，度量空间可以用富集范畴来定义。
度量空间给任意两个对象之间定义了一个距离。这个距离是一个非负实数。把无穷大也算作可能的取值会很方便：如果距离是无穷大，就说明从起点根本到不了终点。

距离显然要满足一些性质。其一，一个对象到它自己的距离必须是零。其二是三角不等式：直达的距离，不会比中途经停的距离之和更长。
我们**不**要求距离是对称的。乍一听这有点怪，但正如 Lawvere 所说：你可以想象一个方向是上坡，另一个方向是下坡。
无论如何，对称性总可以事后作为附加约束加上去。

::: info 数学小课堂：度量空间
**度量空间**（metric space）就是“一个集合 + 一个距离函数 $d$”，满足：

1. $d(a, a) = 0$（自己到自己不用走）；
2. $d(a, c) \le d(a, b) + d(b, c)$（**三角不等式**：绕道不会更近）；
3. （通常还要求）$d(a, b) = d(b, a)$（对称），以及 $d(a, b) = 0 \Rightarrow a = b$。

例子：平面上的直线距离 $\sqrt{(x_1-x_2)^2 + (y_1-y_2)^2}$；城市街区里的“曼哈顿距离” $|x_1-x_2| + |y_1-y_2|$；
两个字符串之间的编辑距离（最少改几个字符）。

Lawvere 的版本只保留 1 和 2（并允许距离为 $\infty$），这样的东西叫 **Lawvere 度量空间**（Lawvere metric space）。
不对称的例子到处都是：登山时“上山的体力消耗”与“下山的体力消耗”不同；单行道很多的城市里，A 到 B 与 B 到 A 的车程也不同。
:::

那么，怎样把度量空间转换成范畴的语言？我们得构造一个范畴，它的 hom-对象就是距离。
请注意：距离不是态射，而是 **hom-对象**。一个 hom-对象怎么会是一个数？只有当我们能构造一个幺半范畴 $\mathcal{V}$、让这些数成为它的对象时，才行。
非负实数（加上无穷大）构成一个全序，所以可以看成一个瘦范畴。两个这样的数 $x$ 与 $y$ 之间有态射，当且仅当 $x \ge y$
（注意：这与预序定义里传统使用的方向正好相反）。幺半结构由加法给出，零充当单位对象。换句话说，两个数的张量积就是它们的和。

度量空间就是在这样一个幺半范畴上富集的范畴。从对象 $a$ 到 $b$ 的 hom-对象 $\mathcal{C}(a, b)$ 是一个非负（可能无穷大）的数，我们称之为从 $a$ 到 $b$ 的距离。
来看看这样的范畴里，恒等和复合会给出什么。

按我们的定义，从张量单位（也就是数零）到 hom-对象 $\mathcal{C}(a, a)$ 的态射，就是这个关系：

$$0 \ge \mathcal{C}(a, a)$$

由于 $\mathcal{C}(a, a)$ 是非负数，这个条件告诉我们：从 $a$ 到 $a$ 的距离永远是零。对上了！

再来说复合。我们从两个首尾相接的 hom-对象的张量积 $\mathcal{C}(b, c) \otimes \mathcal{C}(a, b)$ 出发。我们已经把张量积定义为两个距离之和。
复合是 $\mathcal{V}$ 中从这个积到 $\mathcal{C}(a, c)$ 的态射。而 $\mathcal{V}$ 中的态射被定义为“大于等于”关系。
换句话说：从 $a$ 到 $b$ 的距离加上从 $b$ 到 $c$ 的距离，大于等于从 $a$ 到 $c$ 的距离。这不就是标准的三角不等式吗？又对上了！

把度量空间重新表述为富集范畴，我们“免费”得到了三角不等式和零自距离。

### 把这件事讲透

这是本章最美的一个点子，值得停下来慢慢品味。把普通范畴、度量空间逐项对照：

| 普通范畴（在 $\mathbf{Set}$ 上富集） | 度量空间（在 $([0, \infty], \ge, +)$ 上富集） |
|---|---|
| hom-对象 $\mathcal{C}(a, b)$ 是一个**集合**：所有从 $a$ 到 $b$ 的路 | hom-对象 $\mathcal{C}(a, b)$ 是一个**数**：从 $a$ 到 $b$ 的距离 |
| $\mathcal{V}$ 中的态射是集合之间的函数 | $\mathcal{V}$ 中的态射是“$x \ge y$”这个事实 |
| 张量积是笛卡尔积 $\times$：“先选一条 $a \to b$ 的路，再选一条 $b \to c$ 的路” | 张量积是加法 $+$：“先走 $a \to b$，再走 $b \to c$，总路程相加” |
| 单位是单元素集合 $1$ | 单位是 $0$ |
| 复合：$\mathcal{C}(b,c) \times \mathcal{C}(a,b) \to \mathcal{C}(a,c)$，把两段路拼成一段 | 复合：$d(b,c) + d(a,b) \ge d(a,c)$，**三角不等式** |
| 恒等：$1 \to \mathcal{C}(a,a)$，挑出原地不动的那条路 | 恒等：$0 \ge d(a,a)$，原地不动不花路程 |
| 结合律、单位律（需要验证的等式） | 自动成立（瘦范畴里任意两条平行路线都相等） |

为什么方向要取 $\ge$ 而不是 $\le$？因为在富集范畴里，复合是一个**从**“两段路之和”**到**“直达距离”的态射。
在一个瘦范畴里，“存在从 $x$ 到 $y$ 的态射”应当理解为“$x$ 能推出/能换来 $y$”：
你手里有足够走完 $x$ 的预算，就一定够走完任何 $y \le x$ 的路程。所以“从大数指向小数”才是正确的方向。
若反过来取 $\le$，复合就会变成 $d(a,b) + d(b,c) \le d(a,c)$——绕路反而更近，这显然不是距离。

为什么张量积要取加法？因为“经过 $b$ 从 $a$ 到 $c$”的总代价就是两段代价相加——这正是加法作为“串联”运算的含义。
而 $0$ 是加法的单位，就像“不走路”是“走路”的单位。

最妙的是：**我们没有把三角不等式当作公理写进定义**。我们只说了“度量空间是富集范畴”，
而“富集范畴必须有复合”这条再普通不过的要求，在这个 $\mathcal{V}$ 里一翻译，就**是**三角不等式。同样，“必须有恒等态射”一翻译，就**是** $d(a,a) = 0$。
范畴论的“可复合”与几何的“不能抄近道”是同一件事。

下面这个小组件让你亲手验证。拖动平面上的点，选三个点 $a, b, c$，组件会实时计算
$\mathcal{C}(b, c) \otimes \mathcal{C}(a, b)$ 与 $\mathcal{C}(a, c)$，检查复合态射（即 $\ge$ 关系）是否存在。
你还可以切换到“上坡更费劲”的不对称距离，或者切换到“距离的平方”这个**反例**，看看复合在哪里断掉。

<div>
<Ch3_12MetricEnriched />
</div>

### 在 Lean 中：自然数距离与三角不等式

实数在不依赖 Mathlib 的 Lean 核心库里不好用，我们就用自然数 `Nat` 代替非负实数（暂时先不要无穷大）。
幺半预序 $(\mathbb{N}, \ge, +, 0)$ 写出来是这样的：

```lean
/-- Lawvere 的 V（自然数版）：对象是距离，x → y 当且仅当 x ≥ y，张量积是 +，单位是 0 -/
abbrev DistV : ThinMonoidal where
  V := Nat
  Le x y := x ≥ y
  le_refl x := Nat.le_refl x
  le_trans h₁ h₂ := Nat.le_trans h₂ h₁
  tensor x y := x + y
  unit := 0
  tensor_mono h₁ h₂ := Nat.add_le_add h₁ h₂   -- x ≥ x'、y ≥ y' ⟹ x + y ≥ x' + y'
  assoc := Nat.add_assoc
  unit_tensor := Nat.zero_add
  tensor_unit := Nat.add_zero
```

现在来造一个**不对称**的度量空间，正好对应 Lawvere 的“上坡/下坡”。设想一条山路，对象是海拔（自然数）。
上坡从 $a$ 爬到 $b$ 要花 $b - a$ 份体力，下坡不花体力。用 Lean 的截断减法（`3 - 10 = 0`）一行就写完：

```lean
/-- 登山距离：从海拔 a 到海拔 b 需要爬升 b - a（下坡免费） -/
def uphill : EnrichedOverPreorder DistV Nat where
  hom a b := b - a
  -- 恒等 j_a : 0 → C(a, a)，即 0 ≥ a - a
  ident a := by show 0 ≥ a - a; omega
  -- 复合 C(b, c) ⊗ C(a, b) → C(a, c)，即三角不等式 (c - b) + (b - a) ≥ c - a
  comp a b c := by show (c - b) + (b - a) ≥ c - a; omega

example : uphill.hom 3 10 = (7 : Nat) := rfl   -- 上山：爬 7
example : uphill.hom 10 3 = (0 : Nat) := rfl   -- 下山：免费
```

`comp` 字段的那个证明，就是三角不等式。它在 Lean 里的身份，是“富集范畴的复合态射”。你可以把它和本章开头的 `compUncurried` 对比一下：
那里复合是一个**函数**，这里复合是一个**证明**——因为在瘦的 $\mathcal{V}$ 里，态射就是证明。

::: tip Lean 深入：`show`
`show 目标` 把当前目标换成一个**定义上相等**的写法。`uphill` 的 `comp` 原本的目标是 `DistV.Le (DistV.tensor (hom b c) (hom a b)) (hom a c)`，
`omega` 看不懂这些包装；`show (c - b) + (b - a) ≥ c - a` 让 Lean 先把定义展开、确认两者一致，再把干净的算术目标交给 `omega`。
:::

对称的距离当然也行。数轴上的普通距离 $|a - b|$，用截断减法写成 $(a - b) + (b - a)$（两项中总有一项是零）；
网格上的曼哈顿距离是两个坐标方向的距离之和：

```lean
/-- 数轴上的距离 |a - b| -/
def lineDist : EnrichedOverPreorder DistV Nat where
  hom a b := (a - b) + (b - a)
  ident a := by show 0 ≥ _; omega
  comp a b c := by show _ + _ ≥ _; omega

/-- 网格上的曼哈顿距离 -/
def manhattan : EnrichedOverPreorder DistV (Nat × Nat) where
  hom p q := ((p.1 - q.1) + (q.1 - p.1)) + ((p.2 - q.2) + (q.2 - p.2))
  ident p := by show 0 ≥ _; omega
  comp p q r := by show _ + _ ≥ _; omega

example : lineDist.hom 2 9 = (7 : Nat) := rfl
example : manhattan.hom (0, 0) (3, 4) = (7 : Nat) := rfl
```

“距离的平方”不是度量：取 $a = 0, b = 1, c = 2$，两段各是 $1$，加起来是 $2$，直达却是 $4$。在富集的语言里，这就是说
“复合态射 $2 \to 4$ 不存在”。Lean 可以证明这样的 `EnrichedOverPreorder` **根本造不出来**：

```lean
theorem square_not_enriched :
    ¬ ∃ E : EnrichedOverPreorder DistV Nat, ∀ a b, E.hom a b = ((a - b) + (b - a)) * ((a - b) + (b - a)) := by
  intro ⟨E, hE⟩
  have h := E.comp 0 1 2             -- 复合态射：E.hom 1 2 + E.hom 0 1 ≥ E.hom 0 2
  simp only [DistV, hE] at h         -- 代入平方距离：1 + 1 ≥ 4
  omega                              -- 矛盾
```

::: details 补充：把无穷大也加进来
Lawvere 的 $\mathcal{V}$ 是 $[0, \infty]$，包括无穷大。我们可以给自然数补一个 `inf`，再验证它仍是幺半预序。
有了无穷大就能表达“到不了”：下面的“两个岛”例子里，偶数号城镇之间、奇数号城镇之间按数轴距离走，但偶数岛和奇数岛之间没有桥，距离是 $\infty$。
三角不等式依然成立——如果 $a$ 与 $c$ 不在同一个岛上，那么 $a \to b$ 与 $b \to c$ 中至少有一段跨岛，总和也是 $\infty$。

```lean
/-- 自然数 + 无穷大 -/
inductive Dist where
  | fin (n : Nat)
  | inf

/-- 加法：有一个是无穷大，和就是无穷大 -/
def Dist.add : Dist → Dist → Dist
  | .fin a, .fin b => .fin (a + b)
  | _, _ => .inf

/-- x ≥ y：无穷大大于等于一切；有限数不大于等于无穷大 -/
def Dist.Ge : Dist → Dist → Prop
  | .inf, _ => True
  | .fin _, .inf => False
  | .fin a, .fin b => a ≥ b

abbrev DistInfV : ThinMonoidal where
  V := Dist
  Le := Dist.Ge
  le_refl x := by cases x <;> simp [Dist.Ge]
  le_trans {x y z} h₁ h₂ := by
    cases x <;> cases y <;> cases z <;> simp_all [Dist.Ge] <;> omega
  tensor := Dist.add
  unit := .fin 0
  tensor_mono {x x' y y'} h₁ h₂ := by
    cases x <;> cases x' <;> cases y <;> cases y' <;> simp_all [Dist.Ge, Dist.add] <;> omega
  assoc x y z := by cases x <;> cases y <;> cases z <;> simp [Dist.add, Nat.add_assoc]
  unit_tensor x := by cases x <;> simp [Dist.add]
  tensor_unit x := by cases x <;> simp [Dist.add]

/-- 两个岛：同奇偶的城镇之间按数轴距离，异奇偶的城镇之间无法到达 -/
def islands : EnrichedOverPreorder DistInfV Nat where
  hom a b := if a % 2 = b % 2 then .fin ((a - b) + (b - a)) else .inf
  ident a := by simp [Dist.Ge]
  comp a b c := by
    by_cases h₁ : b % 2 = c % 2 <;> by_cases h₂ : a % 2 = b % 2 <;> by_cases h₃ : a % 2 = c % 2 <;>
      simp [h₁, h₂, h₃, Dist.Ge, Dist.add] <;> omega
```

`by_cases h : P` 把证明按“$P$ 成立 / 不成立”分成两支。三个 `by_cases` 一共分出 8 种情形，每种都交给 `simp` 化简、`omega` 收尾。
:::

::: tip Rust 视角：测试 vs. 证明
在 Rust 里你也可以写一个 `trait Metric { fn dist(&self, other: &Self) -> u64; }`，但三角不等式只能靠测试来“抽查”：

```rust
fn uphill(a: u64, b: u64) -> u64 {
    b.saturating_sub(a) // 截断减法，对应 Lean 的 Nat 减法
}

/// 只能在有限个样本上检查三角不等式
fn check_triangle(dist: impl Fn(u64, u64) -> u64, samples: &[u64]) -> bool {
    samples.iter().all(|&a| {
        samples.iter().all(|&b| {
            samples.iter().all(|&c| dist(b, c) + dist(a, b) >= dist(a, c))
        })
    })
}

#[test]
fn uphill_is_metric() {
    assert!(check_triangle(uphill, &[0, 1, 5, 10, 42]));
}
```

Lean 里的 `uphill.comp` 则对**所有**自然数一劳永逸地成立——那不是测试，是定理。
:::

## 富集函子

函子的定义涉及态射的映射。在富集的情形下，我们没有单个态射的概念，只能成批地处理 hom-对象。
hom-对象是幺半范畴 $\mathcal{V}$ 中的对象，我们手头有它们之间的态射可用。所以，当两个范畴在**同一个**幺半范畴 $\mathcal{V}$ 上富集时，
在它们之间定义富集函子才是合理的：这样我们就能用 $\mathcal{V}$ 中的态射，在两个富集范畴的 hom-对象之间建立映射。

两个范畴 $\mathcal{C}$ 和 $\mathcal{D}$ 之间的**富集函子**（enriched functor）$F$，除了把对象映到对象，还要给 $\mathcal{C}$ 中的每一对对象指定 $\mathcal{V}$ 中的一个态射：

$$F_{a b} \colon \mathcal{C}(a, b) \to \mathcal{D}(F a, F b)$$

函子是保持结构的映射。对普通函子而言，这意味着保持复合与恒等。在富集的情形下，保持复合意味着下面这个图交换：

```diagram
TL: (1.5, 0) "C_{bc} \otimes C_{ab}"
TR: (3, 1.4) "C_{ac}"
BL: (0, 1.4) "D_{Fb\,Fc} \otimes D_{Fa\,Fb}"
BR: (1.5, 2.8) "D_{Fa\,Fc}"
c: TL -> TR "\circ"
fl: TL -> BL "F \otimes F" side=right
fr: TR -> BR "F_{ac}"
d: BL -> BR "\circ" side=right
path "先复合再映射": c fr
path "先映射再复合": fl d color=green
caption: 富集函子保持复合（图中 D 表示 𝒟 的 hom-对象；左边的箭头是 F_bc ⊗ F_ab）。
```

保持恒等则换成：保持 $\mathcal{V}$ 中那些“挑出”恒等的态射：

```diagram
I: (1.5, 0) "i"
L: (0, 1.5) "C_{aa}"
R: (1.5, 3) "D_{Fa\,Fa}"
ja: I -> L "j_a" side=right
jfa: I -> R "j_{Fa}"
f: L -> R "F_{aa}" side=right
path "先挑恒等再映射": ja f
path "直接挑 Fa 的恒等": jfa color=green
caption: 富集函子保持恒等。
```

在 Lean 的简化版本里，富集函子只需要两样东西：对象上的映射 `obj`，以及对每对对象，$\mathcal{V}$ 中从 $\mathcal{C}(a,b)$ 到 $\mathcal{D}(Fa, Fb)$ 的态射（的存在证明）。
上面两个图因为 $\mathcal{V}$ 是瘦的而自动交换：

```lean
structure EnrichedFunctor {M : ThinMonoidal} {C D : Type}
    (EC : EnrichedOverPreorder M C) (ED : EnrichedOverPreorder M D) where
  obj : C → D
  /-- F_ab : C(a, b) → D(F a, F b) -/
  map : ∀ a b, M.Le (EC.hom a b) (ED.hom (obj a) (obj b))
```

翻译一下这意味着什么：

- 在 `BoolV` 上富集（预序）时，`map` 说的是“$a \le b$ 蕴含 $Fa \le Fb$”——富集函子就是**单调函数**。
- 在 `DistV` 上富集（度量空间）时，`map` 说的是 $d(a, b) \ge d(Fa, Fb)$——富集函子就是**不拉长距离的映射**
  （数学上叫非扩张映射、短映射或 1-Lipschitz 映射）。把地图缩小一半是富集函子；放大一倍就不是。

```lean
/-- 把海拔减半：所有爬升都不会变多，所以是富集函子 -/
def halve : EnrichedFunctor uphill uphill where
  obj n := n / 2
  map a b := by show b - a ≥ b / 2 - a / 2; omega

/-- 把海拔加倍：从 0 爬到 1 要 1 份体力，加倍后变成 2 份，距离被拉长了 -/
theorem double_not_functor : ¬ ∃ F : EnrichedFunctor uphill uphill, ∀ n, F.obj n = 2 * n := by
  intro ⟨F, hF⟩
  have h := F.map 0 1
  simp only [DistV, uphill, hF] at h
  omega

/-- 单调函数是预序之间的富集函子 -/
def succMono : EnrichedFunctor natLe natLe where
  obj n := n + 1
  map a b := by simp [natLe]
```

## 自富集

闭的对称幺半范畴可以**自富集**（self-enriched）：用内部 hom（见上面的定义）代替 hom-集。
为此，我们得给内部 hom 定义复合律。换句话说，我们要实现一个具有如下签名的态射：

$$[b, c] \otimes [a, b] \to [a, c]$$

这和任何其他编程任务没什么两样，只不过在范畴论里，我们通常用无点的方式实现。我们先确定它应该是哪个集合中的元素。在这里，它是这个 hom-集的成员：

$$\mathcal{V}([b, c] \otimes [a, b], [a, c])$$

这个 hom-集同构于：

$$\mathcal{V}(([b, c] \otimes [a, b]) \otimes a, c)$$

我只是用了定义内部 hom $[a, c]$ 的那个伴随。如果我们能在这个新集合里造出一个态射，伴随就会把我们指向原集合里对应的态射，我们就可以拿它当复合。
我们把手头可用的几个态射复合起来，造出这个态射。首先，可以用结合子 $\alpha_{[b, c]\,[a, b]\,a}$ 把左边的表达式重新结合：

$$([b, c] \otimes [a, b]) \otimes a \to [b, c] \otimes ([a, b] \otimes a)$$

接着用伴随的余单位 $\varepsilon_{a b}$：

$$[b, c] \otimes ([a, b] \otimes a) \to [b, c] \otimes b$$

再用一次余单位 $\varepsilon_{b c}$，就到达 $c$ 了。这样我们就造出了一个态射：

$$\varepsilon_{b c} \circ (\mathrm{id}_{[b, c]} \otimes \varepsilon_{a b}) \circ \alpha_{[b, c]\,[a, b]\,a}$$

它是这个 hom-集的元素：

$$\mathcal{V}(([b, c] \otimes [a, b]) \otimes a, c)$$

伴随就会给出我们要找的复合律。

```diagram
A: (0, 0) "([b,c] \otimes [a,b]) \otimes a"
B: (0, 1.3) "[b,c] \otimes ([a,b] \otimes a)"
C: (0, 2.6) "[b,c] \otimes b"
D: (0, 3.9) "c"
al: A -> B "\alpha"
e1: B -> C "\mathrm{id}\otimes\varepsilon"
e2: C -> D "\varepsilon_{bc}"
path "挪括号、求值、再求值": al e1 e2
caption: 自富集中复合律的构造：结合子 α、id ⊗ ε_ab、ε_bc 这三个现成的态射首尾相接，再由伴随（柯里化）变成 [b,c] ⊗ [a,b] → [a,c]。
```

同样，恒等

$$j_a \colon i \to [a, a]$$

是下面这个 hom-集的成员：

$$\mathcal{V}(i, [a, a])$$

通过伴随，它同构于：

$$\mathcal{V}(i \otimes a, a)$$

我们知道这个 hom-集里有左单位子 $\lambda_a$。我们可以把 $j_a$ 定义为它在伴随下的像。

自富集的一个实际例子是范畴 $\mathbf{Set}$，它是编程语言中类型的原型。我们以前见过，它相对于笛卡尔积是一个闭幺半范畴。
在 $\mathbf{Set}$ 中，任意两个集合之间的 hom-集本身也是一个集合，所以它是 $\mathbf{Set}$ 中的对象。我们知道它同构于指数集合，所以外部 hom 和内部 hom 是等价的。
现在我们又知道，通过自富集，我们可以把指数集合当作 hom-对象，并用指数对象的笛卡尔积来表达复合。

### 在 Lean 中：照着公式一步步拼出复合

上面那串无点的推导，在 Lean 里可以**逐字**照抄。`curryT` 扮演伴随（柯里化），`assocT` 是结合子，`evalT` 是余单位，`tensorMap` 是 $\otimes$ 作用在态射上：

```lean
section SelfEnrich
variable {a b c : Type}

/-- 复合律 [b, c] ⊗ [a, b] → [a, c] = curry(ε_bc ∘ (id ⊗ ε_ab) ∘ α) -/
def compInternal : (b → c) × (a → b) → (a → c) :=
  curryT (evalT ∘ tensorMap id evalT ∘ assocT)

/-- 它确实就是普通的函数复合！ -/
example (g : b → c) (f : a → b) : compInternal (g, f) = g ∘ f := rfl

/-- 恒等 j_a : i → [a, a] = curry(λ_a) -/
def jInternal : Unit → (a → a) := curryT unitorL

example : jInternal () = (id : a → a) := rfl

end SelfEnrich
```

两个 `rfl` 告诉我们：从“结合子 + 余单位 + 伴随”这些抽象零件拼出来的东西，**计算结果**与我们熟悉的 `∘` 和 `id` 完全一样。

我们的两个瘦的 $\mathcal{V}$ 也都是闭的，因而也都能自富集。这里有一个令人愉快的发现：

```lean
-- BoolV 是闭的：(a ∧ b ⇒ c) ⟺ (a ⇒ (b ⇒ c))，内部 hom [b, c] 就是蕴含 !b || c
example (a b c : Bool) :
    ((a && b) = true → c = true) ↔ (a = true → (!b || c) = true) := by
  cases a <;> cases b <;> cases c <;> decide

-- DistV 是闭的：a + b ≥ c ⟺ a ≥ c - b，内部 hom [b, c] 就是截断减法 c - b
example (a b c : Nat) : a + b ≥ c ↔ a ≥ c - b := by omega

/-- BoolV 在自己上面富集：hom-对象是蕴含 -/
def boolSelf : EnrichedOverPreorder BoolV Bool where
  hom a b := !a || b
  ident a := by cases a <;> decide
  comp a b c := by cases a <;> cases b <;> cases c <;> decide
```

而 `DistV` 的内部 hom $[a, b] = b - a$——这正是前面的 `uphill`！原来，“登山距离”这个不对称度量空间，就是 Lawvere 的 $\mathcal{V}$
在**它自己**上面的富集：从数 $a$ 到数 $b$ 的“距离”，是“已经有了 $a$，还差多少才够 $b$”。

## 与 2-范畴的关系

我曾在 $\mathbf{Cat}$——（小）范畴的范畴——的语境下谈过 2-范畴。范畴之间的态射是函子，但还有额外的结构：函子之间的自然变换。
在 2-范畴里，对象常被称为 0-胞（zero-cell），态射称为 1-胞，态射之间的态射称为 2-胞。
在 $\mathbf{Cat}$ 中，0-胞是范畴，1-胞是函子，2-胞是自然变换。

但请注意，两个范畴之间的函子本身也构成一个范畴；所以在 $\mathbf{Cat}$ 中，我们真正拥有的是 **hom-范畴**（hom-category），而不是 hom-集。
事实证明，就像 $\mathbf{Set}$ 可以看作在 $\mathbf{Set}$ 上富集的范畴一样，$\mathbf{Cat}$ 也可以看作在 $\mathbf{Cat}$ 上富集的范畴。
更一般地，正如每个范畴都可以看作在 $\mathbf{Set}$ 上富集，每个 2-范畴都可以看作在 $\mathbf{Cat}$ 上富集。

::: tip Lean 深入：hom-范畴长什么样
取 `Type` 上的类型构造器 `Type → Type`（比如 `List`、`Option`）作为“函子”，它们之间的“自然变换”是多态函数 `∀ α, F α → G α`。
这些多态函数之间可以（垂直）复合、有恒等，并满足结合律——也就是说，从 `Type` 到 `Type` 的函子们构成一个范畴。
这个范畴就是 2-范畴 $\mathbf{Cat}$ 中，从 `Type` 到 `Type` 的 hom-对象：

```lean
/-- 从 F 到 G 的（未检查自然性的）多态函数 -/
def NT (F G : Type → Type) : Type 1 := ∀ α, F α → G α

def NT.vcomp {F G H : Type → Type} (β : NT G H) (α : NT F G) : NT F H :=
  fun t x => β t (α t x)
def NT.idn (F : Type → Type) : NT F F := fun _ x => x

-- hom-范畴的结合律与单位律，都是 rfl
example {F G H K : Type → Type} (α : NT F G) (β : NT G H) (γ : NT H K) :
    NT.vcomp γ (NT.vcomp β α) = NT.vcomp (NT.vcomp γ β) α := rfl
example {F G : Type → Type} (α : NT F G) : NT.vcomp (NT.idn G) α = α := rfl

def headOpt : NT List Option := fun _ xs => xs.head?
def optToList : NT Option List := fun _ o => o.toList
example : NT.vcomp optToList headOpt Nat [1, 2, 3] = [1] := rfl
```

注意 `NT F G` 住在 `Type 1` 里：它对所有类型 `α : Type` 量化，所以比 `Type` 大一层——又是本章开头讲过的宇宙层级。
:::

## 挑战

原书本章没有挑战题。下面是为本书补充的练习，帮助你巩固“富集 = hom 换成 $\mathcal{V}$ 中的对象”这一想法。

1. **离散度量**：证明“相同则距离为 0，不同则距离为 1”是一个在 `DistV` 上富集的范畴（对象可以是任意带可判定相等的类型）。
2. **复合富集函子**：证明两个富集函子（在同一个 $M$ 上）可以复合，得到一个富集函子。对度量空间，这意味着“两个不拉长距离的映射复合起来，仍不拉长距离”。
3. **恒等富集函子**：写出任意富集范畴上的恒等富集函子。
4. **一个不是度量空间的“距离”**：证明 $d(a, b) = 2$（对所有 $a, b$，包括 $a = b$）不能构成在 `DistV` 上富集的范畴。它违反了哪一条：恒等还是复合？
5. **对称化**：给定在 `DistV` 上富集的 `E`，证明 $d'(a, b) = d(a, b) + d(b, a)$ 也给出一个在 `DistV` 上富集的范畴，并且它是对称的。
   把它用在 `uphill` 上，你得到了什么？
6. （思考题）在 `BoolV` 上富集的范畴就是预序。如果把 `BoolV` 的张量积从 `&&` 换成 `||`（单位换成 `false`），它还是幺半预序吗？
   在它上面富集的范畴，复合和恒等分别说了什么？

::: details 参考答案
```lean
-- 1. 离散度量
def discrete (Obj : Type) [DecidableEq Obj] : EnrichedOverPreorder DistV Obj where
  hom a b := if a = b then 0 else 1
  ident a := by simp
  comp a b c := by
    show (if b = c then 0 else 1) + (if a = b then 0 else 1) ≥ (if a = c then 0 else 1)
    -- 分情况：b = c？a = b？a = c？每种情形都是具体的 0/1 算术
    by_cases h₁ : b = c <;> by_cases h₂ : a = b <;> by_cases h₃ : a = c <;> simp_all

-- 2. 富集函子的复合：把两步 ≥ 用 le_trans 接起来
def EnrichedFunctor.comp {M : ThinMonoidal} {C D E : Type}
    {EC : EnrichedOverPreorder M C} {ED : EnrichedOverPreorder M D} {EE : EnrichedOverPreorder M E}
    (G : EnrichedFunctor ED EE) (F : EnrichedFunctor EC ED) : EnrichedFunctor EC EE where
  obj x := G.obj (F.obj x)
  map a b := M.le_trans (F.map a b) (G.map (F.obj a) (F.obj b))

-- 3. 恒等富集函子：用 V 中的恒等态射
def EnrichedFunctor.idn {M : ThinMonoidal} {C : Type} (EC : EnrichedOverPreorder M C) :
    EnrichedFunctor EC EC where
  obj x := x
  map a b := M.le_refl (EC.hom a b)

-- 4. 常数 2：违反的是恒等（0 ≥ 2 不成立）；复合 2 + 2 ≥ 2 倒是成立的
theorem const_two_not_enriched :
    ¬ ∃ E : EnrichedOverPreorder DistV Nat, ∀ a b, E.hom a b = 2 := by
  intro ⟨E, hE⟩
  have h : 0 ≥ E.hom 0 0 := E.ident 0
  simp only [DistV, hE] at h
  omega

-- 5. 对称化
def symmetrize {Obj : Type} (E : EnrichedOverPreorder DistV Obj) :
    EnrichedOverPreorder DistV Obj where
  hom a b := E.hom a b + E.hom b a
  ident a := by
    have h : 0 ≥ E.hom a a := E.ident a
    show 0 ≥ E.hom a a + E.hom a a
    simp only [DistV] at h ⊢
    omega
  comp a b c := by
    have h₁ : E.hom b c + E.hom a b ≥ E.hom a c := E.comp a b c
    have h₂ : E.hom b a + E.hom c b ≥ E.hom c a := E.comp c b a
    show (E.hom b c + E.hom c b) + (E.hom a b + E.hom b a) ≥ E.hom a c + E.hom c a
    simp only [DistV] at h₁ h₂ ⊢
    omega

theorem symmetrize_symm {Obj : Type} (E : EnrichedOverPreorder DistV Obj) (a b : Obj) :
    (symmetrize E).hom a b = (symmetrize E).hom b a := by
  show E.hom a b + E.hom b a = E.hom b a + E.hom a b
  simp only [DistV]
  omega

-- 对 uphill 对称化，得到的就是数轴上的普通距离 lineDist
example (a b : Nat) : (symmetrize uphill).hom a b = lineDist.hom a b := by
  show (b - a) + (a - b) = (a - b) + (b - a)
  omega
```

6. 是的：`||` 满足结合律，`false` 是它的单位，并且它对“蕴含”单调，所以 `(Bool, ⇒, ||, false)` 也是幺半预序。
   但在它上面富集的范畴就很怪了：恒等要求 $\mathrm{false} \Rightarrow \mathcal{C}(a, a)$，这永远成立，什么也没说；
   复合要求“$\mathcal{C}(b,c)$ **或** $\mathcal{C}(a,b)$ 为真，就有 $\mathcal{C}(a,c)$ 为真”，这是一个比传递律强得多的条件。
   例如取 $\mathcal{C}(x, y) = \mathrm{true}$（对所有 $x, y$）或 $\mathcal{C}(x, y) = \mathrm{false}$（对所有 $x, y$）都行，但普通的 $\le$ 不行
   （$1 \le 2$ 为真，可 $2 \le 0$ 为假）。这说明：选择不同的幺半结构，“富集范畴”这个概念的含义会彻底改变。
:::

## 本章小结

- **富集范畴**把 hom-集 $\mathcal{C}(a, b)$ 换成某个**幺半范畴** $\mathcal{V}$ 中的 hom-对象。对象一般没有元素，所以一切都要用“无点”的方式、作用在 hom-对象整体上来表述。
- 复合变成 $\mathcal{V}$ 中的态射 $\mathcal{C}(b,c) \otimes \mathcal{C}(a,b) \to \mathcal{C}(a,c)$；恒等变成 $j_a \colon i \to \mathcal{C}(a,a)$。结合律、单位律用结合子与单位子画成交换图。
- **幺半范畴**：张量积 $\otimes$ 在自然同构意义下结合、有单位，满足五边形与三角形相干条件。在 Lean 的 `Type` 中，这些都可以用 `funext` + `rfl` 证明。
- **闭**幺半范畴的内部 hom $[b, c]$ 是 $\otimes$ 的右伴随；在 `Type` 里它就是函数类型，伴随就是柯里化。
- **预序**是在 $\{0, 1\}$（Lean 的 `Bool`，张量积为 `&&`）上富集的范畴：复合就是传递律，恒等就是自反律。
- **度量空间**是在 $([0, \infty], \ge, +)$ 上富集的范畴（Lawvere）：复合**就是**三角不等式，恒等**就是** $d(a, a) = 0$。在 Lean 里，三角不等式成了结构体的一个字段，由 `omega` 证明。
- **富集函子**用 $\mathcal{V}$ 中的态射映射 hom-对象：对预序是单调函数，对度量空间是不拉长距离的映射。
- 闭对称幺半范畴可以**自富集**：在 `Type` 里，按公式拼出的内部复合就是 `∘`；而 Lawvere 的 $\mathcal{V}$ 自富集，恰好得到“登山距离” $b - a$。
- 2-范畴（如 $\mathbf{Cat}$）可以看作在 $\mathbf{Cat}$ 上富集：hom 不再是集合，而是一个范畴（函子与自然变换）。
