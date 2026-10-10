# 2.5 米田引理

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

structure NatTrans {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    (F G : CFunctor C D) where
  app : (a : C) → (F.obj a ⟶ G.obj a)
  naturality : ∀ {a b : C} (f : a ⟶ b), G.map f ⊚ app a = app b ⊚ F.map f

infixr:50 " ⟹ " => NatTrans

end CTFP

open CTFP Category

/-- hom 函子 `C(a, -)`（见 2.4）。 -/
def homFunctor {C : Type u} [Category.{u, v} C] (a : C) : CFunctor C (Type v) where
  obj x := a ⟶ x
  map f := fun h => f ⊚ h
  map_id x := by funext h; exact id_comp h
  map_comp f g := by funext h; exact (assoc h f g).symm

/-- 两个自然变换的分量全都相等，它们就相等（自然性证明是命题，自动相等）。 -/
theorem NatTrans.ext' {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    {F G : CFunctor C D} {α β : F ⟹ G} (h : ∀ x, α.app x = β.app x) : α = β := by
  cases α with
  | mk app₁ nat₁ =>
    cases β with
    | mk app₂ nat₂ =>
      have : app₁ = app₂ := funext h
      subst this
      rfl
```

范畴论里的大多数构造，都是把其他更具体的数学分支里早已有之的结果加以推广。积、余积、幺半群、指数对象……这些东西在范畴论诞生之前就广为人知，只是在不同的数学分支里顶着不同的名字：集合论里的笛卡尔积、序理论里的“交”（meet）、逻辑里的合取——它们都是“范畴积”这个抽象概念的具体实例。

**米田引理**（Yoneda lemma）在这方面就显得与众不同了。它是一个关于“一般范畴”的、气势恢宏的论断，在其他数学分支里几乎找不到先例。有人说，和它最接近的是群论中的**凯莱定理**（Cayley's theorem）：每个群都同构于某个集合上的一个置换群。

::: info 数学小课堂：凯莱定理——“一个东西 = 它能做的事”
**群**是一个带乘法的集合，有单位元、每个元素都有逆、乘法满足结合律。比如“钟面上的 0、1、2 点，按模 3 相加”就是一个三元素的群 $\mathbb{Z}_3$。

凯莱定理的思想是：别管元素“是什么”，看它“做什么”。元素 $1$ 做的事是“让每个元素加 1”，也就是把 $0 \mapsto 1, 1 \mapsto 2, 2 \mapsto 0$ 这样转一圈——这是集合 $\{0, 1, 2\}$ 的一个**置换**（重新排列）。每个元素都对应一个置换，不同的元素对应不同的置换，而且元素相乘恰好对应置换的复合。于是群“就是”一组置换。

米田引理把这个思想推广到了任意范畴：**一个对象，完全可以由“从它出发的所有箭头”来刻画**。在 [2.6 米田嵌入](/part2/06-yoneda-embedding) 的挑战题里，你会看到凯莱定理正是米田引理在“只有一个对象的范畴”（幺半群）上的特例。
:::

米田引理的舞台是一个任意的范畴 $\mathcal{C}$，外加一个从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的函子 $F$。上一章我们看到，有些取值于 $\mathbf{Set}$ 的函子是可表的，即与某个 hom 函子同构。米田引理则告诉我们：**所有**取值于 $\mathbf{Set}$ 的函子都可以经由自然变换从 hom 函子得到，而且它把这样的自然变换一个不漏地清点了出来。

在讲自然变换的时候我提到过，自然性条件的约束力可以非常强。当你在一个对象上定义了自然变换的分量之后，自然性往往足以把这个分量“运送”到任何通过态射与它相连的对象上。源范畴和目标范畴里对象之间的箭头越多，你在运送分量时受到的约束就越多。而 $\mathbf{Set}$ 恰好是一个箭头极其丰富的范畴。

米田引理说的是：从 hom 函子到任意函子 $F$ 的一个自然变换，**只要指定它在一个点上的一个分量的取值，就被完全确定了**！自然变换的其余部分全都由自然性条件推出来。

这听起来好得难以置信。我们一步一步来，先把直觉建立起来，再用 Lean 把它证死。

## 自然性条件，再看一遍

先回顾一下米田引理中涉及的两个函子之间的自然性条件。

第一个函子是 hom 函子。对 $\mathcal{C}$ 中一个固定的对象 $a$，它把任意对象 $x$ 映到态射集合 $\mathcal{C}(a, x)$；我们也看到了，它把任意态射 $f : x \to y$ 映到 $\mathcal{C}(a, f)$（后接 $f$）。

第二个函子是一个任意的 $\mathbf{Set}$ 值函子 $F$。

把这两个函子之间的自然变换叫做 $\alpha$。由于我们是在 $\mathbf{Set}$ 中工作，自然变换的分量——比如 $\alpha_x$、$\alpha_y$——就是集合之间的普通函数：

$$\alpha_x : \mathcal{C}(a, x) \to F x \qquad \alpha_y : \mathcal{C}(a, y) \to F y$$

![两个分量](/img/2.5/yoneda1.png "自然变换 α 的两个分量 α_x、α_y：它们都是 Set 中的普通函数。")

既然只是函数，我们就可以看它们在某个具体点上的取值。可 $\mathcal{C}(a, x)$ 这个集合里的“点”是什么呢？关键的观察就在这里：**$\mathcal{C}(a, x)$ 中的每个点，同时也是一个从 $a$ 到 $x$ 的态射 $h$**。一个东西，两重身份——它既是集合里的元素，又是范畴里的箭头。米田引理的全部魔力都来自这种双重身份。

于是，$\alpha$ 的自然性方块

$$\alpha_y \circ \mathcal{C}(a, f) = F f \circ \alpha_x$$

在作用到 $h$ 上时，逐点地变成了

$$\alpha_y (\mathcal{C}(a, f)\, h) = (F f) (\alpha_x\, h)$$

你也许还记得上一章的内容：hom 函子 $\mathcal{C}(a, -)$ 在态射 $f$ 上的作用就是复合：

$$\mathcal{C}(a, f)\, h = f \circ h$$

代进去，得到

$$\alpha_y (f \circ h) = (F f) (\alpha_x\, h)$$

这个条件到底有多强？只要把它特化到 $x = a$ 的情形就能看出来。

![特化到 x = a](/img/2.5/yoneda2.png "让 x 就是 a 本身：这时 h 是一个从 a 到 a 的态射。")

这时 $h$ 变成了从 $a$ 到 $a$ 的态射。我们知道至少有一个这样的态射：$h = \mathrm{id}_a$。把它代进去：

$$\alpha_y\, f = (F f) (\alpha_a\, \mathrm{id}_a)$$

（左边本来是 $\alpha_y(f \circ \mathrm{id}_a)$，由单位律它就是 $\alpha_y\, f$。）

请仔细看刚才发生了什么。等式左边是 $\alpha_y$ 作用在 $\mathcal{C}(a, y)$ 的一个**任意**元素 $f$ 上的结果；而右边只依赖于**一个**值：$\alpha_a$ 在 $\mathrm{id}_a$ 处的取值。我们可以任意挑选这个值，它都会生成一个自然变换。既然 $\alpha_a$ 的取值落在集合 $F a$ 中，$F a$ 中的**任何**一个点都定义了某个 $\alpha$。

下面的图把这个“追元素”的过程画了出来：左上角是 $\mathcal{C}(a, a)$ 里的点 $\mathrm{id}_a$，右上角是它在 $F a$ 中的像 $q = \alpha_a(\mathrm{id}_a)$。从 $\mathrm{id}_a$ 出发有两条路走到 $F y$：

```diagram
id: (0, 0.6) "\mathrm{id}_a"
q: (3, 0.6) "q"
f: (0, 2.4) "f"
Ffq: (3, 2.4) "F f\,q"
s1: (0, 0) "\mathcal{C}(a, a)" color=gray
s2: (3, 0) "F a" color=gray
s3: (0, 3) "\mathcal{C}(a, y)" color=gray
s4: (3, 3) "F y" color=gray
aa: id -> q "\alpha_a"
caf: id -> f "\mathcal{C}(a, f)" side=right
ff: q -> Ffq "F f"
ay: f -> Ffq "\alpha_y" side=right
path "先 α_a，再 F f": aa ff
path "先 C(a, f)，再 α_y": caf ay color=green
caption: 从 id_a 出发：C(a, f) 把 id_a 送到 f ∘ id_a = f；自然性要求 α_y f = (F f) q
```

反过来，给定任意一个从 $\mathcal{C}(a, -)$ 到 $F$ 的自然变换 $\alpha$，把它在 $\mathrm{id}_a$ 处求值，就得到 $F a$ 中的一个点。

我们刚刚证明了米田引理：

> 从 $\mathcal{C}(a, -)$ 到 $F$ 的自然变换，与 $F a$ 的元素之间，存在一一对应。

换句话说，

$$\mathrm{Nat}(\mathcal{C}(a, -), F) \cong F a$$

或者，如果我们用 $[\mathcal{C}, \mathbf{Set}]$ 表示从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的函子范畴，那么自然变换的集合就是这个范畴里的一个 hom-集，于是可以写成

$$[\mathcal{C}, \mathbf{Set}](\mathcal{C}(a, -), F) \cong F a$$

稍后（在下一章）我会解释，这个对应其实还是一个**自然**同构。

::: info 数学小课堂：读懂这个公式
- 左边是一个**集合**：它的元素是“从 hom 函子到 $F$ 的自然变换”。每个元素都是一个庞然大物——对**每个**对象 $x$ 都有一个函数 $\alpha_x$，而且它们彼此满足自然性。
- 右边也是一个**集合**：$F$ 在 $a$ 处的值，元素就是一个个普普通通的点。
- $\cong$ 说：这两个集合能一一配对。还记得上一章说的吗？比较元素种类完全不同的集合是可以的——这里我们正是把“一族函数”和“一个点”拿来比较。

用一句话记住它：**一个从 $\mathcal{C}(a, -)$ 出发的自然变换，等价于它在 $\mathrm{id}_a$ 上的取值**。
:::

## 补充：用 Lean 证明米田引理（任意范畴）

上面那段论证短得惊人，但每一步都值得推敲。好消息是：它可以被**原封不动地**写成 Lean，而且只需要十几行。

两个方向的映射：

- `yonedaTo`：给一个自然变换 `α`，在 `𝟙 a` 处求值，得到 `F.obj a` 的一个元素。
- `yonedaFrom`：给一个元素 `q : F.obj a`，构造自然变换：分量 `α_x` 把 `h : a ⟶ x` 送到 `F.map h q`。

```lean
section general
variable {C : Type u} [Category.{u, v} C]

/-- 自然变换 ↦ 它在 id_a 处的值。 -/
def yonedaTo (a : C) (F : CFunctor C (Type v)) (α : homFunctor a ⟹ F) : F.obj a :=
  α.app a (𝟙 a)

/-- 元素 q ↦ 自然变换 h ↦ F h q。 -/
def yonedaFrom (a : C) (F : CFunctor C (Type v)) (q : F.obj a) : homFunctor a ⟹ F where
  app x := fun h => F.map h q
  -- 自然性：F f (F h q) = F (f ∘ h) q —— 这正是函子保持复合
  naturality {x y} f := by
    funext (h : a ⟶ x)
    show F.map f (F.map h q) = F.map (f ⊚ h) q
    exact (congrFun (F.map_comp h f) q).symm

end general
```

注意构造自然变换时，我们**必须**提供自然性的证明——`NatTrans` 结构体就是这么要求的。这里的证明恰好就是函子 `F` 的复合律 `map_comp`。

接下来是两条往返定理。先证“元素 → 自然变换 → 元素”回到原处，它只用到函子的**恒等律**：

```lean
theorem yoneda_to_from {C : Type u} [Category.{u, v} C] (a : C) (F : CFunctor C (Type v))
    (q : F.obj a) : yonedaTo a F (yonedaFrom a F q) = q := by
  -- 左边按定义就是 F (id_a) q
  show F.map (𝟙 a) q = q
  rw [F.map_id]   -- F 把 id 映到 id
  rfl
```

再证“自然变换 → 元素 → 自然变换”回到原处。这一步才是米田引理真正的核心——它要用到 `α` 的**自然性**，正是我们上面那个“特化到 $h = \mathrm{id}_a$”的论证：

```lean
theorem yoneda_from_to {C : Type u} [Category.{u, v} C] (a : C) (F : CFunctor C (Type v))
    (α : homFunctor a ⟹ F) : yonedaFrom a F (yonedaTo a F α) = α := by
  apply NatTrans.ext'          -- 只需证明每个分量相等
  intro x
  funext (h : a ⟶ x)           -- 再逐点证明
  show F.map h (α.app a (𝟙 a)) = α.app x h
  -- α 在 h 上的自然性方块，作用到 id_a：F h (α_a id_a) = α_x (h ∘ id_a)
  have nat : F.map h (α.app a (𝟙 a)) = α.app x (h ⊚ 𝟙 a) :=
    congrFun (α.naturality h) (𝟙 a)
  rw [nat, comp_id]            -- h ∘ id_a = h
```

就这样，米田引理在**任意**范畴、**任意** $\mathbf{Set}$ 值函子上被机器验证了。把它和原书的纸面论证对照着读：`congrFun (α.naturality h) (𝟙 a)` 就是“把自然性方块作用在点 $\mathrm{id}_a$ 上”，`comp_id` 就是“$h \circ \mathrm{id}_a = h$”。

::: tip Lean 深入：几个用到的工具
- `NatTrans.ext'`（在本章开头的隐藏代码里定义）：两个自然变换只要分量都相等就相等。为什么不用管自然性证明？因为证明是 `Prop` 类型的，而 Lean 有**证明无关性**：同一个命题的任意两个证明都被视为相等。
- `congrFun : f = g → ∀ x, f x = g x`：从“函数相等”得到“逐点相等”。`α.naturality h` 是两个函数（`Set` 里的态射）相等，作用到 `𝟙 a` 上就得到点的等式。
- `show` 把目标改写成一个与之**定义上相等**的、更易读的形式。这里它帮我们把 `homFunctor`、`typeCategory` 的定义展开掉。
:::

## 结晶：自然变换如何从一个点长出来

现在我们来培养一点关于这个结果的直觉。最令人惊叹的是：整个自然变换都从**一个**成核点结晶出来——那就是我们在 $\mathrm{id}_a$ 处给它指定的值。它从这一点出发，沿着自然性条件向外蔓延，最终充满 $\mathcal{C}$ 在 $\mathbf{Set}$ 中的整个像。那么，先来看看 $\mathcal{C}$ 在 $\mathcal{C}(a, -)$ 下的像是什么样子。

从 $a$ 本身的像开始。在 hom 函子 $\mathcal{C}(a, -)$ 下，$a$ 被映到集合 $\mathcal{C}(a, a)$；而在函子 $F$ 下，它被映到集合 $F a$。自然变换的分量 $\alpha_a$ 是某个从 $\mathcal{C}(a, a)$ 到 $F a$ 的函数。我们只盯住 $\mathcal{C}(a, a)$ 中的一个点——对应于态射 $\mathrm{id}_a$ 的那个点。为了强调它只是集合中的一个点，我们叫它 $p$。分量 $\alpha_a$ 应当把 $p$ 映到 $F a$ 中的某个点 $q$。我将向你说明：**无论 $q$ 怎么选，都会得到唯一的一个自然变换**。

![成核点](/img/2.5/yoneda3.png "α_a 把点 p（也就是 id_a）映到 F a 中的点 q。")

**第一个论断**：选定一个点 $q$，就唯一地决定了函数 $\alpha_a$ 的其余部分。确实如此：在 $\mathcal{C}(a, a)$ 中任取另一个点 $p'$，它对应着某个从 $a$ 到 $a$ 的态射 $g$。米田引理的魔法就发生在这里：$g$ 既可以被看作集合 $\mathcal{C}(a, a)$ 中的一个点 $p'$，同时它又挑出了两个集合之间的**函数**。在 hom 函子下，态射 $g$ 被映成函数 $\mathcal{C}(a, g)$；在 $F$ 下，它被映成 $F g$。

![g 的双重身份](/img/2.5/yoneda4.png "态射 g : a → a 既是 C(a, a) 里的点 p'，又被两个函子分别映成函数 C(a, g) 和 F g。")

现在来看 $\mathcal{C}(a, g)$ 作用在我们最初的 $p$ 上会怎样——别忘了，$p$ 对应的是 $\mathrm{id}_a$。这个作用定义为复合 $g \circ \mathrm{id}_a$，它等于 $g$，也就是我们的点 $p'$。所以，态射 $g$ 被映成了这样一个函数：它作用在 $p$ 上，产生的恰好是 $p'$——也就是 $g$ 自己。我们绕了一整圈！

再来看 $F g$ 作用在 $q$ 上：它给出 $F a$ 中的某个点 $q'$。为了让自然性方块交换，$\alpha_a$ 必须把 $p'$ 映到 $q'$。我们挑的是任意的 $p'$（任意的 $g$），并推出了它在 $\alpha_a$ 下的像。所以函数 $\alpha_a$ 被完全确定了。

**第二个论断**：对 $\mathcal{C}$ 中任何与 $a$ 相连的对象 $x$，$\alpha_x$ 也被唯一确定。推理是类似的，只不过现在多了两个集合 $\mathcal{C}(a, x)$ 和 $F x$。从 $a$ 到 $x$ 的态射 $g$ 在 hom 函子下被映成

$$\mathcal{C}(a, g) : \mathcal{C}(a, a) \to \mathcal{C}(a, x)$$

在 $F$ 下被映成

$$F g : F a \to F x$$

同样，$\mathcal{C}(a, g)$ 作用在 $p$ 上给出复合 $g \circ \mathrm{id}_a$，它对应 $\mathcal{C}(a, x)$ 中的某个点 $p'$。自然性决定了 $\alpha_x$ 在 $p'$ 上的值必须是

$$q' = (F g)\, q$$

由于 $p'$ 是任意的，整个函数 $\alpha_x$ 就被确定了。

![蔓延到其他对象](/img/2.5/yoneda5.png "沿着态射 g : a → x，自然性把 q 运送为 F g q，于是 α_x 也被确定。")

那 $\mathcal{C}$ 中**与 $a$ 毫无联系**的对象呢？在 $\mathcal{C}(a, -)$ 下，它们全都被映到同一个集合——空集。回忆一下，空集是集合范畴的始对象：从它到任何集合都有唯一一个函数，我们叫它 `absurd`（在 Lean 里，从空类型出发的唯一函数是 `Empty.elim`，或者对任意空类型用 `nomatch`）。所以在这里，自然变换的分量同样没有选择余地：只能是 `absurd`。

::: tip 换个说法：为什么每个分量都被“逼死”了
把上面两个论断合起来，就是一句话：$\mathcal{C}(a, x)$ 里的每个元素 $g$，都可以写成 $\mathcal{C}(a, g)(\mathrm{id}_a)$——也就是“把 $\mathrm{id}_a$ 沿着 $g$ 推过去”。**hom 函子里的每个元素都是从 $\mathrm{id}_a$ 推出来的**，所以自然变换在每个元素上的值，也都只能是从 $q$ 推出来的。$\mathrm{id}_a$ 是一粒种子，hom 函子是从这粒种子长出来的“自由”的东西；而“自由”的意思恰恰是：你只需要决定种子去哪儿。
:::

下面这张“米田表格”让你亲手做一遍这件事。我们取 $\mathcal{C} = $ `Type`、$a = $ `Bool`，hom 函子就是 `Reader Bool`，即 `Bool → -`。你选定 `F Bool` 中的一个元素 $q$（种子），表格会把每个分量 $\alpha_x(h)$ 一格一格地填出来。试着篡改其中一格——你会发现，任何改动都会立刻破坏某个自然性方块。

<div class="ctfp-ch-widget"><Ch2_5YonedaTable /></div>

理解米田引理的另一种方式，是意识到：$\mathbf{Set}$ 值函子之间的自然变换只不过是一族函数，而函数一般是**有损**的。一个函数可能把信息压扁（把不同的输入送到同一个输出），也可能只覆盖值域的一部分。唯一无损的函数是可逆的那些——同构。由此可见，最能保持结构的 $\mathbf{Set}$ 值函子就是可表函子：要么就是 hom 函子本身，要么与 hom 函子自然同构。其他任何函子 $F$，都是从某个 hom 函子经过一个有损变换得到的。这样的变换不仅可能丢失信息，还可能只覆盖了 $F$ 在 $\mathbf{Set}$ 中的像的一小部分。

::: info 数学小课堂：“有损”的例子
在表格里选 `F = Option`、种子 `q = none`：所有的 $\alpha_x(h)$ 都是 `none`。这个自然变换把 hom 函子里所有丰富的信息（每一个函数 `h`）全都压扁成了一个 `none`——极度有损。

再选 `q = some true`：这时 $\alpha_x(h) = $ `some (h true)`。它只“看了” `h` 在 `true` 处的值，`h false` 的信息丢掉了；而且它永远到不了 `none`，只覆盖了 `Option x` 的一部分。

只有当 $F$ 本身可表（比如 `F = Reader Bool`，取种子 `q = id`）时，这个变换才是无损的同构。
:::

## Lean 中的米田引理

我们在 Lean 里已经以 Reader 函子的面目见过 hom 函子：

```lean
def Reader (a x : Type) := a → x

instance : Functor (Reader a) where
  map f h := f ∘ h
```

Reader 把态射（这里就是函数）映成“与之复合”。米田引理告诉我们：Reader 函子可以被自然地映到**任何**其他函子。

自然变换就是多态函数。所以给定一个函子 `F`，从 Reader 函子到它的映射是：

```lean no-check
alpha : {x : Type} → (a → x) → F x
```

米田引理说，这样的自然变换与 `F a` 的元素一一对应：

```lean no-check
({x : Type} → (a → x) → F x)  ≅  F a
```

这个等式的右边，是我们平时会认为是**数据结构**的东西。还记得“函子是广义的容器”这种解读吗？`F a` 就是一个装着 `a` 的容器。而左边是一个以函数为参数的**多态函数**。米田引理告诉我们：这两种表示是等价的——它们包含完全相同的信息。

换个说法就是：给我一个这种类型的多态函数

```lean no-check
alpha : {x : Type} → (a → x) → F x
```

我就能造出一个装着 `a` 的容器。诀窍就是我们在证明米田引理时用过的那一招：用 `id` 去调用这个函数，就得到 `F a` 的一个元素：

```lean no-check
alpha id : F a
```

反过来也成立：给定一个 `F a` 类型的值

```lean no-check
fa : F a
```

就可以定义一个类型正确的多态函数：

```lean no-check
fun h => h <$> fa      -- 也就是 Functor.map h fa
```

你可以轻松地在两种表示之间来回切换。

### 把它写成定理：为什么需要自然性

在 Haskell 里，故事到此为止——参数性保证了一切。在 Lean 里，我们想把“来回切换互为逆”**证明**出来。这时会碰到一个有趣的障碍。

先试着用裸的多态函数类型 `{x : Type} → (a → x) → F x` 来证。

- 方向一，“`F a` → 多态函数 → `F a`”：`id <$> fa = fa`，这正是函子定律 `id_map`，没问题。
- 方向二，“多态函数 → `F a` → 多态函数”：我们需要对任意 `h` 证明 `h <$> alpha id = alpha h`。这是 `alpha` 在 `h` 上的自然性条件，作用到 `id` 上。**但是一个裸的多态函数并不自带自然性的证明**，我们无从下手。

更要命的是，这不只是“证不出来”，而是**真的不成立**。因为 Lean 有经典逻辑，我们可以写出一个“偷看类型”的伪多态函数。下面这个 `sneaky` 在 `x` 恰好是 `Bool` 时返回 `none`，其他时候老老实实返回 `some (h ())`：

```lean
/-- Unit 和 Bool 不是同一个类型：Bool 有两个不同的值，Unit 没有。 -/
theorem unit_ne_bool : Unit ≠ Bool := by
  intro h
  have key : ∀ p q : Bool, p = q := by
    rw [← h]           -- 把 Bool 换回 Unit
    intro p q
    rfl                -- Unit 的任意两个值都相等
  exact Bool.noConfusion (key true false)

open Classical in
/-- 一个“偷看类型”的伪多态函数。只能 noncomputable：程序在运行时无法比较类型。 -/
noncomputable def sneaky {x : Type} (h : Unit → x) : Option x :=
  if x = Bool then none else some (h ())
```

它在 `id` 处的值是 `some ()`；按 `psi` 把这个值还原回多态函数，在 `x := Bool`、`h := fun _ => true` 处应该给出 `some true`——可 `sneaky` 给的是 `none`。往返失败了：

```lean
-- φ(sneaky) = sneaky id = some ()
example : sneaky (x := Unit) id = some () := by
  simp [sneaky, unit_ne_bool]

-- ψ(φ(sneaky)) 在 Bool 处 ≠ sneaky 在 Bool 处
example : (fun _ => true) <$> sneaky (x := Unit) id ≠ sneaky (x := Bool) (fun _ => true) := by
  simp [sneaky, unit_ne_bool]
```

这就是为什么在 Lean 中，我们要把自然变换定义为**带自然性证明的结构体**。“多态”不足以保证“自然”；必须把自然性写进类型里，就像 `NatTrans` 那样。

::: tip Lean 深入：`noncomputable` 与 `open Classical in`
`if x = Bool then ... else ...` 需要判定“两个类型是否相等”，而这是不可计算的——运行中的程序根本没有类型信息。`open Classical in` 引入了经典逻辑的“排中律”实例，使得任何命题都能用在 `if` 里；代价是这个定义没法生成可执行代码，必须标为 `noncomputable`。这类定义在证明里很常见，在程序里则不会出现。它恰好说明：Lean 的逻辑比 Haskell 的类型系统更强，强到能写出违反参数性的东西——所以自然性必须被显式要求。
:::

下面是对 Lean 自带的 `Functor` 类型类的米田引理。自然变换被定义为一个结构体：一个多态函数 `app`，外加它的自然性证明：

```lean
/-- 从 Reader a 到 F 的自然变换：多态函数 + 自然性。 -/
structure YonedaNat (a : Type) (F : Type → Type) [Functor F] where
  app : {x : Type} → (a → x) → F x
  naturality : ∀ {x y : Type} (f : x → y) (h : a → x), f <$> app h = app (f ∘ h)
```

为了证明 `F` 满足函子定律，我们要求它是 `LawfulFunctor`。这个类型类把两条定律写进了 Lean：

- `id_map : id <$> x = x`
- `comp_map : (h ∘ g) <$> x = h <$> g <$> x`

```lean
section yonedaType
variable {F : Type → Type} [Functor F] [LawfulFunctor F] {a : Type}

/-- φ：自然变换 ↦ 在 id 处的值。 -/
def phi (α : YonedaNat a F) : F a := α.app id

/-- ψ：容器 ↦ 自然变换 h ↦ h <$> fa。自然性由 comp_map 给出。 -/
def psi (fa : F a) : YonedaNat a F where
  app h := h <$> fa
  naturality f h := (comp_map h f fa).symm

omit [LawfulFunctor F] in
/-- 两个 YonedaNat 只要 app 逐点相等就相等。 -/
theorem YonedaNat.ext' {α β : YonedaNat a F}
    (h : ∀ {x : Type} (k : a → x), α.app k = β.app k) : α = β := by
  cases α with
  | mk app₁ nat₁ =>
    cases β with
    | mk app₂ nat₂ =>
      have : @app₁ = @app₂ := by
        funext x k
        exact h k
      subst this
      rfl

/-- F a → Nat → F a：只用到函子的恒等律。 -/
theorem phi_psi (fa : F a) : phi (psi fa) = fa := by
  show id <$> fa = fa
  exact id_map fa

/-- Nat → F a → Nat：需要 α 的自然性！ -/
theorem psi_phi (α : YonedaNat a F) : psi (phi α) = α := by
  apply YonedaNat.ext'
  intro x k
  show k <$> α.app id = α.app k
  rw [α.naturality k id]   -- k <$> α id = α (k ∘ id)
  rfl                      -- k ∘ id 按定义就是 k

end yonedaType
```

这里的 `omit [LawfulFunctor F] in` 告诉 Lean：这条定理用不着 `LawfulFunctor` 这个假设，别把它自动加进来。`@app₁` 中的 `@` 表示“把隐式参数也当成显式的来看”，这样我们才能把 `app₁` 当作一个普通函数来比较。

对照一下两条定理分别用了什么：

| 往返方向 | 需要的东西 |
|---|---|
| `F a → Nat → F a` | 函子 `F` 的恒等律 `id_map` |
| `Nat → F a → Nat` | 自然变换 `α` 的自然性 |
| 构造 `psi fa` 的自然性 | 函子 `F` 的复合律 `comp_map` |

函子的两条定律和自然性，各司其职，一条都不多余。

### 两种表示，各有所长

拥有多种表示的好处在于：其中一种可能比另一种更容易复合，或者在某些应用中更高效。

这一原理最简单的例证，是编译器构造中常用的一种代码变换：**续延传递风格**（continuation passing style，CPS）。它是米田引理在**恒等函子**上最简单的应用。把 `F` 换成恒等函子，得到：

```lean no-check
({r : Type} → (a → r) → r)  ≅  a
```

Lean 的恒等函子叫 `Id`，`Id r` 就是 `r` 本身，它的 `map` 就是函数应用。所以这只是上面定理的一个特例：

```lean
-- 恒等函子的米田：phi / psi 直接拿来用
def toCPS {a : Type} (x : a) : YonedaNat a Id := psi (F := Id) x
def fromCPS {a : Type} (k : YonedaNat a Id) : a := phi k

example : fromCPS (toCPS (42 : Nat)) = 42 := phi_psi (F := Id) _
-- 一个 CPS 值：拿到“后续处理函数” k，就把 42 交给它
example : (toCPS (42 : Nat)).app (fun n => s!"答案是 {n}") = "答案是 42" := rfl
```

这个公式的解读是：任何类型 `a` 的值，都可以换成一个“接收 `a` 的处理器（handler）”的函数。处理器就是一个接受 `a` 并完成剩余计算的函数——也就是**续延**（continuation）。（类型 `r` 通常装着某种状态码。）

这种编程风格在 UI、异步系统和并发编程中非常普遍。CPS 的缺点是它带来了**控制反转**：代码被拆分为生产者和消费者（处理器），不容易复合。任何做过一定规模的 Web 编程的人，都熟悉由一堆互相影响、各自带状态的处理器交织而成的“意大利面条代码”噩梦。我们后面会看到，审慎地使用函子和单子，可以恢复 CPS 的某些可复合性（见 [3.5 单子与副作用](/part3/05-monads-and-effects) 中的续延单子）。

::: tip Rust 视角：回调风格就是 CPS
Rust 程序员对“把值交给回调”再熟悉不过了。下面两个函数信息量完全相同——米田引理（恒等函子版）说的就是这件事：

```rust
struct User { name: String }

// 直接风格：返回一个值
fn get_user() -> User {
    User { name: "Ferris".to_string() }
}

// CPS 风格：不返回值，而是把值交给调用者提供的续延 k
fn with_user<R>(k: impl FnOnce(User) -> R) -> R {
    k(User { name: "Ferris".to_string() })
}

pub fn demo() -> usize {
    let a = get_user().name.len();
    // 用恒等函数“取回”值：with_user(|u| u) 就是 φ(alpha) = alpha id
    let b = with_user(|u| u).name.len();
    // 直接在回调里继续计算
    let c = with_user(|u| u.name.len());
    a + b + c
}
```

`with_user` 对返回类型 `R` 是泛型的：它没法凭空造出一个 `R`，唯一的办法就是调用 `k`——所以它必然“藏着”一个 `User`。当回调一层套一层（`with_db(|db| with_user(|u| with_perm(|p| ...)))`），你就得到了“回调地狱”；`async`/`.await` 正是把它扳回直接风格的语法糖。
:::

## 余米田（co-Yoneda）

和往常一样，把箭头方向反过来，我们又白赚一个构造。把米田引理应用到对偶范畴 $\mathcal{C}^{op}$ 上，就得到一个关于逆变函子的映射。

等价地，我们也可以通过固定 hom 函子的**终点**而不是起点来推导余米田引理。这样得到的是从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的逆变 hom 函子 $\mathcal{C}(-, a)$。米田引理的逆变版本，在从这个函子到任意其他逆变函子 $F$ 的自然变换，与集合 $F a$ 的元素之间，建立了一一对应：

$$\mathrm{Nat}(\mathcal{C}(-, a), F) \cong F a$$

Lean 版本的余米田引理：

```lean no-check
({x : Type} → (x → a) → F x)  ≅  F a      -- 这里 F 是逆变函子
```

注意，在某些文献中，被叫做“米田引理”的恰恰是这个逆变版本。

证明和协变版本如出一辙：在 `id` 处求值是一个方向，`contramap h fa` 是另一个方向。Lean 核心库没有 `Contravariant`，我们定义一个带定律的版本：

```lean
class Contravariant (f : Type → Type) where
  contramap : {α β : Type} → (β → α) → f α → f β

class LawfulContravariant (f : Type → Type) [Contravariant f] : Prop where
  contramap_id : ∀ {α : Type} (x : f α), Contravariant.contramap id x = x
  contramap_comp : ∀ {α β γ : Type} (g : β → α) (h : γ → β) (x : f α),
    Contravariant.contramap (g ∘ h) x = Contravariant.contramap h (Contravariant.contramap g x)

/-- 从 C(-, a) 到逆变函子 G 的自然变换。 -/
structure CoYonedaNat (a : Type) (G : Type → Type) [Contravariant G] where
  app : {x : Type} → (x → a) → G x
  naturality : ∀ {x y : Type} (f : y → x) (h : x → a),
    Contravariant.contramap f (app h) = app (h ∘ f)
```

::: details 余米田引理的完整证明
```lean
section co
variable {G : Type → Type} [Contravariant G] [LawfulContravariant G] {a : Type}

def coPhi (α : CoYonedaNat a G) : G a := α.app id

def coPsi (ga : G a) : CoYonedaNat a G where
  app h := Contravariant.contramap h ga
  naturality f h := (LawfulContravariant.contramap_comp h f ga).symm

theorem coPhi_coPsi (ga : G a) : coPhi (coPsi ga) = ga :=
  LawfulContravariant.contramap_id ga

theorem coPsi_coPhi (α : CoYonedaNat a G) : coPsi (coPhi α) = α := by
  cases α with
  | mk app nat =>
    -- 关键一步仍然是自然性：contramap h (app id) = app (id ∘ h) = app h
    have : (fun {x} (h : x → a) => Contravariant.contramap h (app id)) = @app := by
      funext x h
      exact nat h id
    simp only [coPsi, coPhi]
    congr

end co
```
:::

::: warning 易错点：Haskell 库里的 `Coyoneda` 是另一回事
如果你以后读 Haskell 资料，会在 `kan-extensions` 库里碰到一个叫 `Coyoneda` 的类型：`data Coyoneda f a = forall x. Coyoneda (x -> a) (f x)`。它针对的是**协变**函子，用的是“存在量词”而不是“全称量词”，表达的是 $\exists x.\, (x \to a) \times F x \cong F a$。这是米田引理的另一种对偶形式（我们在 [3.10 端与余端](/part3/10-ends-and-coends) 中会理解它），和本节的逆变版本不是同一个东西。名字撞车而已，别搞混。
:::

## 挑战

1. 证明构成 Lean 中米田同构的两个函数 `phi` 和 `psi` 互为逆。

   ```lean no-check
   def phi (α : YonedaNat a F) : F a := α.app id
   def psi (fa : F a) : YonedaNat a F := ⟨fun h => h <$> fa, ...⟩
   ```

2. **离散范畴**是只有对象、除了恒等态射之外没有任何态射的范畴。对于从这种范畴出发的函子，米田引理是怎样运作的？
3. 单元素列表 `List Unit` 除了长度之外不包含任何信息。所以作为一种数据类型，它可以看作整数的一种编码：空列表编码 0，单元素列表 `[()]`（这里指一个值，不是类型）编码 1，以此类推。利用列表函子的米田引理，构造这个数据类型的另一种表示。

::: details 参考答案

**1.** 就是正文中的 `phi_psi` 与 `psi_phi`。总结一下要点：`phi (psi fa) = id <$> fa = fa` 用的是函子恒等律；`psi (phi α) = α` 要逐点证明 `k <$> α.app id = α.app k`，这是 `α` 在 `k` 处的自然性条件作用于 `id`（再用 `k ∘ id = k`）。如果像 Haskell 那样把自然变换当作裸的多态函数，第二个方向在 Lean 中**不成立**——`sneaky` 就是反例。

**2.** 设离散范畴的对象构成类型 `I`。从 `a` 到 `x` 的态射只有 `a = x` 时才存在（就是恒等态射），所以 hom 函子 $\mathcal{C}(a, -)$ 把 $a$ 映到单元素集 $\{\mathrm{id}_a\}$，把其余所有对象映到空集。函子 $F$ 就是一族集合 $F : I \to \mathbf{Set}$（没有非平凡的态射需要映射，也就没有函子性需要验证）。自然变换在 $a$ 处的分量 $\{\mathrm{id}_a\} \to F a$ 等价于挑选 $F a$ 中的一个元素；在其他对象处的分量都是从空集出发的 `absurd`，别无选择；而自然性条件只涉及恒等态射，自动满足。所以 $\mathrm{Nat}(\mathcal{C}(a, -), F) \cong F a$，米田引理在这里几乎是显然的。

在 Lean 里，可以直接用**相等类型** `a = x` 充当离散范畴的 hom-集。米田引理就变成：

```lean
section discrete
variable {I : Type} {F : I → Type} {a : I}

def discPhi (α : ∀ x, a = x → F x) : F a := α a rfl
def discPsi (q : F a) : ∀ x, a = x → F x := fun _ h => h ▸ q

example (q : F a) : discPhi (discPsi q) = q := rfl

example (α : ∀ x, a = x → F x) : discPsi (discPhi α) = α := by
  funext x h
  cases h        -- h : a = x，“拆开”它就是令 x := a、h := rfl
  rfl

end discrete
```

`h ▸ q` 的意思是“沿着等式 `h : a = x` 把 `q : F a` 搬运成 `F x` 的元素”。有趣的是：这个“离散米田引理”正是 Lean 中等式的**消去规则**（俗称 J 规则）——要对所有 `x` 和所有 `a = x` 定义一个东西，只需要定义 `x := a`、证明为 `rfl` 的那一种情形。`cases h` 这个 tactic 背后用的就是它。

**3.** 列表函子的米田引理给出

$$\texttt{List Unit} \cong \forall x.\, (\texttt{Unit} \to x) \to \texttt{List}\ x \cong \forall x.\, x \to \texttt{List}\ x$$

（第二步用了 `Unit → x ≅ x`：从单元素类型出发的函数，就等同于挑出 `x` 的一个值。）所以自然数的另一种表示是：一个多态函数，给它任意类型的一个值 `v`，它返回一个由 `v` 构成的列表。由自然性，它只能把 `v` 重复若干次——那个次数就是它编码的自然数。在 Lean 中，同样要把自然性写进结构体：

```lean
instance : LawfulFunctor List where
  map_const := rfl
  id_map := List.map_id
  comp_map _ _ _ := (List.map_map ..).symm

/-- 自然数的“米田编码”：给我一个 v，我还你一串 v。 -/
structure YNat where
  run : {x : Type} → x → List x
  naturality : ∀ {x y : Type} (f : x → y) (v : x), (run v).map f = run (f v)

def YNat.ofNat (n : Nat) : YNat := ⟨fun v => List.replicate n v, by intros; simp⟩
def YNat.toNat (c : YNat) : Nat := (c.run ()).length

theorem YNat.toNat_ofNat (n : Nat) : (YNat.ofNat n).toNat = n := by
  simp [YNat.toNat, YNat.ofNat]

theorem YNat.ofNat_toNat (c : YNat) : YNat.ofNat c.toNat = c := by
  cases c with
  | mk run nat =>
    -- 由自然性：run v = (run ()).map (fun _ => v) = replicate (run ()).length v
    have : (fun {x} (v : x) => List.replicate (run ()).length v) = @run := by
      funext x v
      have h := nat (fun _ => v) ()
      rw [List.map_const'] at h
      exact h
    simp only [YNat.ofNat, YNat.toNat]
    congr

example : (YNat.ofNat 3).run "喵" = ["喵", "喵", "喵"] := rfl
```

注意：Lean 核心库并没有为 `List` 提供 `LawfulFunctor` 实例，所以我们自己证明了一个（三条定律都由标准库里关于 `List.map` 的引理直接给出）。有了它，正文中的通用 `phi`/`psi` 也可以直接用在列表上：

```lean
example : phi (psi (F := List) [(), (), ()]) = [(), (), ()] := phi_psi _
example : (psi (F := List) [(), ()]).app (fun _ => 'x') = ['x', 'x'] := rfl
```
:::

## 参考资料

1. The Catsters 关于米田引理的[视频](https://www.youtube.com/watch?v=TLMxHB19khE)。

## 本章小结

- **米田引理**：$\mathrm{Nat}(\mathcal{C}(a, -), F) \cong F a$。从 hom 函子出发的自然变换，与 $F a$ 的元素一一对应。
- 关键观察：$\mathcal{C}(a, x)$ 的元素**既是集合里的点，又是范畴里的箭头**。$\mathrm{id}_a$ 是一粒种子，hom 函子的每个元素 $g$ 都等于 $\mathcal{C}(a, g)(\mathrm{id}_a)$。
- 两个方向：$\alpha \mapsto \alpha_a(\mathrm{id}_a)$；$q \mapsto (h \mapsto F h\, q)$。自然性把种子 $q$ 运送到每一个分量；与 $a$ 不相连的对象，分量只能是 `absurd`。
- 我们在 Lean 中对**任意范畴、任意 $\mathbf{Set}$ 值函子**证明了米田引理：一个方向用函子的恒等律，另一个方向用自然性。
- 在类型范畴里：`({x} → (a → x) → F x) ≅ F a`。左边是多态函数，右边是数据结构——同样的信息，不同的形态。
- Lean 里**自然性不是免费的**：借助经典逻辑可以写出偷看类型的伪多态函数 `sneaky`，它会让往返失败。所以自然变换要定义为“函数 + 自然性证明”的结构体。
- 恒等函子的特例就是 **CPS**：`({r} → (a → r) → r) ≅ a`。回调风格与直接风格信息等价，但回调风格难以复合。
- **余米田**：对逆变函子，`({x} → (x → a) → F x) ≅ F a`，有的文献把它叫做米田引理。
- 一句话直觉：**一个从 $\mathcal{C}(a, -)$ 出发的自然变换，完全由它对 $\mathrm{id}_a$ 做了什么来决定。**
