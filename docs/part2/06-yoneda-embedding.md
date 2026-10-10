# 2.6 米田嵌入

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

/-- 自然变换的外延性（见 2.5）。 -/
theorem NatTrans.ext' {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    {F G : CFunctor C D} {α β : F ⟹ G} (h : ∀ x, α.app x = β.app x) : α = β := by
  cases α with
  | mk app₁ nat₁ =>
    cases β with
    | mk app₂ nat₂ =>
      have : app₁ = app₂ := funext h
      subst this
      rfl

/-- 自然变换的垂直复合与恒等自然变换（见 1.10）。 -/
def NatTrans.vcomp {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    {F G H : CFunctor C D} (β : G ⟹ H) (α : F ⟹ G) : F ⟹ H where
  app x := β.app x ⊚ α.app x
  naturality {x y} f := by
    rw [assoc, β.naturality, ← assoc, α.naturality, assoc]

def NatTrans.ident {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂} [Category.{u₂, v₂} D]
    (F : CFunctor C D) : F ⟹ F where
  app x := 𝟙 (F.obj x)
  naturality f := by rw [id_comp, comp_id]
```

前面我们看到，在范畴 $\mathcal{C}$ 中固定一个对象 $a$，映射 $\mathcal{C}(a, -)$ 就是一个从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的（协变）函子：

$$x \mapsto \mathcal{C}(a, x)$$

（值域之所以是 $\mathbf{Set}$，是因为 hom-集 $\mathcal{C}(a, x)$ 是一个**集合**。）我们管这个映射叫 hom 函子——之前已经定义过它在态射上的作用了。

现在，让这个映射里的 $a$ 也动起来。我们得到一个新的映射：它给每个 $a$ 指派一个 hom-**函子** $\mathcal{C}(a, -)$。

$$a \mapsto \mathcal{C}(a, -)$$

这是一个把范畴 $\mathcal{C}$ 的对象映到函子的映射，而函子是**函子范畴**中的**对象**（参见 [1.10 自然变换](/part1/10-natural-transformations) 里关于函子范畴的小节）。我们用 $[\mathcal{C}, \mathbf{Set}]$ 表示从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的函子范畴。你可能还记得，hom 函子是 [可表函子](/part2/04-representable-functors) 的原型。

::: info 数学小课堂：“函子”也能当“对象”
这里的思维跳跃值得停下来体会一下。在 $[\mathcal{C}, \mathbf{Set}]$ 这个范畴里：

- 一个**对象**是一整个函子 $F : \mathcal{C} \to \mathbf{Set}$——它本身就是一大堆数据（每个对象一个集合、每个态射一个函数）；
- 一个**态射**是两个函子之间的自然变换。

这就像在 Rust 里把一个实现了某个 trait 的类型当成值来传递（`Box<dyn Trait>`）：昨天它还是“规则”，今天它变成了被操作的“数据”。米田嵌入就是把 $\mathcal{C}$ 的每个对象 $a$ 变成这个大范畴里的一个对象 $\mathcal{C}(a, -)$。
:::

每当我们手里有一个两范畴之间的对象映射，很自然就会问：它是不是一个函子？换句话说，能不能把一个范畴里的态射提升为另一个范畴里的态射？$\mathcal{C}$ 中的态射就是 $\mathcal{C}(a, b)$ 中的一个元素，而函子范畴 $[\mathcal{C}, \mathbf{Set}]$ 中的态射是自然变换。所以我们要找的，是一个从态射到自然变换的映射。

来看看能不能为一个态射 $f : a \to b$ 找到对应的自然变换。先看 $a$ 和 $b$ 被映到哪里：它们被映成两个函子，$\mathcal{C}(a, -)$ 和 $\mathcal{C}(b, -)$。我们需要的是这两个函子之间的一个自然变换。

诀窍在这里：我们用米田引理

$$[\mathcal{C}, \mathbf{Set}](\mathcal{C}(a, -), F) \cong F a$$

并把其中一般的 $F$ 换成 hom 函子 $\mathcal{C}(b, -)$。得到：

$$[\mathcal{C}, \mathbf{Set}](\mathcal{C}(a, -), \mathcal{C}(b, -)) \cong \mathcal{C}(b, a)$$

![米田嵌入](/img/2.6/yoneda-embedding.jpg "用 hom 函子 C(b, -) 代替米田引理中的 F：两个 hom 函子之间的自然变换，与 C(b, a) 中的态射一一对应。")

这正是我们要找的两个 hom 函子之间的自然变换，只是带了个小小的转折：我们得到的是自然变换与一个态射——$\mathcal{C}(b, a)$ 的元素——之间的对应，而这个态射走的是“反”方向。不过没关系，这只说明我们面对的函子是**逆变**的。

![方向反转](/img/2.6/yoneda-embedding-2.jpg "C 中从 b 到 a 的态射，对应于从 C(a, -) 到 C(b, -) 的自然变换：方向反过来了。")

具体是哪个自然变换呢？按米田引理的配方，元素 $f \in \mathcal{C}(b, a)$ 对应的自然变换在 $x$ 处的分量把 $h \in \mathcal{C}(a, x)$ 送到 $\mathcal{C}(b, h)(f) = h \circ f$。也就是说：**它就是“前接 $f$”**。给一个从 $a$ 出发的箭头 $h$，在它前面接上 $f : b \to a$，就得到一个从 $b$ 出发的箭头 $h \circ f$。

```diagram
b: (0, 0.9)
a: (1.6, 0.9)
x: (3.4, 0.9)
f: b -> a "f" side=right
h: a -> x "h" side=right
hf: b -> x "h \circ f" bend=50 color=brand
path "先 f 再 h": f h
path "h ∘ f": hf color=green
caption: 米田嵌入把 f : b → a 变成自然变换 C(a, -) ⟹ C(b, -)，其分量是“前接 f”：h ↦ h ∘ f
```

实际上，我们得到的比预想的还要多。从 $\mathcal{C}$ 到 $[\mathcal{C}, \mathbf{Set}]$ 的这个映射不仅是一个逆变函子——它还是一个**全忠实**（fully faithful）函子。全和忠实是函子的两种性质，描述的是函子如何映射 hom-集。

**忠实**（faithful）函子在 hom-集上是**单射**（injective）：它把不同的态射映到不同的态射。换句话说，它不会把态射“粘”在一起。

**全**（full）函子在 hom-集上是**满射**（surjective）：它把一个 hom-集映**满**另一个 hom-集，一个不落地覆盖后者。

全忠实函子 $F$ 在 hom-集上是**双射**（bijection）——两边所有元素一一配对。对源范畴 $\mathcal{C}$ 中的每一对对象 $a$ 和 $b$，$\mathcal{C}(a, b)$ 与 $\mathcal{D}(F a, F b)$ 之间都有一个双射，其中 $\mathcal{D}$ 是 $F$ 的目标范畴（我们这里就是函子范畴 $[\mathcal{C}, \mathbf{Set}]$）。注意，这并**不**意味着 $F$ 在**对象**上是双射。$\mathcal{D}$ 中可能有不在 $F$ 的像里的对象，对于这些对象的 hom-集，我们什么也说不了。

::: info 数学小课堂：单射、满射、双射
设函数 $g : A \to B$。

- **单射**：不同的输入一定给出不同的输出。“$g(x) = g(y) \Rightarrow x = y$”。例：`fun n : Nat => 2 * n` 是单射（不会有两个数乘 2 后相等）；`fun n : Nat => n % 2` 不是（0 和 2 都给出 0）。
- **满射**：$B$ 里的每个元素都被某个输入打中。“$\forall b, \exists a, g(a) = b$”。例：`fun n : Nat => n / 2` 是满射；`fun n : Nat => 2 * n` 不是（奇数打不中）。
- **双射**：既单又满，于是可以反过来——存在逆函数。双射就是集合之间的同构，也就是“一一配对”。

“全忠实”就是把这三个词用在**每一个 hom-集**上：对每对对象 $a, b$，函子在 $\mathcal{C}(a, b) \to \mathcal{D}(F a, F b)$ 上是双射。一个全忠实函子像一面完美的镜子：箭头一根不多、一根不少地映过去；只是镜子里的世界（目标范畴）可能比原来的更大。
:::

### 用 Lean 写出米田嵌入，并证明它全忠实

我们把米田嵌入在态射上的作用写出来：`f : b ⟶ a` 被映成自然变换 `yMap f : homFunctor a ⟹ homFunctor b`，分量是“前接 `f`”。

```lean
section embedding
variable {C : Type u} [Category.{u, v} C]

/-- 米田嵌入作用在态射上：f : b ⟶ a  ↦  C(a, -) ⟹ C(b, -)，分量 h ↦ h ∘ f。 -/
def yMap {a b : C} (f : b ⟶ a) : homFunctor a ⟹ homFunctor b where
  app x := fun h => h ⊚ f
  -- 自然性：g ∘ (h ∘ f) = (g ∘ h) ∘ f，就是结合律
  naturality {x y} g := by
    funext (h : a ⟶ x)
    show g ⊚ (h ⊚ f) = (g ⊚ h) ⊚ f
    exact assoc f h g

end embedding
```

先验证它真的是一个（逆变）函子：保持恒等，并且**反转**复合的顺序。

```lean
theorem yMap_id {C : Type u} [Category.{u, v} C] (a : C) :
    yMap (𝟙 a) = NatTrans.ident (homFunctor a) := by
  apply NatTrans.ext'
  intro x
  funext (h : a ⟶ x)
  exact comp_id h               -- h ∘ id = h

/-- 逆变：yMap (f ∘ g) = yMap g ∘ yMap f —— 顺序反了过来。 -/
theorem yMap_comp {C : Type u} [Category.{u, v} C] {a b c : C} (f : b ⟶ a) (g : c ⟶ b) :
    yMap (f ⊚ g) = NatTrans.vcomp (yMap g) (yMap f) := by
  apply NatTrans.ext'
  intro x
  funext (h : a ⟶ x)
  exact assoc g f h             -- h ∘ (f ∘ g) = (h ∘ f) ∘ g
```

再证明它**忠实**（不同的态射给出不同的自然变换）和**全**（每个自然变换都来自某个态射）。两个证明都是米田引理的翻版：在 `𝟙 a` 处求值。

```lean
/-- 忠实：如果 yMap f = yMap g，则 f = g。 -/
theorem yMap_faithful {C : Type u} [Category.{u, v} C] {a b : C} (f g : b ⟶ a)
    (h : yMap f = yMap g) : f = g := by
  -- 两边在 a 处的分量作用到 id_a 上：id_a ∘ f = id_a ∘ g
  have := congrFun (congrArg (fun α => α.app a) h) (𝟙 a)
  simpa [yMap, homFunctor, id_comp] using this

/-- 全：任何自然变换 α : C(a, -) ⟹ C(b, -) 都等于 yMap (α_a id_a)。 -/
theorem yMap_full {C : Type u} [Category.{u, v} C] {a b : C}
    (α : homFunctor a ⟹ homFunctor b) : yMap (α.app a (𝟙 a)) = α := by
  apply NatTrans.ext'
  intro x
  funext (h : a ⟶ x)
  show h ⊚ α.app a (𝟙 a) = α.app x h
  have nat : h ⊚ α.app a (𝟙 a) = α.app x (h ⊚ 𝟙 a) := congrFun (α.naturality h) (𝟙 a)
  rw [nat, comp_id]
```

`simpa [...] using this` 的意思是：用给定的引理同时化简假设 `this` 和目标，然后看两者是否一致。

`yMap_full` 的证明和上一章 `yoneda_from_to` 的证明逐字相同——这当然不是巧合：全忠实性正是米田引理在 $F = \mathcal{C}(b, -)$ 时的特例。

## 嵌入

我们刚才描述的这个（逆变）函子，即把 $\mathcal{C}$ 中的对象映到 $[\mathcal{C}, \mathbf{Set}]$ 中函子的那个函子

$$a \mapsto \mathcal{C}(a, -)$$

定义了**米田嵌入**（Yoneda embedding）。它把范畴 $\mathcal{C}$（严格说来，由于逆变，是范畴 $\mathcal{C}^{op}$）**嵌入**到函子范畴 $[\mathcal{C}, \mathbf{Set}]$ 之中。它不仅把 $\mathcal{C}$ 中的对象映成函子，还忠实地保留了它们之间的一切联系。

这是一个非常有用的结果，因为数学家对函子范畴了解得很多，尤其是值域为 $\mathbf{Set}$ 的那些函子。把任意一个范畴 $\mathcal{C}$ 嵌入函子范畴，我们就能对它获得大量洞见。

::: tip 打个比方：把陌生的东西搬进熟悉的地方
“嵌入”这个词的意思是：$\mathcal{C}$ 原封不动地成为 $[\mathcal{C}, \mathbf{Set}]$ 的一部分——箭头一根不多一根不少（全忠实），只是它现在身处一个更大、更舒适的环境里。在 $[\mathcal{C}, \mathbf{Set}]$ 里，我们有 $\mathbf{Set}$ 的全部工具可用：可以取积、取余积、取极限……这些在原来的 $\mathcal{C}$ 里未必存在。

这就像程序员把一个难以测试的模块“嵌入”到一个功能完备的测试框架里：模块本身的行为一点没变，但现在你可以用框架里的所有工具来观察和操作它。
:::

当然，米田嵌入也有对偶版本，有时叫做余米田嵌入。注意，我们本可以从固定每个 hom-集的**终点**（而不是起点）开始：$\mathcal{C}(-, a)$。这会给出一个逆变的 hom 函子。从 $\mathcal{C}$ 到 $\mathbf{Set}$ 的逆变函子就是我们熟悉的**预层**（presheaf）（参见 [2.2 极限与余极限](/part2/02-limits-and-colimits)）。余米田嵌入定义了范畴 $\mathcal{C}$ 到预层范畴的嵌入。它在态射上的作用是：

$$[\mathcal{C}^{op}, \mathbf{Set}](\mathcal{C}(-, a), \mathcal{C}(-, b)) \cong \mathcal{C}(a, b)$$

注意这一次方向是“正”的：$a \to b$ 对应于 $\mathcal{C}(-, a) \Rightarrow \mathcal{C}(-, b)$，分量是“后接”。同样，数学家对预层范畴也了解得很多，所以能把任意范畴嵌入其中，是一大收获。

## 在 Lean 中的应用

在类型范畴里，米田嵌入可以表示为：一边是 Reader 函子之间的自然变换，另一边是（方向相反的）函数，两者同构：

```lean no-check
({x : Type} → (a → x) → (b → x))  ≅  (b → a)
```

（别忘了，Reader 函子 `Reader a` 就是 `(a → ·)`。）

这个等式的左边是一个多态函数：给它一个从 `a` 到 `x` 的函数，再给它一个 `b` 类型的值，它就能产出一个 `x` 类型的值（这里我把 `b → x` 外面的括号去掉了——也就是“反柯里化”地去理解它：`(a → x) → b → x`）。要想对**所有** `x` 都做到这一点，唯一的办法是：我们的函数知道怎么把 `b` 转换成 `a`。它必须偷偷地掌握着一个函数 `b → a`。

给定这样一个转换器 `btoa`，就可以定义左边——叫它 `fromY`：

```lean no-check
fromY (f : a → x) (v : b) : x := f (btoa v)
```

反过来，给定一个函数 `fromY`，用恒等函数调用它就能取回转换器：

```lean no-check
fromY id : b → a
```

这就在 `fromY` 类型的函数和 `btoa` 类型的函数之间建立了双射。

和上一章一样，在 Lean 中要证明这个双射，必须把自然性写进左边的类型：

```lean
/-- 从 Reader a 到 Reader b 的自然变换。 -/
structure YEmb (a b : Type) where
  app : {x : Type} → (a → x) → (b → x)
  naturality : ∀ {x y : Type} (f : x → y) (h : a → x), f ∘ app h = app (f ∘ h)

/-- 由转换器 btoa 构造自然变换：前接 btoa。 -/
def fromY {a b : Type} (btoa : b → a) : YEmb a b where
  app f := f ∘ btoa
  naturality _ _ := rfl

/-- 用 id 调用，取回转换器。 -/
def toBtoa {a b : Type} (y : YEmb a b) : b → a := y.app id

example : toBtoa (fromY (fun s : String => s.length)) "米田" = 2 := rfl
```

看待这个同构的另一种方式是：它是函数 `b → a` 的一种 **CPS 编码**。参数 `a → x` 是续延（处理器）；结果是一个从 `b` 到 `x` 的函数，用一个 `b` 类型的值调用它时，它会执行“前面接上了被编码函数”的那个续延。

::: tip Rust 视角：给我一个回调，我还你一个回调
在 Rust 里，`fromY` 是一个“回调转换器”：你交给它“拿到 `A` 之后要做什么”，它还给你“拿到 `B` 之后要做什么”。它之所以能做到，是因为它内部藏着一个 `B -> A` 的转换：

```rust
fn from_y<A, B, X>(btoa: impl Fn(B) -> A, k: impl Fn(A) -> X) -> impl Fn(B) -> X {
    move |b| k(btoa(b))
}

pub fn demo() -> usize {
    // 被编码的函数：&str -> usize
    let btoa = |s: &str| s.chars().count();
    // 把“拿到长度后翻倍”的回调，变成“拿到字符串后……”的回调
    let on_str = from_y(btoa, |n: usize| n * 2);
    on_str("米田") // 4
}
```

传入恒等闭包 `|a| a` 作为 `k`，`from_y` 就把藏着的 `btoa` 原样吐了出来——这就是 `fromY id`。
:::

米田嵌入还解释了 Haskell 里数据结构的一些另类表示。特别地，它为 `Control.Lens` 库中的**透镜**（lens）提供了一种[非常有用的表示](https://bartoszmilewski.com/2015/07/13/from-lenses-to-yoneda-embedding/)。（所谓 van Laarhoven 透镜，类型形如“对所有函子 `f`，`(a → f a) → (s → f s)`”——是不是和上面的 `(a → x) → (b → x)` 长得很像？）

## 补充：CPS 与米田——`∀ r, (a → r) → r ≅ a`

上一章我们已经看到，CPS 是米田引理在恒等函子上的特例。这里把它单独拿出来，写成一个独立的 Lean 定理，因为它是米田思想在编程中最常见的化身。

```lean
/-- CPS 值：一个“等着续延 k 的计算”，以及它必须满足的自然性。 -/
structure CPS (a : Type) where
  run : {r : Type} → (a → r) → r
  naturality : ∀ {r s : Type} (f : r → s) (k : a → r), f (run k) = run (f ∘ k)

/-- 直接值 ↦ CPS：把值交给续延。 -/
def CPS.pure {a : Type} (x : a) : CPS a := ⟨fun k => k x, fun _ _ => rfl⟩

/-- CPS ↦ 直接值：用 id 作为续延。 -/
def CPS.extract {a : Type} (c : CPS a) : a := c.run id

theorem CPS.extract_pure {a : Type} (x : a) : (CPS.pure x).extract = x := rfl

theorem CPS.pure_extract {a : Type} (c : CPS a) : CPS.pure c.extract = c := by
  cases c with
  | mk run nat =>
    -- 由自然性：k (run id) = run (k ∘ id) = run k
    have : (fun {r} (k : a → r) => k (run id)) = @run := by
      funext r k
      exact nat k id
    simp only [CPS.pure, CPS.extract]
    congr
```

这里的自然性条件 `f (run k) = run (f ∘ k)` 有一个非常程序员的读法：“**先让 CPS 计算跑完再加工结果**，等于**把加工步骤塞进续延里**”。一个守规矩的 CPS 值不会偷看续延的返回类型 `r`，也不会自己捏造一个 `r` 出来——它只能乖乖地把某个 `a` 交给续延，而且只交一次。这个“某个 `a`”就是 `extract` 取出来的东西。

## 预序的例子

这个例子是 Robert Harper 提出的。它是米田嵌入在由预序定义的范畴上的应用。**预序**是一个集合，带有一个元素之间的序关系，传统上写作 $\leqslant$（小于等于）。“预”字的意思是：我们只要求这个关系满足**传递性**和**自反性**，而不一定满足反对称性（所以允许出现环）。

::: info 数学小课堂：预序
一个关系 $\leqslant$ 是**预序**，如果：

- **自反**：对任何 $a$，$a \leqslant a$；
- **传递**：若 $a \leqslant b$ 且 $b \leqslant c$，则 $a \leqslant c$。

如果再加上**反对称**（$a \leqslant b$ 且 $b \leqslant a$ 推出 $a = b$），就是**偏序**。例子：

- 自然数上的“整除” $a \mid b$：是偏序。$2 \mid 6$，$3 \mid 6$，但 $2$ 和 $3$ 互不整除——不是任何两个元素都能比较。
- “按字符串长度比较”：$s \leqslant t$ 当且仅当 $|s| \leqslant |t|$。这是预序但不是偏序：`"ab"` 和 `"cd"` 互相 $\leqslant$，却不相等——这就是原文说的“环”。
:::

一个带预序关系的集合会生成一个范畴。对象是集合中的元素。从对象 $a$ 到 $b$ 的态射，要么不存在（如果两个对象无法比较，或者 $a \leqslant b$ 不成立）；要么存在（如果 $a \leqslant b$），从 $a$ 指向 $b$。从一个对象到另一个对象的态射永远不会多于一个。因此，这种范畴里的任何 hom-集要么是空集，要么是单元素集。这样的范畴称为**瘦范畴**（thin category）。

很容易确认这个构造确实是一个范畴：箭头可以复合，因为若 $a \leqslant b$ 且 $b \leqslant c$，则 $a \leqslant c$；复合满足结合律（任意两条从 $a$ 到 $d$ 的路径都只能是那唯一的箭头）。恒等箭头也有，因为每个元素都（小于或）等于它自己（底层关系的自反性）。

在 Lean 里写出来：

```lean
class Preord (α : Type) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c

infix:50 " ≼ " => Preord.le

/-- 预序范畴：a ⟶ b 是“a ≼ b 的证明”，被 PLift 包装成一个类型。 -/
abbrev preordCat (α : Type) [Preord α] : Category α where
  Hom a b := PLift (a ≼ b)
  id a := ⟨Preord.refl a⟩
  comp g f := ⟨Preord.trans f.down g.down⟩

/-- 整除是自然数上的预序。 -/
instance : Preord Nat where
  le a b := a ∣ b
  refl a := Nat.dvd_refl a
  trans := Nat.dvd_trans
```

::: tip Lean 深入：为什么用 `PLift`
`a ≼ b` 是一个命题（`Prop`），而 `Category` 要求 hom-集是一个 `Type`。`PLift p` 把一个命题 `p` “抬升”成一个类型：它的值就是 `⟨证明⟩`，用 `.down` 取回证明。由于证明无关性，同一个命题的任意两个证明都相等，所以 `PLift (a ≼ b)` **最多只有一个值**——这正是“瘦范畴”的意思。三条范畴定律也因此自动成立（两边都是“唯一的那个证明”），我们连证明都不用写：`Category` 里定律字段的默认证明 `by intros; rfl` 就够了。
:::

现在我们把**余米田嵌入**应用到预序范畴上。我们关心的是它在态射上的作用：

$$[\mathcal{C}^{op}, \mathbf{Set}](\mathcal{C}(-, a), \mathcal{C}(-, b)) \cong \mathcal{C}(a, b)$$

右边的 hom-集非空，当且仅当 $a \leqslant b$——此时它是单元素集。因此，若 $a \leqslant b$，左边恰有一个自然变换；否则一个也没有。

那么，预序里 hom 函子之间的自然变换长什么样呢？它应该是集合 $\mathcal{C}(-, a)$ 与 $\mathcal{C}(-, b)$ 之间的一族函数。在预序中，这些集合要么为空，要么是单元素集。我们看看手头都有哪些函数可用：

| 从 | 到 | 函数 |
|---|---|---|
| 空集 | 空集 | 有一个：空集上的恒等函数 |
| 空集 | 单元素集 | 有一个：`absurd`（它什么也不用做，因为只需要对空集的元素定义，而空集没有元素） |
| 单元素集 | 单元素集 | 有一个：单元素集上的恒等函数 |
| 单元素集 | 空集 | **没有**！（作用在那唯一的元素上时，函数的值能是什么呢？） |

所以，我们的自然变换永远不会把一个单元素 hom-集连到一个空 hom-集。换句话说，若 $x \leqslant a$（单元素 hom-集 $\mathcal{C}(x, a)$），则 $\mathcal{C}(x, b)$ 不能为空。$\mathcal{C}(x, b)$ 非空意味着 $x$ 小于等于 $b$。因此，所讨论的自然变换存在，要求：对每个 $x$，若 $x \leqslant a$ 则 $x \leqslant b$。

$$\text{对所有 } x,\ x \leqslant a \Rightarrow x \leqslant b$$

另一方面，余米田告诉我们，这个自然变换的存在等价于 $\mathcal{C}(a, b)$ 非空，也就是 $a \leqslant b$。合在一起，我们得到：

$$a \leqslant b \text{ 当且仅当 对所有 } x,\ x \leqslant a \Rightarrow x \leqslant b$$

我们本可以直接得到这个结果。直觉是：若 $a \leqslant b$，则所有在 $a$ 下方的元素也一定在 $b$ 下方。反过来，在右边把 $x$ 换成 $a$，就推出 $a \leqslant b$。但你得承认，经由米田嵌入得出这个结果要刺激得多。

用集合的语言说：记 $\downarrow a = \{x \mid x \leqslant a\}$ 为 $a$ 的**下方集合**（down-set），那么

$$a \leqslant b \iff \ \downarrow a \subseteq \ \downarrow b$$

**一个元素在序中的位置，完全由“谁在它下面”决定。** 在 Lean 中，这个结论（以及它的直接证明）只有几行：

```lean
theorem coYoneda_preorder {α : Type} [Preord α] (a b : α) :
    a ≼ b ↔ ∀ x, x ≼ a → x ≼ b := by
  constructor
  · -- (→) 若 a ≼ b，则 a 下方的东西都在 b 下方：传递性
    intro hab x hxa
    exact Preord.trans hxa hab
  · -- (←) 取 x := a，用自反性
    intro h
    exact h a (Preord.refl a)

-- 以整除为例：2 ∣ 6，所以 2 的因数都是 6 的因数
example : ∀ x : Nat, x ≼ 2 → x ≼ 6 :=
  (coYoneda_preorder 2 6).mp (show 2 ∣ 6 by decide)
```

`constructor` 把“当且仅当”拆成两个方向分别证明；`·` 开始一个子目标的证明。注意证明的“反方向”恰好就是米田的招数：**把 $x$ 取成 $a$ 本身，用自反性（恒等态射）**——和米田引理里“代入 $\mathrm{id}_a$”是同一个动作。

下面的组件把这一切画了出来。选两个数 $a$、$b$，看看自然变换在每个对象 $x$ 上的分量能否存在。切换到“米田”模式，就得到挑战题 4 的答案。

<div class="ctfp-ch-widget"><Ch2_6PreorderYoneda /></div>

## 自然性

米田引理建立了自然变换的集合与 $\mathbf{Set}$ 中一个对象之间的同构。自然变换是函子范畴 $[\mathcal{C}, \mathbf{Set}]$ 中的态射。任意两个函子之间的自然变换的集合，就是那个范畴里的一个 hom-集。米田引理就是这个同构：

$$[\mathcal{C}, \mathbf{Set}](\mathcal{C}(a, -), F) \cong F a$$

事实证明，这个同构对 $F$ 和 $a$ 都是**自然的**。换句话说，它对 $(F, a)$ 是自然的，$(F, a)$ 是从积范畴 $[\mathcal{C}, \mathbf{Set}] \times \mathcal{C}$ 中取出的一对。注意，我们现在把 $F$ 当作函子范畴中的一个**对象**来看待。

我们来想一想这意味着什么。自然同构是两个函子之间的可逆**自然变换**。而确实，我们这个同构的右边是一个函子：一个从 $[\mathcal{C}, \mathbf{Set}] \times \mathcal{C}$ 到 $\mathbf{Set}$ 的函子。它在一对 $(F, a)$ 上的作用是一个集合——把函子 $F$ 在对象 $a$ 处求值的结果。这叫做**求值函子**（evaluation functor）。

左边也是一个函子，它把 $(F, a)$ 映到自然变换的集合 $[\mathcal{C}, \mathbf{Set}](\mathcal{C}(a, -), F)$。

为了说明它们真的是函子，我们还应该定义它们在态射上的作用。可是一对 $(F, a)$ 与 $(G, b)$ 之间的态射是什么呢？是一对态射 $(\Phi, f)$：第一个是函子之间的态射——一个自然变换；第二个是 $\mathcal{C}$ 中的普通态射。

求值函子把这一对 $(\Phi, f)$ 映成两个集合 $F a$ 与 $G b$ 之间的一个函数。我们可以很容易地用 $\Phi$ 在 $a$ 处的分量（它把 $F a$ 映到 $G a$）和被 $G$ 提升的态射 $f$ 来构造这样一个函数：

$$(G f) \circ \Phi_a$$

注意，由于 $\Phi$ 的自然性，它与下面这个是同一个东西：

$$\Phi_b \circ (F f)$$

```diagram
Fa: (0, 0) "F a"
Ga: (2.6, 0) "G a"
Fb: (0, 1.7) "F b"
Gb: (2.6, 1.7) "G b"
pa: Fa -> Ga "\Phi_a"
pb: Fb -> Gb "\Phi_b" side=right
Ff: Fa -> Fb "F f" side=right
Gf: Ga -> Gb "G f"
path "先 Φ_a 再 G f": pa Gf
path "先 F f 再 Φ_b": Ff pb color=green
caption: 求值函子作用在 (Φ, f) 上：两条路径相等，正是 Φ 的自然性方块
```

我不打算证明整个同构的自然性——一旦确定了函子是什么，证明是相当机械的。它源于这样一个事实：我们的同构是由函子和自然变换搭建起来的。它根本没有出错的余地。

::: details 补充：在 Lean 中证明米田同构的自然性
原书说“相当机械”，那正是 Lean 擅长的事。我们要证明：对任意 $(\Phi, f) : (F, a) \to (G, b)$，先在左边沿 $(\Phi, f)$ 走、再用米田同构，等于先用米田同构、再沿求值函子走。

左边函子作用在 $(\Phi, f)$ 上，把自然变换 $\alpha : \mathcal{C}(a, -) \Rightarrow F$ 送到 $\Phi \circ \alpha \circ \mathrm{yMap}\, f$（注意 $\mathrm{yMap}\, f : \mathcal{C}(b, -) \Rightarrow \mathcal{C}(a, -)$，这里又一次用到了米田嵌入）。右边的求值函子把 $q \in F a$ 送到 $G f (\Phi_a\, q)$。

```lean
def yonedaTo {C : Type u} [Category.{u, v} C] (a : C) (F : CFunctor C (Type v))
    (α : homFunctor a ⟹ F) : F.obj a :=
  α.app a (𝟙 a)

/-- 米田同构对 (F, a) 是自然的。 -/
theorem yoneda_natural {C : Type u} [Category.{u, v} C] {F G : CFunctor C (Type v)}
    (Φ : F ⟹ G) {a b : C} (f : a ⟶ b) (α : homFunctor a ⟹ F) :
    yonedaTo b G (NatTrans.vcomp Φ (NatTrans.vcomp α (yMap f)))
      = G.map f (Φ.app a (yonedaTo a F α)) := by
  -- 左边 = Φ_b (α_b (id_b ∘ f))，右边 = G f (Φ_a (α_a id_a))
  show Φ.app b (α.app b (𝟙 b ⊚ f)) = G.map f (Φ.app a (α.app a (𝟙 a)))
  -- Φ 的自然性：G f ∘ Φ_a = Φ_b ∘ F f
  have hΦ : G.map f (Φ.app a (α.app a (𝟙 a))) = Φ.app b (F.map f (α.app a (𝟙 a))) :=
    congrFun (Φ.naturality f) _
  -- α 的自然性：F f (α_a id_a) = α_b (f ∘ id_a)
  have hα : F.map f (α.app a (𝟙 a)) = α.app b (f ⊚ 𝟙 a) := congrFun (α.naturality f) (𝟙 a)
  rw [hΦ, hα, id_comp, comp_id]
```

确实“没有出错的余地”：证明只用到了 $\Phi$ 和 $\alpha$ 各自的自然性，以及两条单位律。
:::

## 补充：米田的直觉总结

学到这里，你也许被各种 $\mathcal{C}(a, -)$、$\mathrm{Nat}$、$\cong$ 绕得有点晕。让我们退后一步，把这三章的核心浓缩成一句可以记住的话：

> **一个对象，由它与所有其他对象的关系完全决定。**

具体地说：

1. **看它往外的箭头**（米田）：对象 $a$ 由函子 $\mathcal{C}(a, -)$——“从 $a$ 出发能到哪里、有几种走法”——决定。
2. **看指向它的箭头**（余米田）：对象 $a$ 也由预层 $\mathcal{C}(-, a)$——“谁能到达 $a$、有几种走法”——决定。
3. **决定到什么程度？** 到同构为止：如果 $\mathcal{C}(a, -)$ 与 $\mathcal{C}(b, -)$ 自然同构，那么 $a$ 与 $b$ 同构。

第 3 条叫做**米田原理**，它是米田嵌入全忠实的直接推论。我们在 Lean 中把它证明出来——给定两个 hom 函子之间互逆的一对自然变换，就能造出 $a$ 与 $b$ 之间互逆的一对态射：

```lean
theorem iso_of_hom_iso {C : Type u} [Category.{u, v} C] {a b : C}
    (α : homFunctor a ⟹ homFunctor b) (β : homFunctor b ⟹ homFunctor a)
    (βα : ∀ x (h : a ⟶ x), β.app x (α.app x h) = h)
    (αβ : ∀ x (k : b ⟶ x), α.app x (β.app x k) = k) :
    ∃ (f : b ⟶ a) (g : a ⟶ b), f ⊚ g = 𝟙 a ∧ g ⊚ f = 𝟙 b := by
  -- 候选者：两个自然变换在恒等态射上的值（米田！）
  refine ⟨α.app a (𝟙 a), β.app b (𝟙 b), ?_, ?_⟩
  · have e1 : β.app a (α.app a (𝟙 a)) = 𝟙 a := βα a (𝟙 a)
    have nat : β.app a (α.app a (𝟙 a)) = α.app a (𝟙 a) ⊚ β.app b (𝟙 b) := by
      have h1 : α.app a (𝟙 a) ⊚ β.app b (𝟙 b) = β.app a (α.app a (𝟙 a) ⊚ 𝟙 b) :=
        congrFun (β.naturality (α.app a (𝟙 a))) (𝟙 b)
      have h2 : β.app a (α.app a (𝟙 a) ⊚ 𝟙 b) = β.app a (α.app a (𝟙 a)) :=
        congrArg (β.app a) (comp_id _)
      exact (h1.trans h2).symm
    rw [← nat, e1]
  · have e2 : α.app b (β.app b (𝟙 b)) = 𝟙 b := αβ b (𝟙 b)
    have nat : α.app b (β.app b (𝟙 b)) = β.app b (𝟙 b) ⊚ α.app a (𝟙 a) := by
      have h1 : β.app b (𝟙 b) ⊚ α.app a (𝟙 a) = α.app b (β.app b (𝟙 b) ⊚ 𝟙 a) :=
        congrFun (α.naturality (β.app b (𝟙 b))) (𝟙 a)
      have h2 : α.app b (β.app b (𝟙 b) ⊚ 𝟙 a) = α.app b (β.app b (𝟙 b)) :=
        congrArg (α.app b) (comp_id _)
      exact (h1.trans h2).symm
    rw [← nat, e2]
```

`refine ⟨x, y, ?_, ?_⟩` 的意思是：“存在性的证据我先给出 `x`、`y`，剩下两个 `?_` 留作新的目标。”

几个让直觉落地的例子：

- **预序**：一个数在“整除”序中的位置，由它的因数集合（$\downarrow a$）完全决定。$4$ 和 $6$ 的因数集合不同，它们就是不同的位置。
- **类型范畴**：类型 `a` 的元素，恰好就是函数 `Unit → a`（$\mathcal{C}(\mathbf{1}, a)$）。但米田告诉我们更多：你甚至不必单看 `Unit`——**所有**类型 `x` 到 `a` 的函数合起来，就把 `a` 刻画得严丝合缝。
- **群（凯莱定理）**：一个群元素由它“如何作用于所有元素”决定（挑战题 3）。
- **CPS**：一个值 `x : a`，等价于“它会怎样回应每一个续延”（`fun k => k x`）。

::: tip Rust 视角：只能通过接口观察的对象
设想一个 Rust 模块，它导出一个不透明类型 `pub struct Handle(/* 私有字段 */)`，外界只能通过公开的函数与它交互。如果两个 `Handle` 在**所有**公开函数下的表现都一样，外界就**无法区分它们**——从外部看，它们就是“同一个”。

范畴论的对象正是这种极致的“不透明类型”：它根本没有内部，只有箭头（接口）。米田引理是这个哲学的定理版本：**接口就是一切**。这也是为什么面向接口编程、依赖注入、mock 测试能够成立——你只关心一个东西“与其他所有东西如何交互”。
:::

## 挑战

1. 在 Lean 中表达余米田嵌入。
2. 证明我们在 `fromY` 和 `btoa` 之间建立的双射是一个同构（两个映射互为逆）。
3. 对一个幺半群算出米田嵌入。幺半群唯一的对象对应于哪个函子？哪些自然变换对应于幺半群的态射？
4. **协变**米田嵌入应用于预序会得到什么？（问题由 Gershom Bazerman 提出。）
5. 米田嵌入可以用来把任意一个函子范畴 $[\mathcal{C}, \mathcal{D}]$ 嵌入函子范畴 $[[\mathcal{C}, \mathcal{D}], \mathbf{Set}]$。弄清楚它在态射（这里就是自然变换）上是怎样运作的。

::: details 参考答案

**1.** 余米田嵌入在类型范畴中是 `({x : Type} → (x → a) → (x → b)) ≅ (a → b)`：逆变 Reader（`(· → a)`）之间的自然变换，与**同方向**的函数 `a → b` 一一对应。自然变换的分量是“后接 `atob`”。

```lean
structure CoYEmb (a b : Type) where
  app : {x : Type} → (x → a) → (x → b)
  naturality : ∀ {x y : Type} (f : y → x) (h : x → a), app h ∘ f = app (h ∘ f)

def coFromY {a b : Type} (atob : a → b) : CoYEmb a b := ⟨fun h => atob ∘ h, fun _ _ => rfl⟩
def coToAtob {a b : Type} (y : CoYEmb a b) : a → b := y.app id

theorem coRound1 {a b : Type} (atob : a → b) : coToAtob (coFromY atob) = atob := rfl

theorem coRound2 {a b : Type} (y : CoYEmb a b) : coFromY (coToAtob y) = y := by
  cases y with
  | mk app nat =>
    -- 自然性：app id ∘ h = app (id ∘ h) = app h
    have : (fun {x} (h : x → a) => app id ∘ h) = @app := by
      funext x h
      exact nat h id
    simp only [coFromY, coToAtob]
    congr
```

**2.** 一个方向按定义成立：`toBtoa (fromY btoa) = id ∘ btoa = btoa`。另一个方向需要自然性：`fromY (toBtoa y)` 的分量是 `f ↦ f ∘ y.app id`，而由 `y` 的自然性，`f ∘ y.app id = y.app (f ∘ id) = y.app f`。

```lean
theorem toBtoa_fromY {a b : Type} (btoa : b → a) : toBtoa (fromY btoa) = btoa := rfl

theorem fromY_toBtoa {a b : Type} (y : YEmb a b) : fromY (toBtoa y) = y := by
  cases y with
  | mk app nat =>
    have : (fun {x} (f : a → x) => f ∘ app id) = @app := by
      funext x f
      exact nat f id
    simp only [fromY, toBtoa]
    congr
```

**3.** 把幺半群 $M$ 看成只有一个对象 $\ast$ 的范畴，态射就是 $M$ 的元素，复合就是乘法。

- 唯一的对象 $\ast$ 对应于 hom 函子 $\mathcal{C}(\ast, -)$。由于只有一个对象，这个函子把 $\ast$ 映到集合 $\mathcal{C}(\ast, \ast) = M$（$M$ 的底层集合），把每个态射 $m$ 映到函数 $\mathcal{C}(\ast, m) = (n \mapsto m \cdot n)$，也就是**左乘** $m$。所以它就是“$M$ 通过左乘作用在自身上”。
- 自然变换 $\alpha : \mathcal{C}(\ast, -) \Rightarrow \mathcal{C}(\ast, -)$ 只有一个分量 $\alpha : M \to M$，自然性条件是 $\alpha(m \cdot n) = m \cdot \alpha(n)$——它与所有左乘交换。由米田，这样的 $\alpha$ 一定是**右乘**某个元素：$\alpha(n) = n \cdot k$，其中 $k = \alpha(1)$。于是幺半群的每个元素 $k$ 对应自然变换 $\rho_k = (n \mapsto n \cdot k)$。
- 逆变性体现为：$\rho_k \circ \rho_m = (n \mapsto n \cdot m \cdot k) = \rho_{m \cdot k}$，顺序反了过来。

这正是**凯莱定理**的幺半群版本：每个幺半群都同构于它自身上的某个函数幺半群（右乘构成的幺半群）。

```lean
class Monoid' (M : Type) where
  mul : M → M → M
  one : M
  one_mul : ∀ m, mul one m = m
  mul_one : ∀ m, mul m one = m
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

/-- 与所有左乘交换的函数，必然是右乘 α(1)。 -/
theorem cayley {M : Type} [Monoid' M] (α : M → M)
    (nat : ∀ m n, α (Monoid'.mul m n) = Monoid'.mul m (α n)) :
    α = fun n => Monoid'.mul n (α Monoid'.one) := by
  funext n
  rw [← nat, Monoid'.mul_one]   -- n · α(1) = α(n · 1) = α(n)
```

**4.** 协变米田嵌入在态射上的作用是 $[\mathcal{C}, \mathbf{Set}](\mathcal{C}(a, -), \mathcal{C}(b, -)) \cong \mathcal{C}(b, a)$。在预序中，同样的推理（单元素集不能映到空集）给出：自然变换存在当且仅当“对所有 $x$，$a \leqslant x \Rightarrow b \leqslant x$”；而右边非空当且仅当 $b \leqslant a$。所以

$$b \leqslant a \iff \text{对所有 } x,\ a \leqslant x \Rightarrow b \leqslant x \iff \ \uparrow a \subseteq \ \uparrow b$$

即：**一个元素越小，它上方的元素就越多**。（交换 $a$、$b$ 的名字，就是 $a \leqslant b \iff \ \uparrow b \subseteq \ \uparrow a$。）

```lean
theorem yoneda_preorder {α : Type} [Preord α] (a b : α) :
    a ≼ b ↔ ∀ x, b ≼ x → a ≼ x := by
  constructor
  · intro hab x hbx
    exact Preord.trans hab hbx
  · intro h
    exact h b (Preord.refl b)
```

我们甚至可以直接使用正文里的 `homFunctor` 和 `yMap`：在预序范畴中，一个自然变换 `homFunctor a ⟹ homFunctor b` 就是 `b ≼ a` 的证据，反之亦然。

```lean
section preorderNat
attribute [local instance] preordCat

/-- 自然变换 ⇒ b ≼ a：在 id_a 处求值（米田！）。 -/
example {α : Type} [Preord α] (a b : α) (η : homFunctor a ⟹ homFunctor b) : b ≼ a :=
  (η.app a (𝟙 a)).down

/-- b ≼ a ⇒ 自然变换：就是米田嵌入 yMap。 -/
def natOfLe {α : Type} [Preord α] {a b : α} (h : b ≼ a) : homFunctor a ⟹ homFunctor b :=
  yMap (C := α) ⟨h⟩

end preorderNat
```

`attribute [local instance] preordCat` 让 `preordCat` 只在这个 `section` 里充当类型类实例。

**5.** 设 $\mathcal{E} = [\mathcal{C}, \mathcal{D}]$。对 $\mathcal{E}$ 应用米田嵌入：

- 对象：函子 $F \in \mathcal{E}$ 被映到 hom 函子 $\mathcal{E}(F, -) = \mathrm{Nat}(F, -) : \mathcal{E} \to \mathbf{Set}$。它把函子 $H$ 映到集合 $\mathrm{Nat}(F, H)$。
- 态射：$\mathcal{E}$ 中的态射是自然变换 $\theta : G \Rightarrow F$。米田嵌入（逆变！）把它映到一个从 $\mathrm{Nat}(F, -)$ 到 $\mathrm{Nat}(G, -)$ 的自然变换，其在 $H$ 处的分量是**前接 $\theta$**：

  $$\mathrm{Nat}(F, H) \to \mathrm{Nat}(G, H), \qquad \sigma \mapsto \sigma \circ \theta$$

  （这里 $\circ$ 是自然变换的垂直复合。）
- 这一族分量本身的自然性（对 $\tau : H \Rightarrow K$）是 $\tau \circ (\sigma \circ \theta) = (\tau \circ \sigma) \circ \theta$，也就是垂直复合的结合律。
- 由米田引理，它全忠实：$\mathrm{Nat}(\mathrm{Nat}(F, -), \mathrm{Nat}(G, -)) \cong \mathrm{Nat}(G, F)$。

所需的结合律在 Lean 中这样证：

```lean
theorem NatTrans.vcomp_assoc {C : Type u₁} [Category.{u₁, v₁} C] {D : Type u₂}
    [Category.{u₂, v₂} D] {F G H K : CFunctor C D} (γ : H ⟹ K) (β : G ⟹ H) (α : F ⟹ G) :
    NatTrans.vcomp γ (NatTrans.vcomp β α) = NatTrans.vcomp (NatTrans.vcomp γ β) α := by
  apply NatTrans.ext'
  intro x
  exact assoc (α.app x) (β.app x) (γ.app x)
```
:::

## 本章小结

- **米田嵌入**：$a \mapsto \mathcal{C}(a, -)$，把 $\mathcal{C}$ 的对象映成函子范畴 $[\mathcal{C}, \mathbf{Set}]$ 中的对象。它是一个**逆变**函子：$f : b \to a$ 被映成自然变换 $\mathcal{C}(a, -) \Rightarrow \mathcal{C}(b, -)$，分量是“前接 $f$”。
- 它由米田引理直接得到：取 $F = \mathcal{C}(b, -)$，得 $\mathrm{Nat}(\mathcal{C}(a, -), \mathcal{C}(b, -)) \cong \mathcal{C}(b, a)$。
- **忠实** = hom-集上单射；**全** = hom-集上满射；**全忠实** = hom-集上双射（但对象上不一定）。米田嵌入是全忠实的——我们在 Lean 中证明了 `yMap_id`、`yMap_comp`（逆变）、`yMap_faithful`、`yMap_full`。
- **余米田嵌入**：$a \mapsto \mathcal{C}(-, a)$，把 $\mathcal{C}$ 嵌入预层范畴 $[\mathcal{C}^{op}, \mathbf{Set}]$，方向不反转。
- 在类型范畴中：`({x} → (a → x) → (b → x)) ≅ (b → a)`，左边是函数 `b → a` 的 CPS 编码；`∀ r, (a → r) → r ≅ a` 是 CPS 的核心。Rust 的回调风格就是它。
- **预序**：$a \leqslant b \iff \forall x,\ x \leqslant a \Rightarrow x \leqslant b$，即 $\downarrow a \subseteq \downarrow b$；协变版本给出 $\uparrow b \subseteq \uparrow a$。
- 米田同构对 $(F, a)$ 是自然的；右边是求值函子。我们在 Lean 中补上了原书略去的证明。
- **米田原理**：$\mathcal{C}(a, -) \cong \mathcal{C}(b, -)$ 推出 $a \cong b$。
- 一句话记住米田：**一个对象，由它与所有其他对象的关系完全决定。**
