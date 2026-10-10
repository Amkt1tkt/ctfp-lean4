# 3.9 单子的代数

如果我们把自函子解释为定义表达式的方式，那么代数让我们对表达式求值，而单子让我们构造和操作表达式。
把代数和单子结合起来，我们不仅能获得大量功能，还能回答几个有趣的问题。

其中一个问题涉及单子与伴随之间的关系。我们已经看到，每个伴随都[定义了一个单子](/part3/06-monads-categorically)（以及一个余单子）。
问题是：是否每个单子（余单子）都可以从某个伴随导出？答案是肯定的。有一整族伴随都生成同一个给定的单子。我会给你展示其中的两个。

![抱着代数的小猪](/img/3.9/pigalg.png "一只抱着 ALG 盒子的小猪。")

```lean hidden
universe u

/-- Lean 核心库不再为 List 提供 Monad 实例；本章自己给出（pure 是单元素列表，bind 是 flatMap）。 -/
instance listMonad : Monad List where
  pure x := [x]
  bind xs f := xs.flatMap f
  map := List.map

instance : LawfulMonad List := LawfulMonad.mk' List
  (id_map := fun xs => List.map_id xs)
  (pure_bind := fun x f => by show List.flatMap f [x] = f x; simp)
  (bind_assoc := fun xs f g => by
    show List.flatMap g (List.flatMap f xs) = List.flatMap (fun x => List.flatMap g (f x)) xs
    exact List.flatMap_assoc)
  (map_const := fun _ _ => rfl)
  (bind_pure_comp := fun f xs => by
    show List.flatMap (fun y => [f y]) xs = List.map f xs
    exact List.map_eq_flatMap.symm)
```

我们来回顾一下定义。单子是一个自函子 $m$，配备两个满足某些相干条件的自然变换。这两个变换在 $a$ 处的分量是：

$$\eta_a : a \to m\ a \qquad \mu_a : m\ (m\ a) \to m\ a$$

同一个自函子的代数，是选定一个特定的对象——载体 $a$——连同一个态射：

$$\mathit{alg} : m\ a \to a$$

首先要注意的是，代数的方向与 $\eta_a$ 相反。直觉是，$\eta_a$ 从一个类型为 $a$ 的值创建一个平凡的表达式。
使代数与单子相容的第一个相干条件保证：用载体为 $a$ 的代数对这个表达式求值，会得回原来的值：

$$\mathit{alg} \circ \eta_a = \mathrm{id}_a$$

第二个条件源于这样一个事实：对于双重嵌套的表达式 $m\ (m\ a)$，有两种求值的方式。我们可以先应用 $\mu_a$ 把表达式压平，然后使用代数的求值器；
也可以先应用提升后的求值器对内层表达式求值，再对结果应用求值器。我们希望这两种策略是等价的：

$$\mathit{alg} \circ \mu_a = \mathit{alg} \circ m\ \mathit{alg}$$

这里，$m\ \mathit{alg}$ 是用函子 $m$ 提升 $\mathit{alg}$ 所得到的态射。下面的交换图描述了这两个条件（我把 $m$ 换成了 $T$，为接下来的内容做准备）：

```diagram
a: (0, 0) "a"
Ta: (2, 0) "T\,a"
a2: (2, 1.5) "a"
eta: a -> Ta "\eta_a"
alg: Ta -> a2 "\mathit{alg}"
id: a -> a2 "\mathrm{id}_a" side=right
path "η 再 alg": eta alg
path "什么都不做": id color=green
caption: 单位律：$\mathit{alg} \circ \eta_a = \mathrm{id}_a$。
```

```diagram
TTa: (0, 0) "T(T\,a)"
Ta1: (2, 0) "T\,a"
Ta2: (0, 1.5) "T\,a"
a: (2, 1.5) "a"
Talg: TTa -> Ta1 "T\,\mathit{alg}"
mu: TTa -> Ta2 "\mu_a" side=right
alg1: Ta1 -> a "\mathit{alg}"
alg2: Ta2 -> a "\mathit{alg}" side=right
path "先算内层": Talg alg1
path "先压平": mu alg2 color=green
caption: 乘法律：$\mathit{alg} \circ \mu_a = \mathit{alg} \circ T\,\mathit{alg}$。
```

我们也可以用 Lean 来表达这些条件：

```lean
/-- 单子的 join（即 μ）。 -/
def join {m : Type → Type} [Monad m] {a : Type} (mma : m (m a)) : m a := mma >>= id

/-- 单子代数：求值映射，外加与 pure、join 相容的证明。 -/
structure MonadAlgebra (m : Type → Type) [Monad m] (a : Type) where
  alg : m a → a
  unit_law : ∀ x : a, alg (pure x) = x
  mult_law : ∀ mma : m (m a), alg (join mma) = alg (Functor.map alg mma)
```

::: tip Lean 深入：把定律放进结构体
与上一章的 `AlgHom` 一样，`MonadAlgebra` 的后两个字段是**命题**，它们的值是**证明**。
构造一个 `MonadAlgebra` 时，你必须同时交出求值函数和两条定律的证明，否则编译不过。
Rust 的 trait 只能在文档里写“实现者应当保证……”；Lean 的类型可以真的强制这一点。
:::

我们来看一个小例子。列表自函子的一个代数由某个类型 `a` 和一个从 `a` 的列表产生一个 `a` 的函数组成。
假设我们可以用 `foldr` 来表达这个函数，并把元素类型和累加器类型都选为 `a`：

```lean no-check
List.foldr : (a → a → a) → a → List a → a
```

这个特定的代数由一个二元函数（我们叫它 `f`）和一个值 `z` 指定。列表函子恰好也是一个单子，其中 `pure`（Haskell 的 `return`）把一个值变成单元素列表。
代数（这里是 `foldr f z`）复合在 `pure` 之后，把 `x` 变成：

```lean no-check
List.foldr f z [x] = f x z
```

如果对每个 `x` 都满足下面这个相干条件，代数就与单子相容：

```lean no-check
f x z = x
```

如果把 `f` 看作一个二元运算符，这个条件告诉我们 `z` 是右单位元。

第二个相干条件作用在列表的列表上。`join` 的作用是把各个列表拼接起来。然后我们可以折叠得到的列表。
另一方面，我们也可以先折叠各个列表，再折叠得到的结果列表。同样，如果把 `f` 解释为一个二元运算符，这个条件告诉我们这个二元运算满足结合律。
当 `(a, f, z)` 是一个幺半群时，这些条件当然都满足。

在下面的组件里试试几个运算，包括不满足结合律的减法：

<div class="ch-widget-wrap">
<Ch3_9ListAlgebra />
</div>

### 补充：在 Lean 中证明“List 的代数 = 幺半群”

::: warning 易错点：Lean 核心库里的 List 不是 Monad 实例
Lean 4 核心库有意没有给 `List` 提供 `Monad` 实例（列表单子的“非确定性”语义很容易被误用，比如意外地产生指数级的搜索）。
本章在一个隐藏代码块里自己补上了：`pure x = [x]`，`xs >>= f = xs.flatMap f`，并证明了 `LawfulMonad`。
:::

先准备几个小引理，把本章列表单子的 `pure`、`map`、`join` 翻译成熟悉的列表操作：

```lean
theorem list_join_eq {a : Type} (xss : List (List a)) : join xss = xss.flatten :=
  List.flatMap_id

theorem list_map_eq {a b : Type} (f : a → b) (xs : List a) : Functor.map f xs = xs.map f := rfl
theorem list_pure_eq {a : Type} (x : a) : (pure x : List a) = [x] := rfl
```

幺半群给出 `List` 单子的代数：

```lean
namespace MyMonoid
class Monoid (a : Type) where
  op : a → a → a
  e : a
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  e_op : ∀ x, op e x = x
  op_e : ∀ x, op x e = x
end MyMonoid
open MyMonoid

/-- 折叠一个拼接 = 分别折叠再相乘。需要结合律与左单位律。 -/
theorem foldr_append {a : Type} [Monoid a] (xs ys : List a) :
    (xs ++ ys).foldr Monoid.op Monoid.e
      = Monoid.op (xs.foldr Monoid.op Monoid.e) (ys.foldr Monoid.op Monoid.e) := by
  induction xs with
  | nil => simp [Monoid.e_op]
  | cons x xs ih => simp [ih, Monoid.assoc]

/-- 幺半群 ⇒ List 单子的代数。 -/
def monoidAlgebra (a : Type) [Monoid a] : MonadAlgebra List a where
  alg := List.foldr Monoid.op Monoid.e
  unit_law x := by
    rw [list_pure_eq]
    exact Monoid.op_e x            -- foldr op e [x] = op x e = x
  mult_law xss := by
    rw [list_join_eq, list_map_eq]
    induction xss with
    | nil => rfl
    | cons xs xss ih =>
      rw [List.flatten_cons, foldr_append, ih]
      rfl

instance : Monoid Nat where
  op := (· + ·)
  e := 0
  assoc := Nat.add_assoc
  e_op := Nat.zero_add
  op_e := Nat.add_zero

example : (monoidAlgebra Nat).alg [1, 2, 3, 4] = 10 := rfl
```

反方向同样成立，而且更有意思：**任何** `List` 单子的代数（不一定写成 `foldr`）都给出一个幺半群。
取 `op x y := alg [x, y]`、`e := alg []`，用两条代数定律分别推出结合律和单位律：

```lean
/-- List 单子的代数 ⇒ 幺半群。 -/
@[reducible] def algebraMonoid {a : Type} (A : MonadAlgebra List a) : Monoid a where
  op x y := A.alg [x, y]
  e := A.alg []
  assoc x y z := by
    have ux : A.alg [x] = x := A.unit_law x
    have uz : A.alg [z] = z := A.unit_law z
    -- 乘法律用在 [[x, y], [z]] 和 [[x], [y, z]] 上：两者都等于 alg [x, y, z]
    have h1 := A.mult_law [[x, y], [z]]
    have h2 := A.mult_law [[x], [y, z]]
    rw [list_join_eq, list_map_eq] at h1 h2
    simp only [List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_nil, ux, uz] at h1 h2
    rw [← h1, h2]
  e_op x := by
    have ux : A.alg [x] = x := A.unit_law x
    -- 乘法律用在 [[], [x]] 上
    have h := A.mult_law [[], [x]]
    rw [list_join_eq, list_map_eq] at h
    simp only [List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, ux] at h
    exact h.symm
  op_e x := by
    have ux : A.alg [x] = x := A.unit_law x
    -- 乘法律用在 [[x], []] 上
    have h := A.mult_law [[x], []]
    rw [list_join_eq, list_map_eq] at h
    simp only [List.flatten_cons, List.flatten_nil, List.map_cons, List.map_nil,
      List.append_nil, ux] at h
    exact h.symm
```

::: info 数学小课堂：为什么列表单子的代数“就是”幺半群
`List a` 是 `a` 上的[自由幺半群](/part2/03-free-monoids)：它只记下“哪些元素按什么顺序相乘”，并不真的去乘。
一个 `List` 代数 `List a → a` 就是“把这串形式乘积真的算出来”的办法。两条定律保证了算法与“怎么加括号”无关（结合律），
以及空乘积表现得像单位元（单位律）。所以“列表单子的代数”和“幺半群”是同一回事的两种说法。
其他单子也是如此：**单子描述一种代数结构的“自由版本”，它的代数就是这种结构的真实实例。**
:::

## T-代数

由于数学家喜欢把他们的单子叫作 $T$，他们就把与之相容的代数叫作 **$T$-代数**。给定范畴 $\mathcal{C}$ 中的单子 $T$，其 $T$-代数构成一个范畴，
叫作 **Eilenberg–Moore 范畴**，通常记作 $\mathcal{C}^T$。这个范畴中的态射是代数同态。它们就是我们为 F-代数定义过的那种同态。

```lean
section EM
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Eilenberg–Moore 范畴的对象：载体 + 单子代数。 -/
structure TAlg (m : Type → Type) [Monad m] where
  carrier : Type
  str : MonadAlgebra m carrier

/-- Eilenberg–Moore 范畴的态射：与求值交换的映射。 -/
structure THom (A B : TAlg m) where
  map : A.carrier → B.carrier
  comm : ∀ x, map (A.str.alg x) = B.str.alg (Functor.map map x)
```

一个 $T$-代数是一个由载体对象和求值器组成的对 $(a, f)$。从 $\mathcal{C}^T$ 到 $\mathcal{C}$ 有一个显然的遗忘函子 $U^T$，它把 $(a, f)$ 映到 $a$。
它还把 $T$-代数之间的同态映到 $\mathcal{C}$ 中载体对象之间相应的态射。你也许还记得，在讨论[伴随](/part3/03-free-forgetful-adjunctions)时我们说过，
遗忘函子的左伴随叫作自由函子。

$U^T$ 的左伴随叫作 $F^T$。它把 $\mathcal{C}$ 中的对象 $a$ 映到 $\mathcal{C}^T$ 中的一个自由代数。这个自由代数的载体是 $T\,a$。
它的求值器是一个从 $T(T\,a)$ 回到 $T\,a$ 的态射。既然 $T$ 是一个单子，我们就可以用单子的 $\mu_a$（Haskell 中的 `join`）作为求值器。

我们还得证明这是一个 $T$-代数。为此，必须满足两个相干条件：

$$\mathit{alg} \circ \eta_{Ta} = \mathrm{id}_{Ta} \qquad \mathit{alg} \circ \mu_a = \mathit{alg} \circ T\,\mathit{alg}$$

但只要把 $\mu$ 代入作为代数，这两个条件就正是单子定律。

```lean
theorem join_pure {a : Type} (x : m a) : join (pure x) = x := by
  simp only [join, pure_bind, id]

theorem join_map_join {a : Type} (x : m (m (m a))) :
    join (join x) = join (Functor.map join x) := by
  simp only [join, map_eq_pure_bind, bind_assoc, pure_bind, id]

/-- 自由代数 (T a, μ_a)。 -/
def freeAlgebra (a : Type) : MonadAlgebra m (m a) where
  alg := join
  unit_law := join_pure
  mult_law := join_map_join

def FreeT (a : Type) : TAlg m := ⟨m a, freeAlgebra a⟩
```

::: tip Lean 深入：`simp only [...]`
`simp only [引理列表]` 只用列出的引理改写目标，比裸 `simp` 更可控。这里的 `map_eq_pure_bind` 把 `f <$> x` 改写成 `x >>= pure ∘ f`，
`bind_assoc`、`pure_bind` 是单子定律，`id` 展开恒等函数。不加 `only` 的话，`simp` 会把 `map_eq_pure_bind` 和它的反方向 `bind_pure_comp`
一起用，在两者之间来回改写，最后报“最大递归深度”错误。
:::

你也许还记得，每个伴随都定义一个单子。事实证明，$F^T$ 与 $U^T$ 之间的伴随所定义的，恰恰就是构造 Eilenberg–Moore 范畴时所用的那个单子 $T$。
既然我们可以对每个单子做这个构造，就可以得出结论：每个单子都可以由一个伴随生成。稍后我会向你展示另一个生成同一单子的伴随。

计划是这样的：首先，我会向你展示 $F^T$ 确实是 $U^T$ 的左伴随。我会通过定义这个伴随的单位和余单位，并证明相应的三角恒等式成立来做到这一点。
然后，我会向你展示这个伴随所生成的单子确实就是我们原来的单子。

伴随的单位是自然变换：

$$\eta : I \to U^T \circ F^T$$

我们来计算这个变换的 $a$ 分量。恒等函子给我们 $a$。自由函子产生自由代数 $(T\,a, \mu_a)$，遗忘函子把它约化为 $T\,a$。
总的来说，我们得到了一个从 $a$ 到 $T\,a$ 的映射。我们直接用单子 $T$ 的单位作为这个伴随的单位。

我们来看余单位：

$$\varepsilon : F^T \circ U^T \to I$$

我们来计算它在某个 $T$-代数 $(a, f)$ 处的分量。遗忘函子忘掉 $f$，自由函子产生对 $(T\,a, \mu_a)$。所以，为了定义余单位 $\varepsilon$ 在 $(a, f)$ 处的分量，
我们需要 Eilenberg–Moore 范畴中合适的态射，也就是 $T$-代数的一个同态：

$$(T\,a, \mu_a) \to (a, f)$$

这样一个同态应该把载体 $T\,a$ 映到 $a$。我们只要让被遗忘的求值器 $f$ 复活就行了。这一次，我们把它当作 $T$-代数的同态来使用。
确实，使 $f$ 成为 $T$-代数的那个交换图，可以重新解读为说明它是 $T$-代数的同态：

```diagram
TTa: (0, 0) "T(T\,a)"
Ta1: (2, 0) "T\,a"
Ta2: (0, 1.5) "T\,a"
a: (2, 1.5) "a"
Tf: TTa -> Ta1 "T\,f"
mu: TTa -> Ta2 "\mu_a" side=right
f1: Ta1 -> a "f"
f2: Ta2 -> a "f" side=right
path "T f 再 f": Tf f1
path "μ 再 f": mu f2 color=green
caption: 同一个方块：既是 $(a, f)$ 的乘法律，也说明 $f$ 是从 $(T\,a, \mu_a)$ 到 $(a, f)$ 的同态。
```

这样，我们就把余单位自然变换 $\varepsilon$ 在 $(a, f)$（$T$-代数范畴中的一个对象）处的分量定义为 $f$。

```lean
/-- 余单位在 (a, f) 处的分量：f 本身就是从自由代数到 (a, f) 的同态。 -/
def counit (A : TAlg m) : THom (FreeT (m := m) A.carrier) A where
  map := A.str.alg
  comm x := A.str.mult_law x
```

为了完成这个伴随，我们还需要证明单位和余单位满足三角恒等式。它们是：

```diagram
Ta: (0, 0) "T\,a"
TTa: (2, 0) "T(T\,a)"
Ta2: (2, 1.5) "T\,a"
Teta: Ta -> TTa "T\,\eta_a"
mu: TTa -> Ta2 "\mu_a"
id: Ta -> Ta2 "\mathrm{id}" side=right
path "T η 再 μ": Teta mu
path "恒等": id color=green
caption: 第一个三角恒等式：$\mu_a \circ T\,\eta_a = \mathrm{id}_{Ta}$。
```

```diagram
a: (0, 0) "a"
Ta: (2, 0) "T\,a"
a2: (2, 1.5) "a"
eta: a -> Ta "\eta_a"
f: Ta -> a2 "f"
id: a -> a2 "\mathrm{id}" side=right
path "η 再 f": eta f
path "恒等": id color=green
caption: 第二个三角恒等式：$f \circ \eta_a = \mathrm{id}_a$。
```

第一个成立是因为单子 $T$ 的单位律。第二个就是 $T$-代数 $(a, f)$ 的定律。

我们已经确立了这两个函子构成一个伴随：

$$F^T \dashv U^T$$

::: details 补充：在 Lean 中验证 hom-集的一一对应 $\mathcal{C}^T(F^T a, B) \cong \mathcal{C}(a, U^T B)$
伴随也可以用 hom-集的一一对应来刻画。左边是从自由代数 $(T\,a, \mu_a)$ 到 $B = (b, f)$ 的同态，右边是普通函数 $a \to b$：

- 从右往左：给定 $g : a \to b$，先用 $T\,g$ 把 $T\,a$ 映到 $T\,b$，再用 $f$ 求值：$f \circ T\,g$。
- 从左往右：给定同态 $\varphi : T\,a \to b$，限制到“平凡表达式”上：$\varphi \circ \eta_a$。

这就是“自由”的含义：从自由代数出发的同态，完全由它在**生成元**上的取值决定。

```lean
theorem join_map_pure {a : Type} (x : m a) : join (Functor.map pure x) = x := by
  simp only [join, map_eq_pure_bind, bind_assoc, pure_bind, id, bind_pure]

/-- μ 的自然性：T f ∘ μ = μ ∘ T (T f)。 -/
theorem join_natural {a b : Type} (f : a → b) (x : m (m a)) :
    Functor.map f (join x) = join (Functor.map (Functor.map f) x) := by
  simp only [join, map_eq_pure_bind, bind_assoc, pure_bind, id]

theorem alg_map_join {a b : Type} (g : a → b) (alg : m b → b)
    (hmult : ∀ mmb : m (m b), alg (join mmb) = alg (Functor.map alg mmb)) (x : m (m a)) :
    alg (Functor.map g (join x)) = alg (Functor.map (alg ∘ Functor.map g) x) := by
  rw [join_natural, hmult, comp_map]

/-- 从右往左：函数 g ↦ 同态 f ∘ T g。 -/
def toHom {a : Type} {B : TAlg m} (g : a → B.carrier) : THom (FreeT (m := m) a) B where
  map := B.str.alg ∘ Functor.map g
  comm x := alg_map_join g B.str.alg B.str.mult_law x

/-- 从左往右：同态 φ ↦ φ ∘ η。 -/
def fromHom {a : Type} {B : TAlg m} (φ : THom (FreeT (m := m) a) B) : a → B.carrier :=
  φ.map ∘ pure

/-- 往返一：先 toHom 再 fromHom 回到原函数（用到代数的单位律）。 -/
theorem from_to {a : Type} {B : TAlg m} (g : a → B.carrier) :
    fromHom (toHom (m := m) (B := B) g) = g := by
  funext x
  show B.str.alg (Functor.map g (pure x)) = g x
  rw [map_pure, B.str.unit_law]

theorem to_from_aux {a b : Type} (alg : m b → b) (φ : m a → b)
    (hφ : ∀ x : m (m a), φ (join x) = alg (Functor.map φ x)) (x : m a) :
    alg (Functor.map (φ ∘ pure) x) = φ x := by
  rw [comp_map, ← hφ]
  exact congrArg φ (join_map_pure x)

/-- 往返二：先 fromHom 再 toHom 回到原同态（用到同态条件与单子的右单位律）。 -/
theorem to_from {a : Type} {B : TAlg m} (φ : THom (FreeT (m := m) a) B) :
    (toHom (fromHom φ)).map = φ.map := by
  funext x
  exact to_from_aux B.str.alg φ.map φ.comm x
```

两个往返都是恒等，所以这确实是一一对应。（严格地说，伴随还要求这个对应关于 $a$ 和 $B$ 自然；那是两次直接的展开，这里从略。）
:::

每个伴随都会产生一个单子。往返

$$U^T \circ F^T$$

是 $\mathcal{C}$ 中产生相应单子的那个自函子。我们来看看它对对象 $a$ 的作用。$F^T$ 创建的自由代数是 $(T\,a, \mu_a)$。遗忘函子 $U^T$ 丢掉求值器。
所以，确实有：

$$U^T \circ F^T = T$$

正如预期的那样，这个伴随的单位就是单子 $T$ 的单位。

你也许还记得，伴随的余单位通过下面的公式产生单子的乘法：

$$\mu = R \circ \varepsilon \circ L$$

这是三个自然变换的水平复合，其中两个是恒等自然变换，分别把 $L$ 映到 $L$、把 $R$ 映到 $R$。中间那个——余单位——是一个在代数 $(a, f)$ 处分量为 $f$ 的自然变换。

我们来计算分量 $\mu_a$。我们先把 $\varepsilon$ 水平复合在 $F^T$ 之后，结果是 $\varepsilon$ 在 $F^T a$ 处的分量。由于 $F^T$ 把 $a$ 带到代数 $(T\,a, \mu_a)$，
而 $\varepsilon$ 挑出求值器，我们最终得到的就是 $\mu_a$。在左边与 $U^T$ 做水平复合不会改变任何东西，因为 $U^T$ 对态射的作用是平凡的。
所以，从这个伴随得到的 $\mu$ 确实与原来那个单子 $T$ 的 $\mu$ 相同。

## Kleisli 范畴

我们之前见过 [Kleisli 范畴](/part1/04-kleisli-categories)。它是由另一个范畴 $\mathcal{C}$ 和一个单子 $T$ 构造出来的范畴。我们把这个范畴叫作 $\mathcal{C}_T$。
Kleisli 范畴 $\mathcal{C}_T$ 中的对象就是 $\mathcal{C}$ 的对象，但态射不同。Kleisli 范畴中从 $a$ 到 $b$ 的态射 $f_{\mathcal{K}}$，对应于原范畴中一个从 $a$ 到 $T\,b$ 的态射 $f$。
我们把这个态射称为从 $a$ 到 $b$ 的 **Kleisli 箭头**。

Kleisli 范畴中态射的复合，是用 Kleisli 箭头的单子式复合来定义的。例如，我们来把 $g_{\mathcal{K}}$ 复合在 $f_{\mathcal{K}}$ 之后。在 Kleisli 范畴中我们有：

$$f_{\mathcal{K}} : a \to b \qquad g_{\mathcal{K}} : b \to c$$

在范畴 $\mathcal{C}$ 中，它们对应于：

$$f : a \to T\,b \qquad g : b \to T\,c$$

我们把复合

$$h_{\mathcal{K}} = g_{\mathcal{K}} \circ f_{\mathcal{K}}$$

定义为 $\mathcal{C}$ 中的一个 Kleisli 箭头：

$$h : a \to T\,c \qquad h = \mu \circ (T\,g) \circ f$$

在 Lean 中我们这样写：

```lean
def kcomp {m : Type → Type} [Monad m] {a b c : Type} (g : b → m c) (f : a → m b) : a → m c :=
  join ∘ Functor.map g ∘ f
```

存在一个从 $\mathcal{C}$ 到 $\mathcal{C}_T$ 的函子 $F$，它在对象上的作用是平凡的。在态射上，它把 $\mathcal{C}$ 中的 $f$ 映到 $\mathcal{C}_T$ 中的一个态射：
创建一个 Kleisli 箭头，修饰 $f$ 的返回值。给定一个态射：

$$f : a \to b$$

它创建 $\mathcal{C}_T$ 中的一个态射，对应的 Kleisli 箭头是：

$$\eta \circ f$$

在 Lean 中我们这样写：

```lean
def kF {m : Type → Type} [Monad m] {a b : Type} (f : a → b) : a → m b := pure ∘ f
```

我们还可以定义一个从 $\mathcal{C}_T$ 回到 $\mathcal{C}$ 的函子 $G$。它取 Kleisli 范畴中的对象 $a$，把它映到 $\mathcal{C}$ 中的对象 $T\,a$。
它对一个态射 $f_{\mathcal{K}}$（对应于 Kleisli 箭头 $f : a \to T\,b$）的作用，是 $\mathcal{C}$ 中的一个态射：

$$T\,a \to T\,b$$

它由先提升 $f$、再应用 $\mu$ 给出：

$$\mu_b \circ T\,f$$

用 Lean 的记法来写就是：

```lean
def kG {m : Type → Type} [Monad m] {a b : Type} (f : a → m b) : m a → m b := join ∘ Functor.map f
```

你也许认出来了，这正是用 `join` 来定义的单子 bind。

很容易看出，这两个函子构成一个伴随：

$$F \dashv G$$

而它们的复合 $G \circ F$ 重新产生了原来的单子 $T$。

::: details 补充：用 Lean 验证 $G$ 保持复合、$G \circ F$ 就是 $T$
```lean
/-- G 保持复合：G (g ∘ₖ f) = G g ∘ G f（本质上是单子的结合律）。 -/
theorem kG_comp {m : Type → Type} [Monad m] [LawfulMonad m] {a b c : Type}
    (g : b → m c) (f : a → m b) : kG (kcomp g f) = kG g ∘ kG f := by
  funext x
  simp only [kG, kcomp, Function.comp, join, map_eq_pure_bind, bind_assoc, pure_bind, id]

/-- G ∘ F 在态射上就是 T 的 fmap：这个伴随同样产生单子 T。 -/
theorem kG_kF {m : Type → Type} [Monad m] [LawfulMonad m] {a b : Type} (f : a → b) :
    kG (kF (m := m) f) = Functor.map f := by
  funext x
  simp only [kG, kF, Function.comp, join, map_eq_pure_bind, bind_assoc, pure_bind, id]
```

伴随本身更是一目了然：$\mathcal{C}_T(F a, b) = (a \to T\,b) = \mathcal{C}(a, G b)$，两边**字面上是同一个集合**。
:::

所以，这就是产生同一个单子的第二个伴随。事实上，存在一整个伴随范畴 $\mathbf{Adj}(\mathcal{C}, T)$，其中的伴随都产生 $\mathcal{C}$ 上同一个单子 $T$。
我们刚才见到的 Kleisli 伴随是这个范畴中的始对象，而 Eilenberg–Moore 伴随是终对象。

::: tip Rust 视角：两种“副作用”的范畴
设想 `T = Option`。Kleisli 箭头是 `fn(A) -> Option<B>`，复合就是 `f(x).and_then(g)`，这是你天天写的东西。
而 `Option` 的 Eilenberg–Moore 代数是一个 `fn(Option<A>) -> A` 满足 `alg(Some(x)) == x`，也就是给 `None` 选一个默认值，
就像 `unwrap_or(d)`：一个**带基点的集合**。Kleisli 关心“怎样串联可能失败的计算”，Eilenberg–Moore 关心“怎样消化失败”。
:::

## 余单子的余代数

类似的构造可以对任何[余单子](/part3/07-comonads) $W$ 进行。我们可以定义一个由与余单子相容的余代数组成的范畴。它们使下面的图交换：

```diagram
a: (0, 1.5) "a"
Wa: (2, 0) "W\,a"
a2: (0, 0) "a"
coa: a -> Wa "\mathit{coa}" side=right
eps: Wa -> a2 "\varepsilon_a" side=right
id: a -> a2 "\mathrm{id}_a"
path "coa 再 ε": coa eps
path "恒等": id color=green
caption: 余单位律：$\varepsilon_a \circ \mathit{coa} = \mathrm{id}_a$。
```

```diagram
a: (2, 1.5) "a"
Wa1: (2, 0) "W\,a"
Wa2: (0, 1.5) "W\,a"
WWa: (0, 0) "W(W\,a)"
coa1: a -> Wa1 "\mathit{coa}" side=right
coa2: a -> Wa2 "\mathit{coa}"
Wcoa: Wa1 -> WWa "W\,\mathit{coa}" side=right
delta: Wa2 -> WWa "\delta_a"
path "coa 再 W coa": coa1 Wcoa
path "coa 再 δ": coa2 delta color=green
caption: 余结合律：$\delta_a \circ \mathit{coa} = W\,\mathit{coa} \circ \mathit{coa}$。
```

其中 $\mathit{coa}$ 是载体为 $a$ 的余代数的余求值态射：

$$\mathit{coa} : a \to W\,a$$

而 $\varepsilon$ 和 $\delta$ 是定义余单子的两个自然变换（在 Haskell 中，它们的分量叫作 `extract` 和 `duplicate`）。

::: tip Lean 深入：自己定义余单子
Lean 核心库没有余单子类型类，我们自己定义一个最小版本，并把余代数的两条定律写进结构体：

```lean
end EM

class Comonad (w : Type → Type) extends Functor w where
  extract : w a → a
  duplicate : w a → w (w a)

structure ComonadCoalgebra (w : Type → Type) [Comonad w] (a : Type) where
  coa : a → w a
  counit_law : ∀ x, Comonad.extract (coa x) = x
  coassoc_law : ∀ x, Comonad.duplicate (coa x) = Functor.map coa (coa x)
```
:::

从这些余代数组成的范畴到 $\mathcal{C}$ 有一个显然的遗忘函子 $U^W$。它只是忘掉余求值。我们来考虑它的右伴随 $F^W$：

$$U^W \dashv F^W$$

遗忘函子的右伴随叫作**余自由函子**（cofree functor）。$F^W$ 生成余自由的余代数。它给 $\mathcal{C}$ 中的对象 $a$ 指派余代数 $(W\,a, \delta_a)$。
这个伴随把原来的余单子重新产生为复合 $U^W \circ F^W$。

类似地，我们可以构造一个带有 co-Kleisli 箭头的 co-Kleisli 范畴，并从相应的伴随重新生成这个余单子。

## 透镜

我们回到关于透镜的讨论。一个透镜可以写成一个余代数：

$$\mathit{coalg}_s : a \to \mathit{Store}\ s\ a$$

针对的是函子 $\mathit{Store}\ s$：

```lean
structure Store (s a : Type) where
  peek : s → a
  pos : s
```

这个余代数也可以表示为一对函数：

$$\mathit{set} : a \to s \to a \qquad \mathit{get} : a \to s$$

（可以把 $a$ 想成代表“全部”（all），把 $s$ 想成它的一个“小”（small）部分。）用这一对函数来表示，我们有：

$$\mathit{coalg}_s\ a = \mathit{Store}\ (\mathit{set}\ a)\ (\mathit{get}\ a)$$

这里的 $a$ 是一个类型为 $a$ 的值。注意，部分应用的 `set` 是一个函数 $s \to a$。

```lean
structure Lens (a s : Type) where
  get : a → s
  set : a → s → a

def Lens.coalg {a s : Type} (l : Lens a s) : a → Store s a := fun x => ⟨l.set x, l.get x⟩
```

我们也知道 $\mathit{Store}\ s$ 是一个余单子：

```lean
instance : Comonad (Store s) where
  map g x := ⟨g ∘ x.peek, x.pos⟩
  extract x := x.peek x.pos
  duplicate x := ⟨fun s' => ⟨x.peek, s'⟩, x.pos⟩
```

问题是：在什么条件下，透镜是这个余单子的一个余代数？第一个相干条件：

$$\varepsilon_a \circ \mathit{coalg} = \mathrm{id}_a$$

翻译过来就是：

```lean no-check
set a (get a) = a
```

这条透镜定律表达的事实是：如果你把结构 $a$ 的一个字段设成它原来的值，什么都不会改变。这条定律也被称为 **GETPUT**。

第二个条件：

$$\mathit{fmap}\ \mathit{coalg} \circ \mathit{coalg} = \delta_a \circ \mathit{coalg}$$

需要多做一点工作。首先，回忆一下 `Store` 函子的 `fmap` 定义：

```lean no-check
Functor.map g ⟨f, s⟩ = ⟨g ∘ f, s⟩
```

把 `fmap coalg` 应用到 `coalg` 的结果上，得到：

```lean no-check
⟨coalg ∘ set a, get a⟩
```

另一方面，把 `duplicate` 应用到 `coalg` 的结果上，产生的是：

```lean no-check
⟨fun s => ⟨set a, s⟩, get a⟩
```

要让这两个表达式相等，`Store` 之下的两个函数在作用于任意的 `s` 时必须相等：

```lean no-check
coalg (set a s) = ⟨set a, s⟩
```

展开 `coalg`，我们得到：

```lean no-check
⟨set (set a s), get (set a s)⟩ = ⟨set a, s⟩
```

这等价于剩下的两条透镜定律。第一条：

```lean no-check
set (set a s) = set a
```

告诉我们，把一个字段的值设两次，和设一次是一样的。这条定律也被称为 **PUTPUT**。第二条定律：

```lean no-check
get (set a s) = s
```

告诉我们，获取一个已被设为 $s$ 的字段的值，会得回 $s$。这条定律也被称为 **PUTGET**。

满足 GETPUT 和 PUTGET 的透镜叫作**良好的**（well-behaved）透镜。如果透镜还满足 PUTPUT，它就叫作**非常良好的**（very well-behaved）透镜。
换句话说，一个非常良好的透镜确实就是 `Store` 函子的一个余单子余代数。

::: tip Lean 深入：把这个“当且仅当”证出来
```lean
def Lens.GetPut {a s : Type} (l : Lens a s) : Prop := ∀ x, l.set x (l.get x) = x
def Lens.PutPut {a s : Type} (l : Lens a s) : Prop := ∀ x v, l.set (l.set x v) = l.set x
def Lens.PutGet {a s : Type} (l : Lens a s) : Prop := ∀ x v, l.get (l.set x v) = v

theorem lens_coalgebra_iff {a s : Type} (l : Lens a s) :
    ((∀ x, Comonad.extract (l.coalg x) = x) ∧
     (∀ x, Comonad.duplicate (l.coalg x) = Functor.map l.coalg (l.coalg x)))
    ↔ (l.GetPut ∧ l.PutPut ∧ l.PutGet) := by
  constructor
  · -- 余代数定律 ⇒ 三条透镜定律
    intro ⟨h1, h2⟩
    refine ⟨h1, ?_, ?_⟩
    · intro x v
      -- 在位置 v 处比较两个内层 Store 的 peek 分量
      have := congrArg (fun st => (st.peek v).peek) (h2 x)
      exact this.symm
    · intro x v
      -- 在位置 v 处比较两个内层 Store 的 pos 分量
      have := congrArg (fun st => (st.peek v).pos) (h2 x)
      exact this.symm
  · -- 三条透镜定律 ⇒ 余代数定律
    intro ⟨gp, pp, pg⟩
    refine ⟨gp, fun x => ?_⟩
    show Store.mk (fun s' => Store.mk (l.set x) s') (l.get x)
      = Store.mk (fun v => Store.mk (l.set (l.set x v)) (l.get (l.set x v))) (l.get x)
    congr
    funext v
    rw [pp, pg]
```

- `P ↔ Q` 是“当且仅当”。`constructor` 把它拆成两个目标：`P → Q` 和 `Q → P`。
- `intro ⟨h1, h2⟩` 在引入假设的同时把合取拆开（模式匹配）。
- `congrArg φ h` 从 `h : u = v` 得到 `φ u = φ v`。这里用它从“两个 Store 相等”中**取出分量**相等。
- `congr` 把 `Store.mk f p = Store.mk g q` 化简为 `f = g`（`p = q` 两边相同，自动解决）。

用一个具体的透镜试一下：

```lean
structure Point where
  x : Int
  y : Int

/-- 聚焦于 x 坐标的透镜。 -/
def xLens : Lens Point Int := ⟨Point.x, fun p v => { p with x := v }⟩

theorem xLens_lawful : xLens.GetPut ∧ xLens.PutPut ∧ xLens.PutGet :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- 于是 xLens 给出一个 Store 余单子的余代数。 -/
def xCoalgebra : ComonadCoalgebra (Store Int) Point where
  coa := xLens.coalg
  counit_law := ((lens_coalgebra_iff xLens).mpr xLens_lawful).1
  coassoc_law := ((lens_coalgebra_iff xLens).mpr xLens_lawful).2
```
:::

::: tip Rust 视角：透镜定律就是“setter 的合理行为”
Rust 里你很少写透镜，但你一定写过 getter/setter：`fn x(&self) -> i64` 和 `fn set_x(&mut self, v: i64)`。
三条定律就是你**默认**它们满足的东西：`p.set_x(p.x())` 不改变 `p`；`set_x(a); set_x(b)` 等于 `set_x(b)`；`set_x(v)` 之后 `x()` 返回 `v`。
一个会在 `set_x` 里偷偷记日志、计数或做规范化（比如把值截断到某个范围）的 setter，就会违反其中一条。
:::

## 挑战

1. 自由函子 $F^T : \mathcal{C} \to \mathcal{C}^T$ 在态射上的作用是什么？提示：使用单子 $\mu$ 的自然性条件。
2. 定义伴随：$U^W \dashv F^W$
3. 证明上述伴随重新产生了原来的余单子。

::: details 参考答案
**1.** $F^T$ 把 $f : a \to b$ 送到 $T\,f : T\,a \to T\,b$。要验证它是从 $(T\,a, \mu_a)$ 到 $(T\,b, \mu_b)$ 的同态，即
$T\,f \circ \mu_a = \mu_b \circ T(T\,f)$，而这正是 $\mu$ 的自然性条件：

```lean
section Ch1
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def freeMap {a b : Type} (f : a → b) : THom (FreeT (m := m) a) (FreeT b) where
  map := Functor.map f
  comm x := join_natural f x
end Ch1
```

**2.** 对余代数 $A = (a, \mathit{coa})$ 和对象 $b$，要给出一一对应
$\mathcal{C}(U^W A,\ b) \cong \mathbf{Coalg}(A,\ F^W b)$，其中 $F^W b = (W\,b, \delta_b)$：

- $g : a \to b$ 对应 $W\,g \circ \mathit{coa} : a \to W\,b$；
- 余代数同态 $h : a \to W\,b$ 对应 $\varepsilon_b \circ h : a \to b$。

为此需要余单子定律。下面先把它们写成一个类型类：

```lean
class LawfulComonad (w : Type → Type) [Comonad w] : Prop where
  map_comp : ∀ {a b c : Type} (f : a → b) (g : b → c) (x : w a),
    Functor.map (g ∘ f) x = Functor.map g (Functor.map f x)
  extract_map : ∀ {a b : Type} (f : a → b) (x : w a),
    Comonad.extract (Functor.map f x) = f (Comonad.extract x)
  duplicate_map : ∀ {a b : Type} (f : a → b) (x : w a),
    Comonad.duplicate (Functor.map f x) = Functor.map (Functor.map f) (Comonad.duplicate x)
  map_extract_duplicate : ∀ {a : Type} (x : w a),
    Functor.map Comonad.extract (Comonad.duplicate x) = x

/-- Store 满足这些定律，而且全都是 rfl。 -/
instance : LawfulComonad (Store s) where
  map_comp _ _ _ := rfl
  extract_map _ _ := rfl
  duplicate_map _ _ := rfl
  map_extract_duplicate _ := rfl

section Cofree
variable {w : Type → Type} [Comonad w] [LawfulComonad w]

def toCofree {a b : Type} (A : ComonadCoalgebra w a) (g : a → b) : a → w b :=
  fun x => Functor.map g (A.coa x)

def fromCofree {a b : Type} (h : a → w b) : a → b := fun x => Comonad.extract (h x)

/-- toCofree g 确实是到余自由余代数 (W b, δ) 的余代数同态。 -/
theorem toCofree_hom {a b : Type} (A : ComonadCoalgebra w a) (g : a → b) (x : a) :
    Comonad.duplicate (toCofree A g x) = Functor.map (toCofree A g) (A.coa x) := by
  show Comonad.duplicate (Functor.map g (A.coa x))
    = Functor.map (fun y => Functor.map g (A.coa y)) (A.coa x)
  rw [LawfulComonad.duplicate_map, A.coassoc_law]
  exact (LawfulComonad.map_comp A.coa (Functor.map g) (A.coa x)).symm

/-- 往返一：ε ∘ (W g ∘ coa) = g。 -/
theorem from_toCofree {a b : Type} (A : ComonadCoalgebra w a) (g : a → b) :
    fromCofree (toCofree A g) = g := by
  funext x
  show Comonad.extract (Functor.map g (A.coa x)) = g x
  rw [LawfulComonad.extract_map, A.counit_law]

/-- 往返二：对余代数同态 h，W (ε ∘ h) ∘ coa = h。 -/
theorem to_fromCofree {a b : Type} (A : ComonadCoalgebra w a) (h : a → w b)
    (hh : ∀ x, Comonad.duplicate (h x) = Functor.map h (A.coa x)) :
    toCofree A (fromCofree h) = h := by
  funext x
  show Functor.map (fun y => Comonad.extract (h y)) (A.coa x) = h x
  have : (fun y => Comonad.extract (h y)) = Comonad.extract ∘ h := rfl
  rw [this, LawfulComonad.map_comp, ← hh, LawfulComonad.map_extract_duplicate]
end Cofree
```

**3.** 伴随 $U^W \dashv F^W$ 产生的余单子是 $U^W \circ F^W$：

- 在对象上：$b \mapsto (W\,b, \delta_b) \mapsto W\,b$，所以 $U^W \circ F^W = W$。
- 余单位 $\varepsilon : U^W \circ F^W \to I$ 在 $b$ 处是 `fromCofree id`，即 $\varepsilon_b \circ \mathrm{id} = \varepsilon_b$，就是 `extract`。
- 余乘法 $U^W\,\eta\,F^W$：伴随的单位 $\eta$ 在余代数 $(W\,b, \delta_b)$ 处的分量是 `toCofree` 作用于 $\mathrm{id}_{Wb}$，
  即 $W\,\mathrm{id} \circ \delta_b = \delta_b$，就是 `duplicate`。

最后一点可以直接验证：

```lean
example {w : Type → Type} [Comonad w] [LawfulFunctor w] {b : Type} (x : w b) :
    Functor.map id (Comonad.duplicate x) = Comonad.duplicate x := id_map _
```

所以这个伴随重新产生了 $(W, \varepsilon, \delta)$。
:::

## 本章小结

- **单子的代数**（$T$-代数）是 $T$ 上的 F-代数 $\mathit{alg} : T\,a \to a$，并满足 $\mathit{alg} \circ \eta = \mathrm{id}$（单位律）和 $\mathit{alg} \circ \mu = \mathit{alg} \circ T\,\mathit{alg}$（乘法律）。
- `List` 单子的代数**恰好就是幺半群**：我们在 Lean 中证明了两个方向（`monoidAlgebra` 和 `algebraMonoid`）。一般地，单子描述一种代数结构的“自由版本”，它的代数就是这种结构的实例。
- $T$-代数及其同态构成 **Eilenberg–Moore 范畴** $\mathcal{C}^T$。遗忘函子 $U^T$ 有左伴随 $F^T$，$F^T a = (T\,a, \mu_a)$ 是自由代数。
- 伴随 $F^T \dashv U^T$ 重新产生单子 $T$，所以**每个单子都来自一个伴随**。余单位在 $(a, f)$ 处就是 $f$：同一个方块，既是代数定律又是同态条件。
- **Kleisli 范畴**给出另一个产生 $T$ 的伴随。在所有产生 $T$ 的伴随中，Kleisli 是始对象，Eilenberg–Moore 是终对象。
- 对偶地，余单子 $W$ 有**余代数**；遗忘函子 $U^W$ 有右伴随（余自由函子）$F^W b = (W\,b, \delta_b)$，伴随 $U^W \dashv F^W$ 重新产生 $W$。
- **透镜**是 `Store s` 的余代数；它是**余单子**余代数，当且仅当满足 GETPUT、PUTPUT、PUTGET 三条定律（“非常良好的透镜”）。这个“当且仅当”在 Lean 中证明了。
- Lean 核心库没有 `List` 的 `Monad` 实例，也没有 `Comonad` 类；本章自己补上，并把定律写进了类型。
