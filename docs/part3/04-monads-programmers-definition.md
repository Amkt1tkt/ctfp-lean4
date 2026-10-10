# 3.4 单子：程序员的定义

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

程序员们围绕单子编织出了一整套神话。据说它是编程里最抽象、最难懂的概念之一；世上的人分成两种：“懂了的”和“还没懂的”。对不少人来说，顿悟单子的那一刻简直像一次宗教体验。单子抽象出的是许许多多看起来毫不相干的构造的共同本质，日常生活里根本找不到一个贴切的类比。于是我们只能在黑暗中摸索，就像盲人摸象：摸到尾巴的人得意地宣布“这是一根绳子”，摸到腿的人说“这是一棵树”，还有人说“这是一张墨西哥卷饼（burrito）！”

让我把话说清楚：笼罩在单子周围的所有神秘感，都源于一场误会。单子本身是个非常简单的概念；让人困惑的，是它的**用途**五花八门。

为了写这一章，我专门查了查**布基胶带**（duct tape，又叫“鸭子胶带”）都能拿来干什么。随手摘几条：

- 封住通风管道；
- 在阿波罗 13 号上修好二氧化碳过滤器；
- 治疗瘊子；
- 解决苹果 iPhone 4 一握就掉线的问题；
- 做一条毕业舞会穿的裙子；
- 搭一座吊桥。

现在想象一下：你从来没见过布基胶带，只能根据上面这张清单去猜它是什么东西。祝你好运！

所以我想给“单子就像……”这个陈词滥调的大家族再添一员：**单子就像布基胶带**。它的用途千奇百怪，原理却极其朴素：它把东西粘在一起。说得更准确些——它把东西**复合**起来。

这在一定程度上解释了为什么很多程序员（尤其是命令式背景出身的）理解单子时那么吃力。问题在于，我们不习惯用“函数复合”的方式来思考编程。这完全可以理解：我们总爱给中间结果起名字，而不是把它直接从一个函数递给下一个函数；我们也习惯把一小段一小段的“胶水代码”直接内联，而不是把它们抽象成辅助函数。下面是一个命令式风格的“求向量长度”函数（原书用 C 写，这里换成 Rust，味道是一样的）：

```rust
fn vlen(v: &[f64; 3]) -> f64 {
    let mut d = 0.0;
    for n in 0..3 {
        d += v[n] * v[n];
    }
    d.sqrt()
}
```

对比一下这个（刻意风格化的）Lean 版本，它把函数复合摆到了明面上：

```lean
def vlen : List Float → Float := Float.sqrt ∘ List.sum ∘ List.map (· ^ 2)

#guard vlen [3, 4, 0] == 5
#guard vlen [1, 2, 2] == 3
```

（为了让它看起来更“天书”一点，我用了 Lean 的**占位符语法** `(· ^ 2)`：`·` 标出参数的位置，`(· ^ 2)` 就是 `fun x => x ^ 2`，相当于把乘方运算的第二个参数固定为 `2`。Haskell 里要写成 `flip (^) 2`，Lean 的写法友好多了。读法从右往左：先对每个分量平方，再求和，最后开方。）

::: tip Lean 深入：`#guard`
`#guard e` 会在编译时求值布尔表达式 `e`，如果结果不是 `true` 就报错。本书用它代替“在注释里写出 `#eval` 的输出”，这样你在书上看到的结果都经过了机器检验。
:::

我并不是说 Lean（或 Haskell）的无点（point-free）风格总是更好，我只是想强调：函数复合是我们在编程中所做一切事情的最底层。而且，尽管我们实际上一直在复合函数，函数式语言还是不遗余力地为“单子复合”提供了一套命令式风格的语法，叫作 **`do` 记法**（do notation）。稍后我们会看到它怎么用。不过首先，我得解释一下，我们为什么需要单子复合。

## Kleisli 范畴

我们之前（见 [1.4 Kleisli 范畴](/part1/04-kleisli-categories)）通过“修饰”普通函数得到了 **Writer 单子**。具体的修饰方式是：把函数的返回值和一个字符串配成一对；更一般地，和某个**幺半群**（monoid）里的元素配成一对。现在我们可以认出来：这种修饰其实是一个函子。

::: info 数学小课堂：幺半群回顾
**幺半群**就是一个集合 $M$，配上一个二元运算 $\diamond$（读作“拼接”）和一个特殊元素 $e$（“单位元”），满足：

- 结合律：$(x \diamond y) \diamond z = x \diamond (y \diamond z)$；
- 单位律：$e \diamond x = x$，$x \diamond e = x$。

最常见的例子：字符串配上拼接 `++` 和空串 `""`；自然数配上加法和 `0`；自然数配上乘法和 `1`。在 Writer 单子里，幺半群负责“把两段日志接起来”，而空日志就是单位元。
:::

Lean 核心库没有 `Monoid` 类（Mathlib 有），我们自己定义一个，并且——这是 Lean 胜过 Haskell 的地方——把幺半群定律直接写进类型类：

```lean
class Monoid (w : Type) where
  mempty : w
  mappend : w → w → w
  mempty_mappend : ∀ x : w, mappend mempty x = x
  mappend_mempty : ∀ x : w, mappend x mempty = x
  mappend_assoc : ∀ x y z : w, mappend (mappend x y) z = mappend x (mappend y z)

export Monoid (mempty mappend)
infixr:65 " <> " => Monoid.mappend

instance : Monoid String where
  mempty := ""
  mappend := (· ++ ·)
  mempty_mappend _ := String.empty_append
  mappend_mempty _ := String.append_empty
  mappend_assoc _ _ _ := String.append_assoc
```

`export Monoid (mempty mappend)` 让我们可以直接写 `mempty`、`mappend`，不必加 `Monoid.` 前缀；`infixr:65 " <> "` 声明一个右结合、优先级 65 的中缀记号。字符串的三条定律在核心库里都已经有现成的定理，直接拿来用。

接下来是 Writer 函子本身：

```lean
structure Writer (w : Type) (α : Type) where
  run : α × w

instance : Functor (Writer w) where
  map f | ⟨(a, w)⟩ => ⟨(f a, w)⟩
```

`Writer w α` 只是把一个 `α × w` 包了一层，对应 Haskell 的 `newtype`。`map` 只动值、不动日志。

::: tip Lean 深入：`structure` 与匿名构造子
`structure Writer (w α : Type) where run : α × w` 定义了一个只有一个字段 `run` 的结构体。`⟨(a, w)⟩` 是**匿名构造子**记法：外层的 `⟨…⟩` 构造 `Writer`，里面的 `(a, w)` 是一个积（二元组）。在 `map f | ⟨(a, w)⟩ => …` 里，它被用作模式，一次性把结构体和二元组都拆开。
:::

随后我们找到了复合这些修饰函数——也就是 **Kleisli 箭头**（Kleisli arrow）——的方法。Kleisli 箭头就是形如下面这样的函数：

```lean no-check
α → Writer w β
```

正是在复合的过程中，我们实现了日志的累积。

现在可以给 Kleisli 范畴一个更一般的定义了。从一个范畴 $\mathcal{C}$ 和一个自函子 $m$ 出发。对应的 **Kleisli 范畴** $\mathcal{K}$ 和 $\mathcal{C}$ 有相同的对象，但态射不同：$\mathcal{K}$ 中从对象 $a$ 到对象 $b$ 的一个态射，是用原范畴 $\mathcal{C}$ 中的一个态射

$$a \to m\ b$$

来**实现**的。一定要记住：我们把 $\mathcal{K}$ 中的 Kleisli 箭头看作 $a$ 和 $b$ 之间的态射，而**不是** $a$ 和 $m\ b$ 之间的态射。

```diagram
a: (0, 0)
b: (2, 0)
c: (4, 0)
f: a -> b "f"
g: b -> c "g"
gf: a -> c "g \circ_K f" bend=-45 side=right color=green
path "先走 f，再走 g": f g
path "直接走复合箭头": gf color=green
caption: 在 Kleisli 范畴 K 里，f 是 a 到 b 的箭头、g 是 b 到 c 的箭头；它们“看起来”和普通范畴一样，能够复合。
```

```diagram
a: (0, 0)
mb: (2, 0) "m\ b"
b: (2, 1.4)
mc: (4, 1.4) "m\ c"
f: a -> mb "f"
g: b -> mc "g"
gap: b -> mb "?" dashed color=gray
caption: 但在原范畴 C 里，f 的终点是 m b，g 的起点却是 b——两头接不上。单子要解决的正是这个“接头”问题。
```

在我们的例子里，$m$ 被具体化为 `Writer w`，其中 `w` 是某个固定的幺半群。

Kleisli 箭头只有在我们能为它们定义恰当的复合时才构成范畴。如果存在一种复合，它满足结合律，并且每个对象上都有一个恒等箭头，那么函子 $m$ 就叫作一个**单子**（monad），而得到的范畴就叫作 Kleisli 范畴。

在 Haskell 中，Kleisli 复合用“鱼运算符” `>=>` 来定义，恒等箭头是一个叫 `return` 的多态函数。照着这个思路，我们可以用 Kleisli 复合来定义单子（放进命名空间 `KleisliDef`，免得和 Lean 自带的 `Monad` 撞名；鱼运算符暂时记作 `>=>'`，因为 `>=>` 已被核心库占用，下面马上讲）：

```lean
namespace KleisliDef

class Monad (m : Type → Type) where
  fish : {α β γ : Type} → (α → m β) → (β → m γ) → (α → m γ)
  ret : {α : Type} → α → m α

infixr:55 " >=>' " => Monad.fish
```

::: tip Lean 深入：为什么要写 `{α β γ : Type}`
花括号表示**隐式参数**：调用 `fish f g` 时，Lean 会根据 `f`、`g` 的类型自动推断出 `α β γ`。在类型类的字段里，我们必须把它们明确写成 `Type`，否则 Lean 会试图让它们“宇宙多态”，而类的字段不允许含有未定的宇宙层级。本书只在 `Type` 这一层工作就够了。
:::

请记住，定义单子有许多等价的方式，而这种方式并不是 Haskell（或 Lean）生态里的主流。我喜欢它，是因为它概念上最简单、最能给人直觉；但还有其他在编程时更顺手的定义。我们马上就会谈到。

在这种表述下，单子定律非常容易写出来。Haskell 没法强制这些定律，只能拿它们做等式推理。它们不过就是 Kleisli 范畴的标准复合定律：

```lean no-check
(f >=> g) >=> h = f >=> (g >=> h)   -- 结合律
return >=> f = f                    -- 左单位律
f >=> return = f                    -- 右单位律
```

而在 Lean 里，我们可以把它们写成**定理**，并且真的证明出来——稍后就对 Writer 这么做，章末的补充小节还会对**一切**合法单子这么做。

这样的定义也道出了单子的真正面目：**它是复合修饰函数的一种方式**。它与副作用无关，与状态无关，只与复合有关。我们后面会看到，修饰函数可以用来表达各种各样的效应或状态，但那并不是单子存在的理由。单子是那卷黏糊糊的布基胶带，把一个修饰函数的一头粘到另一个修饰函数的另一头上。

回到我们的 `Writer` 例子：记日志的函数（`Writer` 函子的 Kleisli 箭头）之所以构成一个范畴，是因为 `Writer` 是一个单子：

```lean
instance [Monoid w] : Monad (Writer w) where
  fish f g := fun a =>
    let ⟨(b, s)⟩ := f a
    let ⟨(c, s')⟩ := g b
    ⟨(c, s <> s')⟩
  ret a := ⟨(a, mempty)⟩
```

只要 `w` 满足幺半群定律，`Writer w` 就满足单子定律。Haskell 同样无法强制前者；而我们的 `Monoid` 类已经把定律装进了类型里，所以可以直接证明后者：

::: details 完整证明：Writer 满足 Kleisli 形式的三条单子定律
证明的套路是：先用 `funext a` 把“两个函数相等”化为“对每个输入 `a` 结果相等”；再用 `rcases` 把 `f a`、`g b`、`h c` 拆成“值 + 日志”；最后剩下的就只是日志之间的等式，交给幺半群定律。

```lean
open KleisliDef.Monad in
theorem writer_fish_assoc [Monoid w]
    (f : α → Writer w β) (g : β → Writer w γ) (h : γ → Writer w δ) :
    ((f >=>' g) >=>' h) = (f >=>' (g >=>' h)) := by
  funext a
  simp only [fish]
  rcases f a with ⟨b, s₁⟩     -- f a = ⟨(b, s₁)⟩
  rcases g b with ⟨c, s₂⟩     -- g b = ⟨(c, s₂)⟩
  rcases h c with ⟨d, s₃⟩     -- h c = ⟨(d, s₃)⟩
  -- 剩下 (s₁ <> s₂) <> s₃ = s₁ <> (s₂ <> s₃)：幺半群的结合律
  simp [Monoid.mappend_assoc]

theorem writer_ret_fish [Monoid w] (f : α → Writer w β) : (Monad.ret >=>' f) = f := by
  funext a
  simp only [Monad.fish, Monad.ret]
  rcases f a with ⟨b, s⟩
  simp [Monoid.mempty_mappend]   -- mempty <> s = s

theorem writer_fish_ret [Monoid w] (f : α → Writer w β) : (f >=>' Monad.ret) = f := by
  funext a
  simp only [Monad.fish, Monad.ret]
  rcases f a with ⟨b, s⟩
  simp [Monoid.mappend_mempty]   -- s <> mempty = s

end KleisliDef
```

几个第一次出现的 tactic：

- `funext a`：函数外延性——要证 `F = G`，只需证对任意 `a` 都有 `F a = G a`；
- `rcases e with ⟨b, s⟩`：对表达式 `e` 做分情况拆解，把结构体/二元组拆成分量并起名；
- `simp only [fish]`：只用给定的定义/引理做化简（这里是展开 `fish` 的定义）；`simp [...]` 则还会用上默认的化简引理库。

注意单子的结合律**恰好**来自幺半群的结合律，单位律**恰好**来自幺半群的单位律。这不是巧合：Writer 单子把幺半群的结构“搬”到了 Kleisli 箭头上。
:::

对 `Writer` 单子，还有一个很有用的 Kleisli 箭头，叫 `tell`。它唯一的用途就是把参数追加到日志里：

```lean
def tell (s : w) : Writer w Unit := ⟨((), s)⟩
```

我们之后会把它当作积木，搭建其他单子函数。

下面的小工具让你亲手“拼鱼”：三个记日志的 Kleisli 箭头，你可以切换括号的结合方式，或者在两头插上 `ret`，观察值和日志如何沿着管道累积。

<div class="ctfp-widget-host"><Ch3_4KleisliWriter /></div>

## 鱼的解剖学

当你为不同的单子实现鱼运算符时，很快会发现大量代码是重复的，可以轻松地提取出来。首先，两个函数的 Kleisli 复合必须返回一个函数，所以它的实现不妨从一个接受 `α` 类型参数的 lambda 开始：

```lean no-check
def fish (f : α → m β) (g : β → m γ) : α → m γ :=
  fun a => _
```

对这个参数，我们唯一能做的事就是把它传给 `f`：

```lean no-check
def fish (f : α → m β) (g : β → m γ) : α → m γ :=
  fun a =>
    let mb := f a
    _
```

（`_` 在 Lean 里表示“这里还空着”，编译器会告诉你这个洞需要什么类型——对理解代码非常有帮助的一个习惯。）

此刻我们必须产生一个 `m γ` 类型的结果，手头有的是一个 `m β` 类型的对象，以及一个函数 `g : β → m γ`。我们定义一个专门干这件事的函数。它叫作 **bind**（绑定），通常写成中缀运算符：

```lean no-check
(>>=) : m α → (α → m β) → m β
```

对每个单子，我们可以不定义鱼运算符，而改为定义 bind。实际上，Haskell 的标准单子定义用的正是 bind：

```lean
namespace BindDef
class Monad (m : Type → Type) where
  bind : {α β : Type} → m α → (α → m β) → m β
  ret : {α : Type} → α → m α
end BindDef
```

Lean 也是如此。Lean 核心库的 `Monad` 类大致长这样（我们把继承来的字段展开写）：

```lean no-check
class Monad (m : Type u → Type v) extends Applicative m, Bind m where
  -- 来自 Pure：      pure : α → m α
  -- 来自 Bind：      bind : m α → (α → m β) → m β
  -- 来自 Functor 等：map、seq、seqLeft、seqRight 都有基于 bind 的默认实现
```

所以在 Lean 里：

| 原书（Haskell） | Lean 4 |
|---|---|
| `return` | `pure`（在 `do` 块里也可以写关键字 `return`，见下文） |
| `>>=` | `>>=`，即 `bind` |
| `>=>` | `>=>`，即 `Bind.kleisliRight` |
| `join` | 核心库**没有**通用的 `join`/`joinM`（Mathlib 有 `joinM`）；有特定版本 `Option.join`、`List.flatten` |

最后一行我在 Lean 4.34 里实际查证过：`#check @joinM` 和 `#check @Monad.join` 都会报“未知标识符”。而鱼运算符确实在核心库里，定义就是我们刚推出来的样子：

```lean no-check
-- 核心库中的定义（#print Bind.kleisliRight 的输出）
def Bind.kleisliRight [Bind m] (f₁ : α → m β) (f₂ : β → m γ) : α → m γ :=
  fun a => f₁ a >>= f₂
-- 记号：f >=> g 即 Bind.kleisliRight f g；g <=< f 即 Bind.kleisliLeft g f；f =<< x 即 x >>= f
```

```lean
example (f g : Nat → Option Nat) : (f >=> g) = fun a => f a >>= g := rfl
example (f g : Nat → Option Nat) : (g <=< f) = (f >=> g) := rfl
```

注意核心库的 `>=>` 是**由 bind 派生出来的**，而不是像我们的 `KleisliDef` 那样作为基本操作。这正说明了 bind 才是工程上的主角。

下面是 `Writer` 单子的 bind，写成 Lean 核心 `Monad` 类的实例：

```lean
instance [Monoid w] : Monad (Writer w) where
  map f x := f <$> x
  pure a := ⟨(a, mempty)⟩
  bind x f :=
    let (a, s) := x.run
    let (b, s') := (f a).run
    ⟨(b, s <> s')⟩
```

它确实比鱼运算符的定义短一些。（`map f x := f <$> x` 这一行只是告诉 Lean 沿用上面定义好的 `Functor` 实例；如果省略，Lean 会自动用 `bind` 和 `pure` 生成一个 `map`。）

### `LawfulMonad`：把单子定律写进类型类

Haskell 的单子定律只能写在文档里，靠程序员自觉。Lean 则有一个专门的类 `LawfulMonad m`，它的字段**就是**定律（以及与 `Functor`、`Applicative` 部分相容的定律）。其中最核心的两条是：

```lean no-check
pure_bind  : pure x >>= f = f x                                    -- 左单位律
bind_assoc : x >>= f >>= g = x >>= fun a => f a >>= g              -- 结合律
-- 右单位律 x >>= pure = x 可由 id_map 与 bind_pure_comp 推出（核心库定理 bind_pure）
```

为一个单子提供 `LawfulMonad` 实例，就是为它的定律给出**证明**。核心库提供了一个便捷构造器 `LawfulMonad.mk'`，只要求你证明三条关键定律，其余的若能用 `rfl` 自动证出就自动补上，不能的话再手动提供。我们为 Writer 证明：

```lean
instance [Monoid w] : LawfulMonad (Writer w) := LawfulMonad.mk'
  -- id <$> x = x：map 只改值不动日志，定义上就成立
  (id_map := fun _ => rfl)
  -- pure a >>= f = f a：归结为 mempty <> s = s
  (pure_bind := by
    intro α β a f
    show (⟨((f a).run.1, mempty <> (f a).run.2)⟩ : Writer w β) = f a
    rw [Monoid.mempty_mappend])
  -- 结合律：归结为日志的 (s₁ <> s₂) <> s₃ = s₁ <> (s₂ <> s₃)
  (bind_assoc := by
    intro α β γ x f g
    show (⟨_, (x.run.2 <> _) <> _⟩ : Writer w γ) = ⟨_, x.run.2 <> (_ <> _)⟩
    rw [Monoid.mappend_assoc])
  -- (do let y ← x; pure (f y)) = f <$> x：归结为 s <> mempty = s
  (bind_pure_comp := by
    intro α β f x
    show (⟨(f x.run.1, x.run.2 <> mempty)⟩ : Writer w β) = ⟨(f x.run.1, x.run.2)⟩
    rw [Monoid.mappend_mempty])
```

::: tip Lean 深入：`show` 与 `rw`
`show T` 把当前目标**改写成一个定义上相等的形式** `T`——Lean 会检查两者确实只差在定义展开上。这里我们用它把 `pure a >>= f` 这种抽象的写法“摊开”成具体的二元组，让剩下的差别一目了然。`_` 表示“这部分你自己填，我不关心”。

`rw [h]` 用等式 `h : l = r` 把目标中的 `l` 改写成 `r`。改写完如果两边一模一样，目标自动关闭。
:::

我们可以利用 `m` 是函子这一事实，把 bind 进一步拆开。用 `map`（Lean 中写作 `<$>`）把函数 `α → m β` 作用在 `m α` 的内容上，就把每个 `α` 变成了 `m β`，于是整个结果的类型是 `m (m β)`。这还不完全是我们要的——我们要的是 `m β`——但已经很接近了。只差一个能把两层 `m` “压扁”成一层的函数。这个函数叫 **`join`**：

```lean no-check
join : m (m α) → m α
```

前面说过，Lean 核心库没有通用的 `join`，我们自己定义一个——最简单的写法是用 bind 加上恒等函数：

```lean
def join [Monad m] (mma : m (m α)) : m α := mma >>= id

-- 它和核心库里 Option 专用的 join 是一回事
example (x : Option (Option Nat)) : join x = x.join := by cases x <;> rfl
```

（`cases x <;> rfl`：先对 `x` 分情况（`none` / `some _`），`<;>` 表示“对产生的**每个**子目标都执行后面的 tactic”。）

反过来，用 `join` 可以把 bind 重写为：

```lean no-check
ma >>= f = join (f <$> ma)
```

在任何合法单子中这都是一条定理（证明见章末补充小节的 `bind_eq_join_map`）。这引出了定义单子的第三种方案：

```lean
namespace JoinDef
class Monad (m : Type → Type) [Functor m] where
  join : {α : Type} → m (m α) → m α
  ret : {α : Type} → α → m α
end JoinDef
```

这里我们明确要求 `m` 是一个 `Functor`（方括号 `[Functor m]` 表示“需要一个 `Functor m` 实例”）。前两种单子定义里我们没有这样要求，这是因为任何支持鱼运算符或 bind 运算符的类型构造子都**自动**是一个函子。比如，`map` 可以用 bind 和 `return` 来定义：

```lean no-check
f <$> ma = ma >>= fun a => pure (f a)
```

在 Lean 里，这恰好是 `LawfulMonad` 的一个字段 `bind_pure_comp`——它要求你提供的 `map` 必须与“用 bind 定义出来的 map”一致：

```lean
example [Monad m] [LawfulMonad m] (f : α → β) (ma : m α) :
    (ma >>= fun a => pure (f a)) = f <$> ma :=
  bind_pure_comp f ma
```

为了完整起见，下面是 `Writer` 单子的 `join`：外层日志在前，内层日志在后，拼起来。

```lean
def Writer.join' [Monoid w] : Writer w (Writer w α) → Writer w α
  | ⟨(⟨(a, w')⟩, w)⟩ => ⟨(a, w <> w')⟩

-- 和通用的 join 定义上完全一致
example [Monoid w] (x : Writer w (Writer w α)) : join x = x.join' := rfl
```

把三种定义的关系画成一张图：对 Kleisli 箭头 `f : a → m b` 和 `g : b → m c`，鱼运算符 `f >=> g` 等于“先 `f`，再 `map g`，最后 `join`”。

```diagram
a: (0, 0)
mb: (2, 0) "m\ b"
mmc: (4, 0) "m\ (m\ c)"
mc: (4, 1.5) "m\ c"
f: a -> mb "f"
fg: mb -> mmc "\mathrm{map}\ g"
j: mmc -> mc "\mathrm{join}"
fish: a -> mc "f \mathbin{\texttt{>=>}} g" side=right pos=0.4 color=green
bnd: mb -> mc "\mathrm{bind}\ g" side=left pos=0.45 color=orange
path "f，map g，再 join": f fg j
path "f，再 bind g": f bnd color=orange
path "一步到位：鱼运算符": fish color=green
caption: 三种单子定义的关系：fish = bind 之后接上 f = 先 map 再 join。三条路径殊途同归。
```

## `do` 记法

使用单子写代码的一种方式是直接操作 Kleisli 箭头，用鱼运算符把它们复合起来。这种编程模式是无点风格的推广。无点代码紧凑，常常也很优雅；但一般来说它不太好懂，有时简直像密码。所以大多数程序员更喜欢给函数参数和中间值起名字。

具体到单子，这意味着更偏爱 bind 而非鱼运算符。bind 接受一个单子值，返回一个单子值，程序员可以给这些值起名字。但这几乎算不上改进。我们真正想要的，是**假装**自己在处理普通的值，而不是包着它们的单子容器。命令式代码就是这样工作的：副作用（比如往全局日志里追加一条）大多被藏在视线之外。而 `do` 记法模拟的正是这一点。

那你可能会问：既然如此，何必用单子呢？如果想让副作用不可见，为什么不干脆用命令式语言？答案是：单子让我们对副作用拥有**好得多的控制**。比如，`Writer` 单子里的日志是从一个函数传到下一个函数的，从来不会暴露成全局变量。日志不可能被搅乱，也不可能产生数据竞争。此外，单子代码有清晰的边界，被隔离在程序的其余部分之外——在 Lean 里，这条边界就写在类型上：看到返回类型 `Writer String α`，你就知道这个函数会写日志，并且**只会**写日志。

`do` 记法只是单子复合的语法糖。表面上它很像命令式代码，但它会被直接翻译成一串 bind 和 lambda 表达式。

举个例子，回想我们之前用来演示 `Writer` 单子中 Kleisli 箭头复合的那个例子。用现在的定义，它可以写成（注意这里的 `>=>` 是**Lean 核心库**的鱼运算符，它会自动使用我们上面给 `Writer` 写的 `Monad` 实例）：

```lean
def words (s : String) : List String := (s.splitOn " ").filter (· ≠ "")

def upCase (s : String) : Writer String String := ⟨(s.toUpper, "upCase ")⟩
def toWords (s : String) : Writer String (List String) := ⟨(words s, "toWords ")⟩

def process : String → Writer String (List String) := upCase >=> toWords

#guard (process "hello world").run == (["HELLO", "WORLD"], "upCase toWords ")
```

（Lean 核心库没有 Haskell 的 `words`，我们用 `splitOn " "` 按空格切开，再滤掉空串。）

这个函数把输入字符串里的字符全部转成大写，再拆分成单词，同时记录下自己做过的每一步。

用 `do` 记法，它是这样的：

```lean
def process₂ (s : String) : Writer String (List String) := do
  let upStr ← upCase s
  toWords upStr
```

这里 `upStr` 只是一个 `String`，尽管 `upCase` 产生的是一个 `Writer`。这是因为编译器会把这个 `do` 块**脱糖**（desugar）成：

```lean
def process₃ (s : String) : Writer String (List String) :=
  upCase s >>= fun upStr =>
    toWords upStr
```

`upCase` 的单子结果被绑定到一个接受 `String` 的 lambda 上，`do` 块里出现的，正是这个字符串参数的名字。读到这一行时：

```lean no-check
let upStr ← upCase s
```

我们说 `upStr` **取得**（gets）了 `upCase s` 的结果。（Haskell 写作 `upStr <- upCase s`；Lean 多了一个 `let`，箭头是 `←`，可以用 `\l` 或 `<-` 输入。）

口说无凭。在 Lean 里，我们可以让编译器亲自确认“`do` 块和手写的 bind 链是**同一个**东西”——不是“行为一样”，而是**定义上相等**，`rfl` 就能证明：

```lean
example : process₂ = process₃ := rfl
example : process = process₃ := rfl    -- 鱼运算符版本也一样！
```

如果把 `toWords` 内联，这种伪命令式风格就更明显了。我们把它换成对 `tell` 的调用（记录字符串 `"toWords "`），然后 `return` 用 `words` 切分 `upStr` 的结果。注意 `words` 是一个处理字符串的普通函数：

```lean
def process₄ (s : String) : Writer String (List String) := do
  let upStr ← upCase s
  tell "toWords "
  return words upStr

#guard (process₄ "hello world").run == (["HELLO", "WORLD"], "upCase toWords ")
```

这里，`do` 块的每一行都会在脱糖后的代码中引入一层新的嵌套 bind：

```lean
def process₅ (s : String) : Writer String (List String) :=
  upCase s >>= fun upStr =>
    tell "toWords " >>= fun () =>
      pure (words upStr)

example : process₄ = process₅ := rfl
```

注意 `tell` 产生的是一个单位值 `()`，所以没必要把它传给后面的 lambda（`fun () => …` 用模式 `()` 接住它，然后弃之不用）。忽略单子结果的**内容**——但不忽略它的**效应**，这里就是它对日志的贡献——是相当常见的需求，所以有一个专门的运算符来代替这种情况下的 bind。在 Haskell 里它叫 `>>`；在 Lean 里，对应的是 `*>`（`seqRight`）：

```lean no-check
x *> y   -- 运行 x，丢弃它的结果，再运行 y
-- 在合法单子中：x *> y = x >>= fun _ => y   （核心库定理 seqRight_eq_bind）
```

::: warning 易错点：Lean 的 `>>` 不是 Haskell 的 `>>`
在 Lean 4 里，`>>` 是 `HAndThen` 类的通用记号，**不是**单子的“丢弃结果再继续”。要表达 Haskell 的 `m >> k`，请写 `m *> k`，或者干脆在 `do` 块里写成两行。另外，Lean 的 `do` 并不会把“结果被丢弃的行”翻译成 `*>`，而是翻译成 `bind x (fun _ => …)`——用 `set_option pp.notation false` 再 `#check` 一个 `do` 块就能看到。
:::

于是，我们的代码也可以写成：

```lean
def process₆ (s : String) : Writer String (List String) :=
  upCase s >>= fun upStr =>
    tell "toWords " *>
      pure (words upStr)

-- 这一次不再是定义上相等，而要用到单子定律（seqRight_eq_bind 依赖 LawfulMonad）
theorem process₄_eq_process₆ : process₄ = process₆ := by
  funext s
  simp only [process₄, process₆, seqRight_eq_bind]
```

一般来说，`do` 块由若干行（或子块）组成：有的行用左箭头引入新名字，这些名字在后续代码中可用；有的行纯粹是为了副作用而执行。行与行之间隐含着 bind 运算符。顺带一提，在 Haskell 里可以用花括号和分号替代 `do` 块中的缩进排版；Lean 也一样，你可以写 `do let x ← a; b x; c`。这就为“单子是**重载分号**的一种方式”这个说法提供了依据。

```lean
example : (do let upStr ← upCase "a b"; tell "toWords "; return words upStr) = process₄ "a b" := rfl
```

还请注意，脱糖 `do` 记法时 lambda 和 bind 层层嵌套，其效果是：**每一行的结果都能影响 `do` 块其余部分的执行**。这个性质可以用来引入复杂的控制结构，比如模拟异常。（下一章的 `Option` 和 `Except` 单子正是这么做的：一旦某一行“失败”，bind 就根本不去调用后面的 lambda。）

下面这个组件把脱糖过程一步一步演示出来：每按一次“下一步”，就有一行 `do` 代码被改写成 `>>= fun x =>` 的形式，同色高亮标出对应关系。

<div class="ctfp-widget-host"><Ch3_4DoDesugar /></div>

有意思的是，`do` 记法的等价物已经在命令式语言里找到了用武之地，C++ 尤其如此。我说的是**可恢复函数**（resumable function），也就是协程。C++ 的 future [构成一个单子](https://bartoszmilewski.com/2014/02/26/c17-i-see-a-monad-in-your-future/)，这早已不是秘密；它是延续单子（continuation monad）的一个例子，我们很快就会讨论。延续的问题在于它们非常难以复合。在 Haskell 里，我们用 `do` 记法把“我的回调会调用你的回调”这种意大利面条，变成看上去非常像顺序代码的东西。可恢复函数让 C++ 也能做同样的变换。同样的机制还能把[层层嵌套的循环这碗面条](https://bartoszmilewski.com/2014/04/21/getting-lazy-with-c/)变成列表推导式或“生成器”，而它们本质上就是列表单子的 `do` 记法。没有单子这个统一的抽象，上面每个问题通常都要靠给语言打上专门的扩展来解决；而在 Haskell（以及 Lean）里，这一切都由库来处理。

::: tip Rust 视角：你每天都在写单子代码
Rust 没有 `Monad` trait（缺少高阶类型），但单子的“影子”无处不在：

- `Option::and_then` / `Result::and_then` **就是** bind：`x.and_then(f)` 对应 `x >>= f`。
- `?` 运算符是 `do` 记法的一个**特例**：它只能用于 `Option`/`Result`（以及实现了 `Try` 的类型），只支持一种效应——短路。`let x = e?;` 对应 Lean 的 `let x ← e`。
- `async`/`await` 是 `Future` 的 `do` 记法：`let x = fut.await;` 也对应 `let x ← fut`。编译器把 `async fn` 改写成状态机，这和 Haskell 把 `do` 改写成延续的嵌套，是同一个思想的两种实现。
- `Iterator::flat_map` 是列表单子的 bind（下一章细讲）。

```rust
// `?`：Option 的 do 记法
fn parse_and_add(a: &str, b: &str) -> Option<u32> {
    let x = a.parse::<u32>().ok()?;
    let y = b.parse::<u32>().ok()?;
    Some(x + y)
}

// 手动“脱糖”：一串嵌套的 and_then（也就是 bind）
fn parse_and_add_desugared(a: &str, b: &str) -> Option<u32> {
    a.parse::<u32>().ok().and_then(|x| {
        b.parse::<u32>().ok().and_then(|y| Some(x + y))
    })
}

// Option 的鱼运算符
pub fn fish<A, B, C>(
    f: impl Fn(A) -> Option<B>,
    g: impl Fn(B) -> Option<C>,
) -> impl Fn(A) -> Option<C> {
    move |a| f(a).and_then(&g)
}

// async/await：Future 的 do 记法
async fn fetch_len(url: String) -> usize { url.len() }
async fn total() -> usize {
    let a = fetch_len("a".to_string()).await;
    let b = fetch_len("bb".to_string()).await;
    a + b
}
```

同一个函数用 Lean 写：

```lean
def parseAndAdd (a b : String) : Option Nat := do
  let x ← a.toNat?
  let y ← b.toNat?
  return x + y

#guard parseAndAdd "12" "30" == some 42
#guard parseAndAdd "12" "abc" == none
```

区别在于：Rust 为每一种效应单独发明一套语法（`?`、`.await`、生成器……），Lean 的 `do` 则对**所有**单子一视同仁。
:::

## 补充：Lean 的 `do` 记法远不止 bind

Haskell 的 `do` 只有“绑定”和“顺序”两种语句。Lean 4 的 `do` 则是一门小型命令式语言：它有可变变量 `let mut`、`for` 循环、`if` 不带 `else`、提前 `return`、嵌套动作 `(← e)`……写起来几乎和 Rust 一样。但关键是：**它们统统会被脱糖成 bind**，所以仍然是纯函数，仍然服从单子定律。下面逐个拆开看，并且都用 `rfl` 或 `#guard` 让机器确认。

### 嵌套动作 `(← e)`

在表达式中间写 `(← e)`，意思是“先执行 `e`，把结果放在这儿”。Lean 会把它提到当前语句前面，变成一个 bind：

```lean
def addBoth (x y : Option Nat) : Option Nat := do
  return (← x) + (← y)

example (x y : Option Nat) :
    addBoth x y = (x >>= fun a => y >>= fun b => pure (a + b)) := rfl

#guard addBoth (some 2) (some 3) == some 5
#guard addBoth (some 2) none == none
```

### `return`：位于末尾时就是 `pure`

在 `do` 块的最后一行，`return e` 就是 `pure e`：

```lean
example : (do return 5 : Option Nat) = pure 5 := rfl
```

但 `return` 写在中间时，它的含义是**提前退出整个 `do` 块**——这正是 Haskell 的 `return` 常被诟病“名不副实”、而 Lean 把它做成了货真价实的关键字的原因。

### `if` 不带 `else`

`if c then act` 的缺省分支是 `pure ()`：

```lean
example (c : Bool) (x : Option Unit) :
    (do if c then x : Option Unit) = (if c then x else pure ()) := rfl
```

### `let mut` 与 `for`：脱糖为 `forIn`

可变变量并不是真的“可变”。Lean 把 `let mut` 变量当作循环状态，`for` 循环脱糖为核心库函数 `forIn`：它接受容器、初始状态和“循环体”，循环体返回 `ForInStep.yield 新状态`（继续）或 `ForInStep.done 新状态`（`break`）。

```lean
def sumSquares (xs : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in xs do
    acc := acc + x * x
  return acc

#guard sumSquares [1, 2, 3] == 14

-- 手动脱糖：可变变量 acc 变成了 forIn 的“状态参数”
example (xs : List Nat) :
    sumSquares xs = Id.run (forIn xs 0 fun x acc => pure (ForInStep.yield (acc + x * x))) := rfl

-- 再往前一步：在纯的 Id 单子里，这个循环就是 foldl
theorem sumSquares_eq (xs : List Nat) :
    sumSquares xs = xs.foldl (fun acc x => acc + x * x) 0 := by
  simp [sumSquares]
```

::: tip Lean 深入：`Id` 单子与 `Id.run`
`Id α` 就是 `α` 本身（`def Id (α) := α`），它是“什么效应都没有”的单子：`pure` 是恒等，`bind x f` 就是 `f x`。`Id.run do …` 的意思是“我只想用 `do` 的命令式语法写一段**纯**计算”。这一招在 Lean 里极其常用——你会发现自己用 `let mut` 和 `for` 写的代码，最后都被证明等于一个 `foldl`。
:::

### 提前 `return`

循环里的 `return` 会立即结束整个函数。Lean 的做法是：给循环状态多加一个 `Option` 槽位，`return v` 就是“把 `some v` 放进槽位，并用 `ForInStep.done` 跳出循环”，循环结束后再检查槽位：

```lean
def findFirst (p : Nat → Bool) (xs : List Nat) : Option Nat := Id.run do
  for x in xs do
    if p x then return some x
  return none

#guard findFirst (· > 10) [1, 20, 3, 40] == some 20
#guard findFirst (· > 100) [1, 20, 3, 40] == none
```

用 `#print findFirst` 可以看到编译器生成的代码（整理后）：

```lean no-check
def findFirst p xs := Id.run do
  let r ← forIn xs (none, ()) fun x _ =>
    if p x then pure (ForInStep.done (some (some x), ()))   -- 记下返回值并 break
    else pure (ForInStep.yield (none, ()))
  match r.1 with
  | some v => pure v       -- 循环中途 return 过
  | none   => pure none    -- 正常走完循环，执行后面的 return none
```

### 在“有效应”的单子里写循环

上面几例都在 `Id` 里。换成 `Option`，循环中的一行 `none` 就会让整个计算短路——这就是“用单子模拟异常”：

```lean
def safeDivAll (n : Nat) (ds : List Nat) : Option Nat := do
  let mut r := n
  for d in ds do
    if d == 0 then none     -- 失败：后面的 bind 都不会再被调用
    r := r / d
  return r

#guard safeDivAll 100 [2, 5] == some 10
#guard safeDivAll 100 [2, 0, 5] == none
```

这段代码读起来和 Rust 的

```rust no-check
let mut r = n;
for d in ds { if d == 0 { return None; } r /= d; }
Some(r)
```

几乎一样，但 Lean 版本里没有任何真正的可变状态：`r` 是 `forIn` 传递的状态，`none` 的短路来自 `Option` 的 bind。

## 补充：三种定义等价（用 Lean 证明）

原书只是说“定义单子有许多等价的方式”。在 Lean 里，我们可以把“等价”**证明**出来。下面分四步：

1. 从 bind 的定律推出鱼运算符的定律（因而任何合法单子都给出一个 Kleisli 范畴）；
2. 反过来，从鱼运算符的定律推出 bind 的定律；
3. 从 bind 的定律推出 `join` 的定律；
4. 反过来，从 `join` 的定律推出 bind 的定律。

### 第一步：`LawfulMonad` ⟹ Kleisli 定律，并得到真正的 Kleisli 范畴

```lean
section
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem kleisli_id_left (f : α → m β) : (pure >=> f) = f := by
  funext a; simp [Bind.kleisliRight]           -- 用 pure_bind

theorem kleisli_id_right (f : α → m β) : (f >=> pure) = f := by
  funext a; simp [Bind.kleisliRight]           -- 用 bind_pure

theorem kleisli_assoc (f : α → m β) (g : β → m γ) (h : γ → m δ) :
    ((f >=> g) >=> h) = (f >=> (g >=> h)) := by
  funext a; simp only [Bind.kleisliRight, bind_assoc]; rfl   -- 用 bind_assoc
end
```

有了这三条，我们就能用全书统一的 `CTFP.Category` 类，为**任何**合法单子构造出它的 Kleisli 范畴——对象是类型（用 `Kl m` 包一层，以免和 **Type** 范畴的实例混淆），从 `a` 到 `b` 的态射是 `a → m b`：

```lean
structure Kl (m : Type → Type) where
  of :: obj : Type

instance kleisliCat (m : Type → Type) [Monad m] [LawfulMonad m] : Category (Kl m) where
  Hom a b := a.obj → m b.obj
  id _ := pure
  comp g f := f >=> g                 -- g ⊚ f：先 f 后 g
  id_comp f := kleisli_id_right f
  comp_id f := kleisli_id_left f
  assoc f g h := kleisli_assoc f g h
```

这就是本节开头那句话的形式化：“如果存在一种满足结合律、并有恒等箭头的复合，那么 $m$ 就是单子，得到的范畴就是 Kleisli 范畴”。

### 第二步：Kleisli 定律 ⟹ bind 定律

现在反过来：假设有人只给了我们鱼运算符和 `ret`，以及 Kleisli 形式的三条定律。我们用鱼来**定义** bind：把单子值 `ma` 看成一个“忽略 `Unit` 参数”的 Kleisli 箭头 `fun () => ma`，和 `f` 复合，再喂进 `()`。

这里有个微妙之处值得一提。光有三条范畴定律还不够，我们还需要一条看起来“理所当然”的性质 `fish_pre`：先用普通函数 `k` 预处理输入，再做 Kleisli 复合，等于先复合再预处理。在 Haskell 里，这条性质由**参数性**（parametricity）免费保证——一个对 `α` 完全多态的函数，只能把 `α` 原样传来传去，没法“偷看”它。但 Lean 不会自动把这种“免费定理”交给你，所以我们把它作为一条定律写进类里。

```lean
namespace FromFish
class KMonad (m : Type → Type) where
  fish : {α β γ : Type} → (α → m β) → (β → m γ) → (α → m γ)
  ret : {α : Type} → α → m α
  ret_fish : ∀ {α β} (f : α → m β), fish ret f = f
  fish_ret : ∀ {α β} (f : α → m β), fish f ret = f
  fish_assoc : ∀ {α β γ δ} (f : α → m β) (g : β → m γ) (h : γ → m δ),
    fish (fish f g) h = fish f (fish g h)
  -- 参数性给出的“免费定理”：鱼运算符与预处理输入可交换
  fish_pre : ∀ {α' α β γ} (k : α' → α) (p : α → m β) (f : β → m γ),
    fish (p ∘ k) f = fish p f ∘ k

variable {m : Type → Type} [KMonad m]
open KMonad

def bind' (ma : m α) (f : α → m β) : m β := fish (fun (_ : Unit) => ma) f ()

theorem fish_apply (p : α → m β) (f : β → m γ) (a : α) :
    fish (fun (_ : Unit) => p a) f () = fish p f a :=
  congrFun (fish_pre (fun (_ : Unit) => a) p f) ()

theorem fish_const (q : Unit → m β) (f : β → m γ) :
    (fun (_ : Unit) => fish q f ()) = fish q f := by
  funext u; cases u; rfl              -- Unit 只有一个值 ()

theorem pure_bind' (a : α) (f : α → m β) : bind' (ret a) f = f a := by
  rw [bind', fish_apply, ret_fish]

theorem bind_pure' (ma : m α) : bind' ma ret = ma := by
  rw [bind', fish_ret]

theorem bind_assoc' (ma : m α) (f : α → m β) (g : β → m γ) :
    bind' (bind' ma f) g = bind' ma (fun a => bind' (f a) g) := by
  simp only [bind']
  rw [fish_const, fish_assoc]         -- 化归为鱼运算符的结合律
  congr 1
  funext a
  exact (fish_apply f g a).symm
end FromFish
```

（`congrFun h x`：由函数相等 `h : F = G` 得到 `F x = G x`；`congr 1`：要证 `F a = F b`，化为证 `a = b`；`.symm` 把等式两边对调。）

### 第三步：`LawfulMonad` ⟹ `join` 定律

用 `join` 表述时，单子定律长成这样（$\eta$ 是 `pure`，$\mu$ 是 `join`）：

- 左单位律：`join (pure x) = x`，即 $\mu \circ \eta_{m} = \mathrm{id}$；
- 右单位律：`join (pure <$> x) = x`，即 $\mu \circ m\,\eta = \mathrm{id}$；
- 结合律：`join (join x) = join (join <$> x)`，即 $\mu \circ \mu_{m} = \mu \circ m\,\mu$。

再加上两条“自然性”：`pure` 和 `join` 都与 `map` 可交换（下一章之后你会认出它们是**自然变换**的自然性条件）。

```lean
section
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem join_pure (x : m α) : join (pure x) = x := by simp [join]
theorem join_map_pure (x : m α) : join (pure <$> x) = x := by simp [join]
theorem join_join (x : m (m (m α))) : join (join x) = join (join <$> x) := by
  simp [join, bind_assoc]

theorem pure_natural (f : α → β) (x : α) : f <$> (pure x : m α) = pure (f x) := map_pure f x
theorem join_natural (f : α → β) (x : m (m α)) : f <$> join x = join ((f <$> ·) <$> x) := by
  simp [join]

-- bind 可以用 map 和 join 表达
theorem bind_eq_join_map (x : m α) (f : α → m β) : x >>= f = join (f <$> x) := by
  simp [join]
end
```

结合律和单位律画成交换图，就是下面两张。点按钮看两条路径殊途同归：

```diagram
mmm: (0, 0) "m\,(m\,(m\,a))"
mm1: (3, 0) "m\,(m\,a)"
mm2: (0, 1.6) "m\,(m\,a)"
ma: (3, 1.6) "m\,a"
top: mmm -> mm1 "\mathrm{map}\ \mathrm{join}"
left: mmm -> mm2 "\mathrm{join}" side=right
right: mm1 -> ma "\mathrm{join}"
bottom: mm2 -> ma "\mathrm{join}" side=right
path "先压内层两层": top right
path "先压外层两层": left bottom color=green
caption: join 的结合律：三层 m 无论先压哪两层，结果都一样。
```

```diagram
ma1: (0, 0) "m\,a"
mma: (2, 0) "m\,(m\,a)"
ma2: (4, 0) "m\,a"
ma: (2, 1.5) "m\,a"
l: ma1 -> mma "\mathrm{pure}"
r: ma2 -> mma "\mathrm{map}\ \mathrm{pure}" side=right
jj: mma -> ma "\mathrm{join}"
idl: ma1 -> ma "\mathrm{id}" side=right color=gray
idr: ma2 -> ma "\mathrm{id}" color=gray
path "左：pure 再 join": l jj
path "左：什么都不做": idl color=gray
path "右：map pure 再 join": r jj color=green
path "右：什么都不做": idr color=gray
caption: join 的两条单位律：在外面或里面包一层 pure，再 join 掉，等于什么都没做。
```

### 第四步：`join` 定律 ⟹ bind 定律

最后，假设有人只给了我们 `map`（满足函子定律）、`join`、`ret` 以及上面那些定律，用 `bindJ x f := join (f <$> x)` 定义 bind，三条 bind 定律都成立。结合律的证明用 `calc` 写成一串等式链，每一步注明理由：

```lean
namespace FromJoin
class JMonad (m : Type → Type) [Functor m] where
  join : m (m α) → m α
  ret : α → m α
  join_ret : ∀ {α} (x : m α), join (ret x) = x
  join_map_ret : ∀ {α} (x : m α), join (ret <$> x) = x
  join_join : ∀ {α} (x : m (m (m α))), join (join x) = join (join <$> x)
  ret_natural : ∀ {α β} (f : α → β) (x : α), f <$> ret x = ret (f x)
  join_natural : ∀ {α β} (f : α → β) (x : m (m α)), f <$> join x = join ((f <$> ·) <$> x)

variable {m : Type → Type} [Functor m] [JMonad m]
open JMonad (ret ret_natural join_ret join_map_ret)

def bindJ (x : m α) (f : α → m β) : m β := JMonad.join (f <$> x)

theorem ret_bindJ (a : α) (f : α → m β) : bindJ (ret a) f = f a := by
  simp [bindJ, ret_natural, join_ret]

theorem bindJ_ret (x : m α) : bindJ x ret = x := join_map_ret x

theorem bindJ_assoc [LawfulFunctor m] (x : m α) (f : α → m β) (g : β → m γ) :
    bindJ (bindJ x f) g = bindJ x (fun a => bindJ (f a) g) := by
  simp only [bindJ]
  calc JMonad.join (g <$> JMonad.join (f <$> x))
      = JMonad.join (JMonad.join ((g <$> ·) <$> (f <$> x)))   := by rw [JMonad.join_natural]
    _ = JMonad.join (JMonad.join (((g <$> ·) ∘ f) <$> x))     := by rw [Functor.map_map]; rfl
    _ = JMonad.join (JMonad.join <$> (((g <$> ·) ∘ f) <$> x)) := by rw [JMonad.join_join]
    _ = JMonad.join ((JMonad.join ∘ (g <$> ·) ∘ f) <$> x)     := by rw [Functor.map_map]; rfl
end FromJoin
```

::: tip Lean 深入：`calc`
`calc a = b := 证明₁; _ = c := 证明₂; …` 把一条等式链串起来，最后得到 `a = c`。每一步的 `_` 代表上一步的右边。这几乎就是数学课本上“连等号推导”的原样搬运，是写可读证明的利器。这里用到了 `Functor.map_map`（函子定律：`g <$> f <$> x = (g ∘ f) <$> x`），它来自 `LawfulFunctor`。
:::

四步合起来，就严格地说明了：**鱼运算符、bind、join 三种定义方式在定律层面是等价的**。你可以选择最顺手的那个来定义单子，其余两个连同它们的定律一并免费得到。

## 练习（本书补充）

原书本章没有挑战题。下面几道练习帮助你巩固本章内容。

1. 不借助 `LawfulMonad`，直接对 `Writer` 证明 `join` 形式的右单位律：`Writer.join' (pure <$> x) = x`。
2. 对 `Option`，手写一个鱼运算符 `optFish`（用 `match`，不用 `>>=`），并证明它和核心库的 `>=>` 相等。
3. 把下面的 `do` 块手动脱糖成 bind 链，并用 `rfl` 验证：

```lean no-check
def ex3 (x y : Option Nat) : Option Nat := do
  let a ← x
  let b ← y
  if a < b then none
  return a - b
```

::: details 参考答案
```lean
-- 1
theorem writer_join_map_pure [Monoid w] (x : Writer w α) :
    Writer.join' ((pure : α → Writer w α) <$> x) = x := by
  rcases x with ⟨a, s⟩
  show (⟨(a, s <> mempty)⟩ : Writer w α) = ⟨(a, s)⟩
  rw [Monoid.mappend_mempty]

-- 2
def optFish (f : α → Option β) (g : β → Option γ) : α → Option γ := fun a =>
  match f a with
  | none => none
  | some b => g b

theorem optFish_eq (f : α → Option β) (g : β → Option γ) : optFish f g = (f >=> g) := by
  funext a
  simp only [optFish, Bind.kleisliRight]
  cases f a <;> rfl

-- 3
def ex3 (x y : Option Nat) : Option Nat := do
  let a ← x
  let b ← y
  if a < b then none
  return a - b

-- 最“朴素”的脱糖：if 语句整体是一个 Option Unit，再 bind 后面的代码
def ex3' (x y : Option Nat) : Option Nat :=
  x >>= fun a =>
    y >>= fun b =>
      (if a < b then none else pure ()) >>= fun () =>
        pure (a - b)

-- Lean 实际的脱糖：把“if 之后的代码”打包成一个汇合点（join point）jp，
-- 再把 bind 推进 if 的两个分支里。这样就能定义上相等：
def ex3'' (x y : Option Nat) : Option Nat :=
  x >>= fun a =>
    y >>= fun b =>
      let jp := fun (_ : Unit) => pure (a - b)
      if a < b then none >>= fun r => jp r else jp ()

example : ex3 = ex3'' := rfl

-- 朴素版本只是命题上相等：需要对 a < b 分情况
theorem ex3_eq : ex3 = ex3' := by
  funext x y
  simp only [ex3, ex3']
  congr; funext a; congr; funext b
  by_cases h : a < b <;> simp [h]

#guard ex3 (some 5) (some 3) == some 2
#guard ex3 (some 3) (some 5) == none
```

第 3 题很有启发性：用 `set_option pp.notation false` 再 `#print ex3`，你会看到 Lean 的 `do` 展开器生成了一个叫 `__do_jp` 的局部函数。这就是编译器术语里的**汇合点**（join point）：`if` 的两个分支都要“接着执行后面的代码”，编译器不复制这段代码，而是把它包成函数，让两个分支都去调用。从语义上看，这和朴素的脱糖等价（`ex3_eq` 证明了这一点），只是“定义上相等”变成了“命题上相等”。
:::

## 本章小结

- 单子不神秘：它就是**复合修饰函数**（Kleisli 箭头 `a → m b`）的一种方式，像布基胶带一样把东西粘起来。
- Kleisli 范畴：对象同原范畴，从 $a$ 到 $b$ 的态射是 $a \to m\,b$。复合满足结合律、有恒等箭头，$m$ 就是单子。
- 定义单子有三种等价方式：鱼运算符 `>=>` + `pure`；bind `>>=` + `pure`（Lean 和 Haskell 的标准做法）；`join` + `pure` + `map`。我们在 Lean 中证明了三者的定律可以互推。
- Lean 核心库有 `>=>`（`Bind.kleisliRight`）、`<=<`、`=<<`，但没有通用的 `join`/`joinM`；`return` 对应 `pure`，Haskell 的 `>>` 对应 `*>`。
- `LawfulMonad` 把单子定律写进了类型类；为 Writer 提供实例就是给出证明，而 Writer 的定律恰好来自幺半群的定律。
- `do` 记法只是语法糖：每一行都脱糖为一层嵌套的 `>>= fun x =>`，可以用 `rfl` 验证它和手写的 bind 链定义上相等。
- Lean 的 `do` 还支持 `(← e)`、`let mut`、`for`、提前 `return`，它们都被翻译成 bind 和 `forIn`，因此仍然是纯函数。
- Rust 的 `and_then` 是 bind，`?` 和 `.await` 是针对特定单子的 `do` 记法；Lean 的 `do` 则对所有单子通用。
