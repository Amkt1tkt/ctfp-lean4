# 0.2 数学工具箱：读这本书需要的全部数学

::: tip 关于本章
本章是中文 Lean 4 版**新增**的导读，原书没有对应章节。原书假定读者对集合、函数、关系、同构这些概念已经熟悉，
而这正是许多程序员（尤其是离开学校很久的程序员）卡住的地方。本章把全书用到的数学从头讲一遍。
:::

范畴论常被称为“数学的数学”，听起来好像需要先学完大半个数学系的课程。其实不然。读这本书，你只需要下面这一小撮概念，
而且它们都很朴素：集合、函数、关系、一点逻辑、一点代数。真正的难点不在于概念多，而在于**习惯数学家说话的方式**：
“对所有……存在唯一的……使得……”。本章的另一个目标就是帮你练出这种阅读能力。

每个概念都按同样的顺序讲：

1. **直觉**：它大概是什么意思；
2. **例子**：几个具体的小例子（以及反例）；
3. **精确定义**：数学家会怎么写；
4. **Lean 中的表达**：一小段能编译的 Lean 代码，把定义和例子变成机器检查过的东西；
5. **本书何处用到**：链接到相应章节。

你不必一口气读完。可以先读 §1 ~ §4（集合与函数），然后直接开始第一章；以后正文里遇到“偏序”“同构”“唯一存在”时再回来查。
如果 Lean 代码看不懂，请先看 [0.1 Lean 4 速成](/guide/lean-for-rustaceans)。

| 概念 | 本章 | 主要用于 |
|---|---|---|
| 集合、元素、子集 | §1、§2 | [1.2 类型与函数](/part1/02-types-and-functions)、[1.3 大大小小的范畴](/part1/03-categories-great-and-small) |
| 笛卡尔积、不交并 | §3 | [1.5 积与余积](/part1/05-products-and-coproducts)、[1.6 简单代数数据类型](/part1/06-simple-algebraic-data-types) |
| 函数、复合、恒等 | §4 | [1.1 范畴](/part1/01-category) 起的每一章 |
| 单射、满射、双射、反函数 | §4 | [1.5](/part1/05-products-and-coproducts)、[2.6 米田嵌入](/part2/06-yoneda-embedding)、[3.13 拓扑斯](/part3/13-topoi) |
| 等价关系、偏序、全序 | §5 | [1.3](/part1/03-categories-great-and-small)、[3.10 端与余端](/part3/10-ends-and-coends) |
| 同构、“在同构意义下” | §6 | [1.5](/part1/05-products-and-coproducts)、[1.6](/part1/06-simple-algebraic-data-types)、[3.2 伴随](/part3/02-adjunctions) |
| 计数：$\lvert B \rvert^{\lvert A \rvert}$ | §7 | [1.6](/part1/06-simple-algebraic-data-types)、[1.9 函数类型](/part1/09-function-types) |
| 逻辑与量词 | §8 | 处处 |
| 证明方法（含归纳法） | §9 | [2.3 自由幺半群](/part2/03-free-monoids)、[3.8 F-代数](/part3/08-f-algebras) |
| 幺半群与群 | §10 | [1.3](/part1/03-categories-great-and-small)、[1.4 Kleisli 范畴](/part1/04-kleisli-categories)、[2.3](/part2/03-free-monoids)、[3.15](/part3/15-monads-monoids-and-categories) |
| 唯一存在 | §11 | [1.5](/part1/05-products-and-coproducts)、[2.2 极限与余极限](/part2/02-limits-and-colimits) |
| 交换图 | §12 | [1.1](/part1/01-category)、[1.10 自然变换](/part1/10-natural-transformations) 及以后各章 |

## 1 集合与元素

#### 直觉

**集合**（set）就是“一堆东西”，这些东西叫它的**元素**（element）。集合只关心“谁在里面”，不关心顺序，也不关心重复：
$\{1, 2, 3\}$、$\{3, 1, 2\}$、$\{1, 1, 2, 3\}$ 是同一个集合。

你可以把集合想象成一个**不带顺序、自动去重**的容器，类似 Rust 的 `HashSet`；但数学里的集合可以是无穷的，
比如所有自然数组成的集合。

#### 例子

- $\{0, 1\}$：两个元素的集合。
- $\{\text{红}, \text{绿}, \text{蓝}\}$：三个元素的集合。元素可以是任何东西。
- $\mathbb{N} = \{0, 1, 2, 3, \dots\}$：自然数集合，无穷多个元素。
- $\varnothing = \{\}$：**空集**，没有任何元素。空集只有一个（任意两个空集的元素都相同，所以它们相等）。
- $\{\varnothing\}$：只有一个元素的集合，这个元素恰好是空集。它**不是**空集，就像“一个空盒子”不等于“没有盒子”。
- $\{n \in \mathbb{N} \mid n \text{ 是偶数}\} = \{0, 2, 4, \dots\}$：用条件描述的集合，读作“所有满足‘n 是偶数’的自然数 n 组成的集合”。
  竖线 $\mid$ 读作“使得”。

#### 精确定义

- $x \in A$ 读作“$x$ 属于 $A$”或“$x$ 是 $A$ 的元素”；$x \notin A$ 读作“$x$ 不属于 $A$”。
- **外延性**（extensionality）：两个集合相等，当且仅当它们有完全相同的元素。即 $A = B$ 当且仅当对所有 $x$，$x \in A \Leftrightarrow x \in B$。

（“集合到底是什么”在数学基础里是个深刻的问题，本书用不到。我们只需要会用它。）

#### Lean 中的表达

Lean 里与“集合”最接近的东西有两个。

**第一，类型本身就像一个集合**。`Bool` 像集合 $\{\mathtt{true}, \mathtt{false}\}$，`Nat` 像 $\mathbb{N}$，`Empty` 像 $\varnothing$，`Unit` 像单元素集合。
`x : Bool` 就相当于 $x \in \mathtt{Bool}$。区别在于，Lean 中每个值都只属于**一个**类型，不同类型的值不能混在一起。
原书[第 1.2 章](/part1/02-types-and-functions)正是从“类型就是值的集合”这一观点出发的。

**第二，一个类型的子集可以用“谓词”表示**：一个从 `α` 到 `Prop` 的函数，告诉你每个元素是否在集合里。
（Mathlib 把它叫 `Set α`；本书只用核心库，所以自己定义一个。）

```lean
/-- α 的一个子集：对每个 x 给出命题“x 在集合里”。 -/
def MySet (α : Type) : Type := α → Prop

/-- 让 `x ∈ A` 这个记号可用：`x ∈ A` 的意思就是 `A x`。 -/
instance {α : Type} : Membership α (MySet α) := ⟨fun A x => A x⟩

def evens : MySet Nat := fun n => n % 2 = 0       -- {n ∈ ℕ | n 是偶数}
def emptySet {α : Type} : MySet α := fun _ => False   -- 空集：谁都不在里面
def univ {α : Type} : MySet α := fun _ => True       -- 全集：谁都在里面

example : 4 ∈ evens := rfl          -- 4 % 2 = 0，算一下就成立

example : 3 ∉ evens := by
  intro h                 -- 假设 3 ∈ evens
  change 3 % 2 = 0 at h   -- 把 h 展开成它的定义
  simp at h               -- 3 % 2 = 1，所以 h 是假的，矛盾

example (x : Nat) : x ∉ (emptySet : MySet Nat) := fun h => h
```

最后一行：`x ∈ emptySet` 按定义就是 `False`，而 `x ∉ emptySet` 是 `x ∈ emptySet → False`，也就是 `False → False`，
恒等函数 `fun h => h` 就是证明。

::: warning 易错点：“所有集合组成的集合”
你可能会想：能不能有一个包含所有集合的集合？不行，这会导致罗素悖论。这和 Lean 中 `Type` 不能属于 `Type`
（而是属于 `Type 1`）是同一个原因，见 [0.1 §13](/guide/lean-for-rustaceans#_13-宇宙-type、type-u、sort、prop)。
范畴论里经常说“所有集合组成的范畴 $\mathbf{Set}$”，这时数学家会小心地区分“小”和“大”，本书在[第 1.3 章](/part1/03-categories-great-and-small)等处会提到。
:::

**本书何处用到**：[1.2](/part1/02-types-and-functions)（类型作为集合）、[1.3](/part1/03-categories-great-and-small)（集合范畴 $\mathbf{Set}$）、
以及每一处“hom-集”（两个对象之间所有态射组成的集合）。

## 2 子集

#### 直觉

如果 $A$ 的每个元素都在 $B$ 里，就说 $A$ 是 $B$ 的**子集**（subset），记作 $A \subseteq B$。想象 $A$ 这个圈完全画在 $B$ 这个圈里面。

#### 例子

- $\{1, 2\} \subseteq \{1, 2, 3\}$。
- “4 的倍数” $\subseteq$ “偶数” $\subseteq \mathbb{N}$。
- 任何集合都是自己的子集：$A \subseteq A$。
- 空集是任何集合的子集：$\varnothing \subseteq A$。（要检查“$\varnothing$ 的每个元素都在 $A$ 里”，而 $\varnothing$ 根本没有元素，所以无需检查任何东西，命题自动成立。这叫**空真**，vacuous truth，§8 还会遇到。）
- $\{1, 4\} \not\subseteq \{1, 2, 3\}$，因为 4 不在右边。

一个集合的所有子集组成的集合叫它的**幂集**（power set），记作 $\mathcal{P}(A)$。例如 $\mathcal{P}(\{1, 2\}) = \{\varnothing, \{1\}, \{2\}, \{1, 2\}\}$。
如果 $A$ 有 $n$ 个元素，它的幂集有 $2^n$ 个元素：每个元素都可以选择“在”或“不在”子集里，两种选择，$n$ 个元素就是 $2^n$ 种。

#### 精确定义

$A \subseteq B$ 当且仅当：对所有 $x$，若 $x \in A$，则 $x \in B$。

常用事实：$A = B$ 当且仅当 $A \subseteq B$ 且 $B \subseteq A$（“双向包含”）。证明两个集合相等时，经常分别证明这两个方向。

#### Lean 中的表达

```lean
def MySubset {α : Type} (A B : MySet α) : Prop := ∀ x, x ∈ A → x ∈ B

instance {α : Type} : HasSubset (MySet α) := ⟨MySubset⟩   -- 让 A ⊆ B 可用（输入 \sub）

def mult4 : MySet Nat := fun n => n % 4 = 0

example : mult4 ⊆ evens := by
  intro x h                     -- 任取 x，假设 x ∈ mult4
  have h4 : x % 4 = 0 := h      -- 也就是 x % 4 = 0
  show x % 2 = 0                -- 要证 x ∈ evens，也就是 x % 2 = 0
  omega                         -- 线性算术：4 的倍数一定是 2 的倍数

theorem subset_refl {α : Type} (A : MySet α) : A ⊆ A :=
  fun _ h => h

theorem subset_trans {α : Type} {A B C : MySet α} (hab : A ⊆ B) (hbc : B ⊆ C) : A ⊆ C :=
  fun x h => hbc x (hab x h)

theorem empty_subset {α : Type} (A : MySet α) : emptySet ⊆ A :=
  fun _ h => nomatch h          -- h : False，没有任何情况需要处理
```

注意 `subset_refl` 和 `subset_trans`：“包含”关系是自反的、传递的。§5 会看到，这意味着子集关系是一个**偏序**，
从而（[第 1.3 章](/part1/03-categories-great-and-small)）构成一个范畴。

幂集在 Lean 中就是 `MySet α` 本身，即 `α → Prop`。如果只看有限、可计算的情况，可以用 `α → Bool`：一个子集就是给每个元素回答“在”或“不在”。
`Bool → Bool` 恰好有 $2^2 = 4$ 个，§7 会证明这一点。

**本书何处用到**：[1.3](/part1/03-categories-great-and-small)（以包含关系为态射的范畴）、[3.13 拓扑斯](/part3/13-topoi)（子对象与子对象分类子，幂集的推广）。

## 3 笛卡尔积与不交并

#### 直觉

**笛卡尔积**（Cartesian product）$A \times B$ 是所有“有序对” $(a, b)$ 组成的集合，其中 $a \in A$，$b \in B$。
想象一个表格：行是 $A$ 的元素，列是 $B$ 的元素，每个格子就是一个有序对。

**不交并**（disjoint union，也叫和）$A + B$ 是把 $A$ 和 $B$ 的元素“贴上标签”放在一起：来自 $A$ 的元素贴“左”，来自 $B$ 的贴“右”。
即使 $A$ 和 $B$ 有相同的元素，贴了标签后也不会混在一起。

#### 例子

- $\{1, 2\} \times \{x, y, z\} = \{(1,x), (1,y), (1,z), (2,x), (2,y), (2,z)\}$，共 $2 \times 3 = 6$ 个。
- 有序对是**有序**的：$(1, x) \neq (x, 1)$（后者甚至不在这个集合里）。
- 平面上的点就是 $\mathbb{R} \times \mathbb{R}$。
- $\{1, 2\} + \{2, 3\} = \{\text{左}\,1, \text{左}\,2, \text{右}\,2, \text{右}\,3\}$，共 $2 + 2 = 4$ 个元素。
  注意“左 2”和“右 2”是不同的元素；而普通的并集 $\{1, 2\} \cup \{2, 3\} = \{1, 2, 3\}$ 只有 3 个。不交并的大小永远是两者之和。

#### 精确定义

- $A \times B = \{(a, b) \mid a \in A, b \in B\}$。两个有序对相等，当且仅当对应分量分别相等：$(a, b) = (a', b')$ 当且仅当 $a = a'$ 且 $b = b'$。
- $A + B = \{(\text{左}, a) \mid a \in A\} \cup \{(\text{右}, b) \mid b \in B\}$。
- 若 $A$、$B$ 有限，则 $|A \times B| = |A| \cdot |B|$，$|A + B| = |A| + |B|$（$|A|$ 表示 $A$ 的元素个数，§7）。

#### Lean 中的表达

积就是 `α × β`（Rust 的元组 `(A, B)`），不交并就是 `α ⊕ β`（Rust 的 `enum Either<A, B> { Left(A), Right(B) }`）：

```lean
def pairs : List (Nat × Char) := [(1, 'x'), (1, 'y'), (2, 'x')]

#guard (1, 'x').1 == 1
#guard (1, 'x').2 == 'x'

-- 有序对相等 ⟺ 分量分别相等
example (a a' : Nat) (b b' : Bool) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := by
  simp

-- 不交并：同一个 2，贴上不同标签就是不同元素
def left2 : Nat ⊕ Nat := Sum.inl 2
def right2 : Nat ⊕ Nat := Sum.inr 2

example : left2 ≠ right2 := by
  intro h
  cases h                 -- inl 2 = inr 2 不可能：不同构造子的值永远不相等
```

最后一个证明值得体会：`cases h` 对等式 `Sum.inl 2 = Sum.inr 2` 做分情况讨论，Lean 发现两个不同的构造子不可能相等，
于是一种情况都不剩，证明完成。

**本书何处用到**：[1.5 积与余积](/part1/05-products-and-coproducts)（积与不交并的范畴论定义）、[1.6 简单代数数据类型](/part1/06-simple-algebraic-data-types)
（为什么叫“积类型”和“和类型”）。

## 4 函数

函数是本书的绝对主角：范畴论的“箭头”（态射）就是对函数的抽象。这一节最长，值得慢慢读。

### 4.1 定义域、陪域、良定义

#### 直觉

一个**函数**（function）$f \colon A \to B$ 是一种“分配方案”：给 $A$ 中的**每一个**元素，分配 $B$ 中的**恰好一个**元素。
$A$ 叫**定义域**（domain），$B$ 叫**陪域**（codomain）。$a$ 被分配到的元素记作 $f(a)$，读作“$f$ 在 $a$ 处的值”。

画成图：左边一列点是 $A$，右边一列点是 $B$，从每个左边的点**恰好**引出一条箭头指向右边。

```diagram
a1: (0, 0) "1" shape=dot
a2: (0, 0.7) "2" shape=dot
a3: (0, 1.4) "3" shape=dot
b1: (2.2, 0.35) "x" shape=dot
b2: (2.2, 1.05) "y" shape=dot
e1: a1 -> b1 ""
e2: a2 -> b1 ""
e3: a3 -> b2 ""
caption: 一个函数 f : {1, 2, 3} → {x, y}：f(1) = x，f(2) = x，f(3) = y。两个元素映到同一处是允许的。
```

#### 例子与反例

- $f(n) = n + 1$，$f \colon \mathbb{N} \to \mathbb{N}$。
- “每个人的生日”：人 $\to$ 日期。很多人可以同一天生日，但每个人恰好一个生日。
- **不是函数**：某个元素引出了**两条**箭头（“2 映到 x 也映到 y”）。函数的输出必须是唯一的。
- **不是函数**（从 $A$ 出发的）：某个元素**没有**箭头。函数必须对**每个**输入都有定义。
- 陪域里可以有“没人指向”的元素（上图的 $B$ 如果再加一个 $z$，仍然是函数）。

满足“每个元素恰好一条箭头”这个要求，称为**良定义**（well-defined）。本节末尾的交互组件会帮你检查这一点。

#### 精确定义

函数 $f \colon A \to B$ 是一条规则，它对每个 $a \in A$ 给出唯一的 $f(a) \in B$。
（形式上，可以把它定义为 $A \times B$ 的一个子集，即“图像”$\{(a, f(a))\}$，要求每个 $a$ 恰好出现在一个有序对里。）

两个函数 $f, g \colon A \to B$ 相等，当且仅当它们对每个输入给出相同的输出：对所有 $a$，$f(a) = g(a)$。
这叫**函数外延性**（function extensionality），Lean 中对应 `funext`。

#### Lean 中的表达

在 Lean 中，类型为 `α → β` 的东西**自动**是良定义的函数：Lean 的函数必须对每个输入给出结果（全函数），而且是纯的，
同样的输入永远得到同样的输出。

```lean
def f : Fin 3 → Char
  | 0 => 'x'
  | 1 => 'x'
  | 2 => 'y'

#guard f 0 == 'x' && f 2 == 'y'
```

`Fin 3` 是核心库中“恰好有 3 个元素 $\{0, 1, 2\}$ 的类型”，用来表示小的有限集合非常方便。

::: tip Rust 视角
Rust 的 `fn(A) -> B` 并不总是数学函数：它可能 `panic!`、可能死循环（没有对每个输入给出结果），也可能读取全局状态或随机数
（同样的输入给出不同结果）。Lean 的 `α → β` 排除了这些情况，这正是[第 1.2 章](/part1/02-types-and-functions)强调“纯函数”的原因。
:::

### 4.2 像

#### 直觉、例子、定义

函数 $f \colon A \to B$ 的**像**（image）是所有“实际被指到的”输出组成的集合：$f(A) = \{f(a) \mid a \in A\} \subseteq B$。
它总是陪域的子集，但不一定是整个陪域。

例如 $\mathrm{sq}(n) = n^2$，$\mathrm{sq} \colon \mathbb{N} \to \mathbb{N}$，它的像是 $\{0, 1, 4, 9, 16, \dots\}$，不是整个 $\mathbb{N}$。
同样可以对子集求像：$\mathrm{sq}(\text{偶数}) = \{0, 4, 16, 36, \dots\}$。

#### Lean 中的表达

```lean
/-- 子集 A 在 f 下的像：b 在像里，当且仅当存在 A 中的 a 使得 f a = b。 -/
def image {α β : Type} (g : α → β) (A : MySet α) : MySet β :=
  fun b => ∃ a, a ∈ A ∧ g a = b

example : 16 ∈ image (fun n => n * n) evens :=
  ⟨4, rfl, rfl⟩     -- 见证者 4：4 是偶数，并且 4 * 4 = 16
```

要证明“16 在像里”，按定义就是要给出一个 $a$（这里是 4），并证明 $a \in$ 偶数、$a \cdot a = 16$。
这是“存在”的典型证明方式：**把它找出来**（§9）。

### 4.3 单射、满射、双射

#### 直觉

看函数的箭头图，有两个自然的问题：

- **有没有两条箭头撞到同一个点？** 如果从不相撞，即不同的输入总给出不同的输出，就叫**单射**（injective，也叫“一对一”）。
  单射不丢失信息：看到输出，就能确定输入。
- **右边的每个点都被指到了吗？** 如果是，即像等于整个陪域，就叫**满射**（surjective，也叫“到上”）。
- 既单又满，叫**双射**（bijective）。双射把两个集合的元素**完美配对**。

#### 例子

| 函数 | 单射？ | 满射？ | 为什么 |
|---|---|---|---|
| $n \mapsto n + 1$，$\mathbb{N} \to \mathbb{N}$ | 是 | 否 | 不同的数加 1 后仍不同；但 0 没有被指到 |
| $n \mapsto \lfloor n / 2 \rfloor$，$\mathbb{N} \to \mathbb{N}$ | 否 | 是 | 0 和 1 都映到 0；但每个 $m$ 都是 $2m$ 的像 |
| $\mathtt{not}$，$\mathtt{Bool} \to \mathtt{Bool}$ | 是 | 是 | true 和 false 互换，完美配对 |
| $n \mapsto 0$，$\mathbb{N} \to \mathbb{N}$ | 否 | 否 | 所有输入撞在一起；只有 0 被指到 |
| 生日：人 $\to$ 日期 | 否 | （几乎肯定）是 | 有人同一天生日 |

对有限集合，有一个实用的直觉（“鸽笼原理”）：从 $A$ 到 $B$ 的单射存在，需要 $|A| \le |B|$；
满射存在，需要 $|A| \ge |B|$；双射存在，需要 $|A| = |B|$。

#### 自己动手试试

下面的组件里，点击左边的一个元素，再点击右边的一个元素，就画出（或擦掉）一条箭头。它会实时告诉你：
这是不是一个良定义的函数？是单射吗？满射吗？双射吗？下方还会数出这两个集合之间一共有多少个函数（§7 会解释这个数）。

<div><Ch0_2FunctionChecker /></div>

#### 精确定义

- $f$ 是**单射**：对所有 $a_1, a_2 \in A$，若 $f(a_1) = f(a_2)$，则 $a_1 = a_2$。
  （等价说法：若 $a_1 \neq a_2$，则 $f(a_1) \neq f(a_2)$。数学家喜欢前一种写法，因为它更好用。）
- $f$ 是**满射**：对所有 $b \in B$，存在 $a \in A$ 使得 $f(a) = b$。
- $f$ 是**双射**：既是单射又是满射。

#### Lean 中的表达

Lean 核心库里已经有 `Function.Injective` 和 `Function.Surjective`。为了看清楚定义，我们自己写一遍：

```lean
namespace Toolkit

def Injective {α β : Type} (g : α → β) : Prop :=
  ∀ a₁ a₂, g a₁ = g a₂ → a₁ = a₂

def Surjective {α β : Type} (g : α → β) : Prop :=
  ∀ b, ∃ a, g a = b

def Bijective {α β : Type} (g : α → β) : Prop :=
  Injective g ∧ Surjective g

-- n ↦ n + 1 是单射
theorem succ_injective : Injective (fun n : Nat => n + 1) := by
  intro a₁ a₂ h
  have h' : a₁ + 1 = a₂ + 1 := h   -- 把 h 写成更直白的形式
  omega

-- 但不是满射：0 没有原像
theorem succ_not_surjective : ¬ Surjective (fun n : Nat => n + 1) := by
  intro h              -- 假设它是满射
  obtain ⟨a, ha⟩ := h 0  -- 那么存在 a 使得 a + 1 = 0
  have ha' : a + 1 = 0 := ha
  omega                -- 不可能

-- n ↦ n / 2 是满射：m 的原像是 2m
theorem half_surjective : Surjective (fun n : Nat => n / 2) := by
  intro m
  exact ⟨2 * m, show 2 * m / 2 = m by omega⟩

-- 但不是单射：0 和 1 撞到了一起
theorem half_not_injective : ¬ Injective (fun n : Nat => n / 2) := by
  intro h
  have : (0 : Nat) = 1 := h 0 1 rfl
  contradiction

-- not 是双射
theorem not_bijective : Bijective not := by
  constructor
  · intro a₁ a₂ h
    cases a₁ <;> cases a₂ <;> simp_all
  · intro b
    exact ⟨!b, by cases b <;> rfl⟩

end Toolkit
```

注意证明的结构和定义一一对应：证明单射时，先 `intro` 两个输入和“输出相等”的假设，再推出输入相等；
证明满射时，对每个 `b` 给出一个原像；证明“不是满射”时，假设它是满射，然后推出矛盾。

### 4.4 复合与恒等

#### 直觉

两个函数首尾相接：$f \colon A \to B$，$g \colon B \to C$，先做 $f$ 再做 $g$，得到从 $A$ 到 $C$ 的函数，叫作**复合**（composition），
记作 $g \circ f$，读作“$g$ 在 $f$ 之后”。注意顺序：**右边的先做**，因为 $(g \circ f)(a) = g(f(a))$。

只有当 $f$ 的陪域等于 $g$ 的定义域时才能复合，就像 Rust 里只有类型对得上才能把一个函数的返回值传给另一个函数。

**恒等函数**（identity）$\mathrm{id}_A \colon A \to A$ 什么也不做：$\mathrm{id}_A(a) = a$。

```diagram
A: (0, 0)
B: (2, 0)
C: (2, 1.6)
f: A -> B "f"
g: B -> C "g"
gf: A -> C "g \circ f" side=right
path "先 f 再 g": f g
path "直接走 g∘f": gf color=green
caption: 复合：从 A 到 C 的两条路径给出同一个函数。点击按钮看光点沿哪条路走。
```

#### 精确定义与定律

- $(g \circ f)(a) = g(f(a))$。
- **结合律**：$h \circ (g \circ f) = (h \circ g) \circ f$。所以可以不加括号地写 $h \circ g \circ f$。
- **单位律**：$f \circ \mathrm{id}_A = f$，$\mathrm{id}_B \circ f = f$。

这三条（复合、结合律、单位律）就是[第 1.1 章](/part1/01-category)里“范畴”的全部要求。函数是范畴的原型。

#### Lean 中的表达

```lean
example (a : Nat) : ((· * 2) ∘ (· + 1)) a = (a + 1) * 2 := rfl

theorem comp_assoc {α β γ δ : Type} (f : α → β) (g : β → γ) (h : γ → δ) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := rfl

theorem comp_id' {α β : Type} (f : α → β) : f ∘ id = f := rfl
theorem id_comp' {α β : Type} (f : α → β) : id ∘ f = f := rfl
```

三条定律的证明都是 `rfl`：把 `∘` 和 `id` 的定义展开，两边就一模一样。在 Lean 里，函数天然构成一个范畴。

单射和满射在复合下保持：两个单射的复合是单射，两个满射的复合是满射。

```lean
theorem Toolkit.Injective.comp {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : Toolkit.Injective g) (hf : Toolkit.Injective f) : Toolkit.Injective (g ∘ f) := by
  intro a₁ a₂ h          -- h : g (f a₁) = g (f a₂)
  apply hf               -- 要证 a₁ = a₂，只需证 f a₁ = f a₂
  apply hg               -- 要证 f a₁ = f a₂，只需证 g (f a₁) = g (f a₂)
  exact h
```

### 4.5 反函数、截面与收缩

#### 直觉

如果 $f \colon A \to B$ 是双射，每个 $b$ 恰好有一个原像，那么“反过来走”也是一个函数，叫作 $f$ 的**反函数**（inverse），记作 $f^{-1} \colon B \to A$。
先走 $f$ 再走 $f^{-1}$，回到原地；反之亦然。

#### 例子

- $\mathtt{not}$ 的反函数是它自己：$\mathtt{not}(\mathtt{not}(b)) = b$。
- $n \mapsto n + 1$（$\mathbb{N} \to \mathbb{N}$）没有反函数，因为 0 没有原像，“反过来走”时 0 无处可去。
  但 $n \mapsto n - 1$ 是它的**左逆**：先加 1 再减 1，总能回到原处。

#### 精确定义

- 若 $g \circ f = \mathrm{id}_A$，称 $g$ 是 $f$ 的**左逆**（left inverse）。这时 $f$ 必定是单射：$f$ 没有丢失信息，$g$ 能把它恢复出来。
- 若 $f \circ g = \mathrm{id}_B$，称 $g$ 是 $f$ 的**右逆**（right inverse）。这时 $f$ 必定是满射：每个 $b$ 都有原像 $g(b)$。
- 若 $g$ 既是左逆又是右逆，称 $g$ 是 $f$ 的**反函数**（或逆）。一个函数有反函数，当且仅当它是双射。

范畴论里，$g \circ f = \mathrm{id}$ 时也说 $f$ 是 $g$ 的**截面**（section），$g$ 是 $f$ 的**收缩**（retraction）。

#### Lean 中的表达

```lean
namespace Toolkit

theorem injective_of_leftInverse {α β : Type} {f : α → β} {g : β → α}
    (h : ∀ a, g (f a) = a) : Injective f := by
  intro a₁ a₂ hf         -- hf : f a₁ = f a₂
  calc a₁ = g (f a₁) := (h a₁).symm
    _ = g (f a₂) := by rw [hf]
    _ = a₂ := h a₂

theorem surjective_of_rightInverse {α β : Type} {f : α → β} {g : β → α}
    (h : ∀ b, f (g b) = b) : Surjective f :=
  fun b => ⟨g b, h b⟩    -- b 的原像就是 g b

-- 例子：n ↦ n - 1 是 n ↦ n + 1 的左逆
example : ∀ n : Nat, (fun m => m - 1) ((fun m => m + 1) n) = n := by
  intro n
  simp

end Toolkit
```

`injective_of_leftInverse` 的 `calc` 链读起来就像课本：$a_1 = g(f(a_1)) = g(f(a_2)) = a_2$。

**本书何处用到**：复合与恒等从[第 1.1 章](/part1/01-category)起无处不在；单射、满射、双射在[第 1.5 章](/part1/05-products-and-coproducts)正式出场，
在[第 2.6 章](/part2/06-yoneda-embedding)（米田嵌入是“单射”的）与[第 3.13 章](/part3/13-topoi)（单态射是单射的推广）中再次出现。

## 5 关系：等价关系、偏序、全序

#### 直觉

**关系**（relation）是对“两个元素之间是否有某种联系”的回答：“$a$ 小于等于 $b$”、“$a$ 整除 $b$”、“$a$ 和 $b$ 奇偶性相同”。
集合 $A$ 上的一个关系 $R$，对每一对 $(a, b)$ 回答“是”或“否”。$a$ 与 $b$ 有关系时写作 $a \mathrel{R} b$。

### 关系的几种性质

设 $R$ 是 $A$ 上的关系：

| 性质 | 定义 | $\le$ | 整除 $\mid$ | 同奇偶 | $<$ |
|---|---|---|---|---|---|
| 自反（reflexive） | 对所有 $a$：$a \mathrel{R} a$ | 是 | 是 | 是 | 否 |
| 对称（symmetric） | 若 $a \mathrel{R} b$ 则 $b \mathrel{R} a$ | 否 | 否 | 是 | 否 |
| 反对称（antisymmetric） | 若 $a \mathrel{R} b$ 且 $b \mathrel{R} a$，则 $a = b$ | 是 | 是（在 $\mathbb{N}$ 上） | 否 | 是（空真） |
| 传递（transitive） | 若 $a \mathrel{R} b$ 且 $b \mathrel{R} c$，则 $a \mathrel{R} c$ | 是 | 是 | 是 | 是 |
| 完全（total） | 对所有 $a, b$：$a \mathrel{R} b$ 或 $b \mathrel{R} a$ | 是 | 否 | 否 | 否 |

### 等价关系

**自反 + 对称 + 传递**的关系叫**等价关系**（equivalence relation）。它表达的是“在某种意义下一样”。

例子：“除以 3 余数相同”。它把 $\mathbb{N}$ 分成三堆：$\{0, 3, 6, \dots\}$、$\{1, 4, 7, \dots\}$、$\{2, 5, 8, \dots\}$，
每堆叫一个**等价类**。一般地，等价关系总是把集合切分成互不相交的等价类，同一类中的元素彼此等价。
“把等价的元素看作同一个”得到的新集合叫**商集**（quotient）。

```lean
-- “除以 3 余数相同”是等价关系。Equivalence 是核心库里的结构体，三个字段分别是自反、对称、传递
theorem mod3_equiv : Equivalence (fun a b : Nat => a % 3 = b % 3) :=
  ⟨fun _ => rfl,                     -- 自反：a % 3 = a % 3
   fun h => h.symm,                  -- 对称：等式反过来
   fun h₁ h₂ => h₁.trans h₂⟩         -- 传递：等式串起来
```

（Lean 核心库还提供 `Quot` 和 `Quotient`，用来真正构造商集；本书在[第 3.10 章](/part3/10-ends-and-coends)讨论余端时会用到“商”的思想。）

### 预序、偏序、全序

- **预序**（preorder）：自反 + 传递。例如“$a$ 能到达 $b$”（在一张有向图里）；或者“字符串长度 $\le$”：“ab”和“cd”互相 $\le$，但它们并不相等。
- **偏序**（partial order）：预序 + 反对称。例如子集关系 $\subseteq$、整除关系。“偏”是指不是任意两个元素都能比较：2 和 3 互不整除。
- **全序**（total order，也叫线性序）：偏序 + 完全。例如数的 $\le$：任意两个数都能比大小，可以排成一条线。

偏序可以画成一张图（叫 Hasse 图）：把 12 的所有因数画出来，若 $a$ 整除 $b$ 且中间没有别的因数，就从 $a$ 画一条箭头到 $b$。

```diagram
n1: (1, 2) "1"
n2: (0, 1.2) "2"
n3: (2, 1.2) "3"
n4: (0, 0.4) "4"
n6: (2, 0.4) "6"
n12: (1, -0.4) "12"
a12: n1 -> n2 ""
a13: n1 -> n3 ""
a24: n2 -> n4 ""
a26: n2 -> n6 ""
a36: n3 -> n6 ""
a412: n4 -> n12 ""
a612: n6 -> n12 ""
path "1 ∣ 2 ∣ 4 ∣ 12": a12 a24 a412
path "1 ∣ 3 ∣ 6 ∣ 12": a13 a36 a612 color=green
caption: 12 的因数在整除关系下构成偏序。传递性保证：沿箭头能走到的地方都“被整除”，例如 2 ∣ 12。4 和 6 之间没有路径：它们不可比较。
```

在 Lean 中，我们可以把这些定义写成结构体，并验证 $\mathbb{N}$ 上的 $\le$ 是全序、整除是偏序：

```lean
structure IsPreorder {α : Type} (R : α → α → Prop) : Prop where
  refl : ∀ a, R a a
  trans : ∀ {a b c}, R a b → R b c → R a c

structure IsPartialOrder {α : Type} (R : α → α → Prop) : Prop extends IsPreorder R where
  antisymm : ∀ {a b}, R a b → R b a → a = b

structure IsTotalOrder {α : Type} (R : α → α → Prop) : Prop extends IsPartialOrder R where
  total : ∀ a b, R a b ∨ R b a

theorem le_total_order : IsTotalOrder (fun a b : Nat => a ≤ b) where
  refl := Nat.le_refl
  trans := Nat.le_trans
  antisymm := Nat.le_antisymm
  total := Nat.le_total

theorem dvd_partial_order : IsPartialOrder (fun a b : Nat => a ∣ b) where
  refl := Nat.dvd_refl
  trans := Nat.dvd_trans
  antisymm := Nat.dvd_antisymm

-- 整除不是全序：2 和 3 不可比较
theorem dvd_not_total : ¬ IsTotalOrder (fun a b : Nat => a ∣ b) := by
  intro h
  cases h.total 2 3 with
  | inl h23 => exact absurd h23 (by decide)
  | inr h32 => exact absurd h32 (by decide)
```

（`a ∣ b` 是“整除”，输入 `\|` 或 `\mid`，注意它不是键盘上的竖线 `|`。）

**本书何处用到**：[第 1.3 章](/part1/03-categories-great-and-small)会把预序看成一个范畴：对象是元素，$a \le b$ 时有一条从 $a$ 到 $b$ 的箭头，
传递性就是复合，自反性就是恒等箭头。上面的 Hasse 图其实已经是一个范畴的图了（省略了恒等箭头和复合出来的箭头）。
[第 1.5 章](/part1/05-products-and-coproducts)里的“偏序集”（poset）也是它。等价关系在[第 3.10 章](/part3/10-ends-and-coends)出现。

## 6 同构与“在同构意义下”

#### 直觉

$\{0, 1\}$、$\{\mathtt{true}, \mathtt{false}\}$、$\{\text{红}, \text{绿}\}$ 是三个不同的集合，但作为“两个元素的集合”，它们没有本质区别：
只是元素的名字不同。只要给出一个完美的配对（双射），就可以把一个集合里的任何讨论原封不动地搬到另一个里。

这种“只差改个名字”的关系叫**同构**（isomorphism），记作 $A \cong B$。范畴论几乎从不问“两个东西是否**相等**”，
而只问“是否**同构**”。

#### 例子

- $\mathtt{Bool} \cong \{0, 1\}$。
- $A \times B \cong B \times A$：交换两个分量即可，交换两次回到原样。注意它们**不相等**：$(1, \mathtt{true})$ 和 $(\mathtt{true}, 1)$ 是不同的东西。
- $\mathtt{Bool} \cong \mathtt{Unit} + \mathtt{Unit}$：“两个值”就是“左边一个或右边一个”。这正是[第 1.6 章](/part1/06-simple-algebraic-data-types)“$2 = 1 + 1$”的类型版本。
- $A \times \mathtt{Unit} \cong A$：和单元素集合配对不增加任何信息。

#### 精确定义

在集合与函数的世界里，**同构**就是一对函数 $f \colon A \to B$ 和 $g \colon B \to A$，满足 $g \circ f = \mathrm{id}_A$ 且 $f \circ g = \mathrm{id}_B$。
（由 §4.5，这时 $f$ 是双射，$g$ 是它的反函数。）

[第 1.5 章](/part1/05-products-and-coproducts)会把这个定义推广到任意范畴：只需把“函数”换成“态射”。它不再提“元素”，只用复合和恒等来表达。
这是范畴论思维方式的一个缩影。

### “在同构意义下唯一”

数学家常说：“满足某某性质的对象**在同构意义下唯一**（unique up to isomorphism）。”意思是：满足这个性质的对象可能有很多个，
但它们两两同构，所以“本质上只有一个”。

例子：“单元素集合”有无穷多个，$\{0\}$、$\{\star\}$、$\{\text{猫}\}$……但任意两个之间都有（唯一的）同构，所以我们可以说“**那个**单元素集合”。
本书[第 1.5 章](/part1/05-products-and-coproducts)用泛构造定义的积、余积、始对象、终对象，全都是“在同构意义下唯一”的。

#### Lean 中的表达

```lean
structure Iso (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

infix:25 " ≅ " => Iso    -- 输入 \iso

def prodComm (α β : Type) : α × β ≅ β × α where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

def boolIsoUnitSum : Bool ≅ Unit ⊕ Unit where
  toFun b := if b then .inl () else .inr ()
  invFun
    | .inl _ => true
    | .inr _ => false
  left_inv b := by cases b <;> rfl
  right_inv s := by cases s <;> rfl

def prodUnit (α : Type) : α × Unit ≅ α where
  toFun p := p.1
  invFun a := (a, ())
  left_inv _ := rfl
  right_inv _ := rfl
```

注意 `Iso` 的后两个字段是**证明**：你无法构造一个“假同构”。这里有个微妙之处：在 Lean 里你不可能证明 `Bool = Unit ⊕ Unit`（类型的相等太强了），
但能轻松构造 `Bool ≅ Unit ⊕ Unit`。同构正是“相等”的恰当替代品。

**本书何处用到**：[1.5](/part1/05-products-and-coproducts)（同构的定义、泛构造的唯一性）、[1.6](/part1/06-simple-algebraic-data-types)（代数数据类型的同构）、
[1.10](/part1/10-natural-transformations)（自然同构）、[2.4](/part2/04-representable-functors)、[2.5](/part2/05-the-yoneda-lemma)、[3.2 伴随](/part3/02-adjunctions)。

## 7 基数与计数

#### 直觉

有限集合 $A$ 的**基数**（cardinality）就是它的元素个数，记作 $|A|$。$|\{\text{红}, \text{绿}, \text{蓝}\}| = 3$，$|\varnothing| = 0$。
两个有限集合同构，当且仅当它们元素个数相同。所以在“同构意义下”，有限集合只由它的大小决定。

### 三条计数规则

- **积**：$|A \times B| = |A| \cdot |B|$。表格有 $|A|$ 行、$|B|$ 列。
- **和**：$|A + B| = |A| + |B|$。贴了标签放在一起，个数相加。
- **函数**：从 $A$ 到 $B$ 的函数有 $|B|^{|A|}$ 个。

最后一条值得仔细论证。一个函数 $f \colon A \to B$ 就是对 $A$ 的**每个**元素，独立地选一个 $B$ 中的元素作为它的输出。
设 $A = \{a_1, \dots, a_n\}$，$|B| = m$：

- $f(a_1)$ 有 $m$ 种选法；
- $f(a_2)$ 也有 $m$ 种选法，与 $f(a_1)$ 的选择无关；
- ……
- $f(a_n)$ 也有 $m$ 种选法。

各个选择互相独立，所以总数是 $m \times m \times \cdots \times m = m^n$。这就是为什么从 $A$ 到 $B$ 的函数集合常记作 $B^A$，
[第 1.9 章](/part1/09-function-types)会把函数类型叫作**指数对象**（exponential）。

几个边界情况特别重要（它们在[第 1.5 章](/part1/05-products-and-coproducts)和[第 1.9 章](/part1/09-function-types)里扮演主角）：

- 从任意 $A$ 到单元素集合的函数：$1^{|A|} = 1$ 个。所有元素只能映到那唯一的点。
- 从空集到任意 $B$ 的函数：$|B|^0 = 1$ 个。这个唯一的函数叫**空函数**：没有输入，所以什么都不用分配，“什么都不做”本身就是一种（且唯一一种）分配方案。
- 从非空集合到空集的函数：$0^{|A|} = 0$ 个。有输入，却无处可去。
- 从 $A$ 到 $\mathtt{Bool}$ 的函数：$2^{|A|}$ 个，恰好等于幂集的大小（§2）。每个函数都回答“每个元素在不在子集里”。

在上面的[函数性质检查器](#自己动手试试)里调整两个集合的大小，就能看到这些数字。

#### Lean 中的表达

我们可以让 Lean 真的“列出”所有函数并数一数。把一个从 $\{0, \dots, n-1\}$ 到 $\{0, \dots, m-1\}$ 的函数表示成它的输出列表
$[f(0), \dots, f(n-1)]$，那么：

```lean
/-- 所有从 n 元集合到 m 元集合的函数（每个函数表示为它的输出列表）。 -/
def allFuns : Nat → Nat → List (List Nat)
  | 0, _ => [[]]                                  -- 空集出发：只有空函数
  | n + 1, m =>                                   -- 多一个输入：为它的输出选 m 种之一
    (allFuns n m).flatMap (fun f => (List.range m).map (fun b => b :: f))

#guard allFuns 2 2 == [[0, 0], [1, 0], [0, 1], [1, 1]]
#guard (allFuns 3 2).length == 8       -- 2^3
#guard (allFuns 2 3).length == 9       -- 3^2
#guard (allFuns 0 5).length == 1       -- 5^0：空函数
#guard (allFuns 2 0).length == 0       -- 0^2：无处可去

-- 不只是验证几个例子：对所有 n、m 都成立
theorem allFuns_length (n m : Nat) : (allFuns n m).length = m ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [allFuns, List.length_flatMap, List.map_const', List.sum_replicate_nat, ih,
      Nat.pow_succ, Nat.mul_comm]
```

`allFuns` 的定义就是上面的计数论证本身：给 $n$ 个输入的函数再加一个输入，这个新输入有 $m$ 种选择，所以数量乘以 $m$。
`allFuns_length` 用归纳法证明了它对所有 $n$、$m$ 都成立。

也可以直接对 `Bool → Bool` 证明：它恰好就是那 $2^2 = 4$ 个函数之一。

```lean
theorem bool_funs (g : Bool → Bool) :
    g = id ∨ g = not ∨ g = (fun _ => true) ∨ g = (fun _ => false) := by
  -- 一个 Bool → Bool 的函数完全由 g true 和 g false 决定：2 × 2 = 4 种情况
  cases ht : g true <;> cases hf : g false
  · right; right; right; funext b; cases b <;> simp [ht, hf]   -- 都是 false：常值 false
  · right; left; funext b; cases b <;> simp [ht, hf]           -- true ↦ false, false ↦ true：not
  · left; funext b; cases b <;> simp [ht, hf]                  -- true ↦ true, false ↦ false：id
  · right; right; left; funext b; cases b <;> simp [ht, hf]    -- 都是 true：常值 true
```

**本书何处用到**：[1.6 简单代数数据类型](/part1/06-simple-algebraic-data-types)（类型的“代数”：积对应乘法，和对应加法）、
[1.9 函数类型](/part1/09-function-types)（指数对象 $b^a$，以及 $a^{b+c} = a^b \times a^c$ 这样的恒等式）。

## 8 逻辑：命题、连接词与量词

### 8.1 命题与连接词

**命题**（proposition）是一个或真或假的陈述：“2 是偶数”（真）、“3 > 5”（假）、“每个大于 2 的偶数都是两个素数之和”（没人知道）。

用**连接词**可以把命题组合起来：

| 记号 | 读作 | 何时为真 |
|---|---|---|
| $P \wedge Q$ | P 并且 Q | 两个都真 |
| $P \vee Q$ | P 或者 Q | 至少一个真（数学里的“或”是可兼的：都真也算） |
| $\neg P$ | 非 P | P 为假 |
| $P \Rightarrow Q$ | 若 P 则 Q（P 蕴涵 Q） | 除了“P 真而 Q 假”之外都为真 |
| $P \Leftrightarrow Q$ | P 当且仅当 Q | P、Q 同真或同假 |

**蕴涵**最容易让人困惑。想象一个承诺：“如果明天下雨，我就带伞。”什么时候我食言了？只有“下雨了，但我没带伞”这一种情况。
如果明天没下雨，无论我带不带伞，我都没有食言。所以 $P \Rightarrow Q$ 在 $P$ 为假时**自动为真**。这就是 §2 提到的**空真**。

| P | Q | P ⇒ Q |
|---|---|---|
| 真 | 真 | 真 |
| 真 | 假 | **假** |
| 假 | 真 | 真 |
| 假 | 假 | 真 |

在 Lean 中，`Prop` 里的命题使用 `∧ ∨ ¬ → ↔`（见 [0.1 §14](/guide/lean-for-rustaceans#_14-命题即类型、证明即程序)）；
对 `Bool` 值则有可计算的版本 `&& || !`。真值表可以让 Lean 逐行检查：

```lean
-- 蕴涵的真值表：p → q 等价于 (!p || q)
example : ∀ p q : Bool, (p → q) ↔ ((!p || q) = true) := by decide

-- 德摩根律：非（p 且 q）等于（非 p）或（非 q）
example : ∀ p q : Bool, (!(p && q)) = (!p || !q) := by decide
```

### 8.2 量词

**全称量词** $\forall$（“对所有”）和**存在量词** $\exists$（“存在”）用来谈论“一批东西”：

- $\forall n \in \mathbb{N},\ n + 0 = n$：对所有自然数 $n$，$n + 0 = n$。
- $\exists n \in \mathbb{N},\ n \cdot n = 49$：存在一个自然数 $n$，使得 $n \cdot n = 49$。

**否定量词**时，$\forall$ 和 $\exists$ 互换：

- “不是所有人都喜欢香菜” = “存在一个人不喜欢香菜”：$\neg \forall x, P(x) \Leftrightarrow \exists x, \neg P(x)$。
- “不存在会飞的猪” = “所有猪都不会飞”：$\neg \exists x, P(x) \Leftrightarrow \forall x, \neg P(x)$。

```lean
theorem not_exists_iff {α : Type} (P : α → Prop) : (¬ ∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h x hx          -- 假设“不存在”，任取 x 和“P x”
    exact h ⟨x, hx⟩       -- 那就存在了，矛盾
  · intro h ⟨x, hx⟩       -- 假设“所有 x 都不满足”，又有一个满足的 x
    exact h x hx          -- 矛盾
```

### 8.3 量词的顺序很重要

比较这两句话：

1. $\forall n,\ \exists m,\ m > n$：“对每个数 $n$，都有一个比它大的数 $m$”。**真**：取 $m = n + 1$ 即可。$m$ 可以依赖于 $n$。
2. $\exists m,\ \forall n,\ m > n$：“存在一个数 $m$，比所有数都大”。**假**：没有最大的自然数（$m$ 自己就不比自己大）。

只是交换了量词的顺序，意思天差地别。诀窍是**从左往右读，把它想成一个游戏**：$\forall$ 是对手出招（任意选一个），$\exists$ 是你接招（你来选一个）。
第一句里，对手先选 $n$，你看到 $n$ 之后再选 $m$，你当然能赢。第二句里，你得先选 $m$，对手看到你的 $m$ 后再选 $n$，对手总能赢（选 $n = m$）。

```lean
theorem forall_exists_gt : ∀ n : Nat, ∃ m, m > n :=
  fun n => ⟨n + 1, by omega⟩         -- 看到 n 之后，选 m = n + 1

theorem not_exists_forall_gt : ¬ ∃ m : Nat, ∀ n, m > n := by
  intro ⟨m, hm⟩                      -- 假设有这样的 m
  have := hm m                       -- 对手选 n = m：得到 m > m
  omega                              -- 矛盾
```

Lean 的证明完美对应这个“游戏”：证明 $\forall$ 就是写一个函数（对手给你 $n$）；证明 $\exists$ 就是给出见证者（你选 $m$）。

### 8.4 怎么读范畴论里的长句子

本书会反复出现这样的句子（它是[第 1.5 章](/part1/05-products-and-coproducts)中积的定义）：

> 对任意对象 $c$ 和任意一对态射 $p \colon c \to a$、$q \colon c \to b$，**存在唯一的**态射 $m \colon c \to a \times b$，使得 $p = \pi_1 \circ m$ 且 $q = \pi_2 \circ m$。

别慌，按“游戏”的方式拆开：

1. **对手**任意给你一个对象 $c$，以及两个态射 $p$、$q$（$\forall$）。
2. **你**要给出一个态射 $m$（$\exists$），满足两个等式（$\wedge$）。
3. 而且这个 $m$ 必须是**唯一**的：任何其他满足这两个等式的 $m'$，都必须等于 $m$（§11）。

写成符号：$\forall c,\ \forall p,\ \forall q,\ \exists!\, m,\ (p = \pi_1 \circ m \wedge q = \pi_2 \circ m)$。
你会发现，绝大多数“泛性质”都是这个形状。

**本书何处用到**：处处都用。[1.9 函数类型](/part1/09-function-types)会解释逻辑与类型的深刻对应（Curry–Howard），[0.1 §14](/guide/lean-for-rustaceans#_14-命题即类型、证明即程序)已经预演过了。

## 9 证明方法

### 9.1 直接证明

从已知条件出发，一步步推出结论。要证“若 $P$ 则 $Q$”，就**假设** $P$ 成立，然后推出 $Q$。

例：两个偶数之和是偶数。设 $a = 2k$，$b = 2l$，则 $a + b = 2k + 2l = 2(k + l)$，所以 $a + b$ 是偶数。

```lean
theorem even_add_even (a b : Nat) (ha : ∃ k, a = 2 * k) (hb : ∃ l, b = 2 * l) :
    ∃ j, a + b = 2 * j := by
  obtain ⟨k, hk⟩ := ha       -- 取出 a = 2k
  obtain ⟨l, hl⟩ := hb       -- 取出 b = 2l
  exact ⟨k + l, by omega⟩    -- 见证者 k + l
```

### 9.2 反证法与逆否命题

**证明“非 P”**：假设 $P$ 成立，推出矛盾。这其实就是“非”的定义（$\neg P$ 就是 $P \Rightarrow \text{假}$），在 Lean 里完全不需要额外的公理。
§4.3 的 `succ_not_surjective` 和 §8.3 的 `not_exists_forall_gt` 都是这样证的。

**证明“P”**：假设 $\neg P$ 成立，推出矛盾，从而断定 $P$。这一步需要**排中律**（$P$ 要么真要么假），属于经典逻辑。
Lean 中用 `Classical.byContradiction`：

```lean
theorem by_contra_demo (p : Prop) (h : ¬¬p) : p := by
  apply Classical.byContradiction   -- 要证 p，只需从 ¬p 推出矛盾
  intro hnp
  exact h hnp
```

**逆否命题**：“若 $P$ 则 $Q$”等价于“若非 $Q$ 则非 $P$”。“如果下雨，地就湿”等价于“如果地不湿，就没下雨”。
从左推右不需要经典逻辑：

```lean
theorem contrapositive' (p q : Prop) (hpq : p → q) : ¬q → ¬p :=
  fun hnq hp => hnq (hpq hp)
```

### 9.3 数学归纳法

要证明“对所有自然数 $n$，$P(n)$ 成立”，只需证明两件事：

1. **基础情况**：$P(0)$ 成立；
2. **归纳步骤**：对任意 $k$，若 $P(k)$ 成立（**归纳假设**），则 $P(k + 1)$ 成立。

直觉是一排多米诺骨牌：第一块会倒；任何一块倒下都会推倒下一块。于是所有骨牌都会倒。

为什么这是对的？回忆 [0.1 §6.3](/guide/lean-for-rustaceans#_6-3-lean-内置的归纳类型)：自然数的定义就是“要么是 0，要么是某个数的后继”。
每个自然数都是从 0 出发、有限次取后继得到的，所以沿着这条构造路径，$P$ 一路传递下去。归纳法就是对归纳类型做**递归**，只不过结果是证明。

例：$0 + 1 + \cdots + n = \dfrac{n(n+1)}{2}$。为了避免除法，证明 $2 \times (0 + 1 + \cdots + n) = n(n+1)$：

- 基础：$n = 0$，左边 $= 0$，右边 $= 0$。
- 步骤：设 $2 S(k) = k(k+1)$。则 $2 S(k+1) = 2(k + 1) + 2 S(k) = 2(k+1) + k(k+1) = (k+1)(k+2)$。

```lean
def sumUpTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumUpTo n

theorem gauss (n : Nat) : 2 * sumUpTo n = n * (n + 1) := by
  induction n with
  | zero => rfl                         -- 基础情况：2 * 0 = 0 * 1
  | succ k ih =>                        -- ih : 2 * sumUpTo k = k * (k + 1)
    simp only [sumUpTo, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
    omega                               -- 展开乘法后，剩下的是线性推理
```

归纳法不只适用于自然数，对列表、树等任何归纳类型都可以做（对列表就是：对空列表成立；若对 `xs` 成立则对 `x :: xs` 成立）。
[0.1 §15](/guide/lean-for-rustaceans#_15-3-常用-tactic-一览) 里的 `sumList_append` 就是对列表的归纳。

### 9.4 构造性证明

要证明“存在某个东西”，最直接的办法是**把它造出来**，这叫**构造性证明**。§4.2 的“16 在偶数的平方的像里”（造出 4）、
§8.3 的“存在比 $n$ 大的数”（造出 $n + 1$）都是构造性的。

数学上也有非构造性的存在证明，比如“假设不存在，推出矛盾，所以存在”，它告诉你“有”，却不告诉你“是哪个”。
Lean 默认是构造性的：一个 `∃` 的构造性证明里**真的包含**见证者。这和编程的直觉吻合：说“存在一个满足条件的值”，最有说服力的方式是把它返回给你。
范畴论的许多证明本质上是构造性的：“存在一个态射”通常意味着“这是那个态射的构造方法”。

**本书何处用到**：直接证明和构造性证明处处可见；归纳法是[2.3 自由幺半群](/part2/03-free-monoids)和[3.8 F-代数](/part3/08-f-algebras)
（卡塔态射本质上就是“归纳法 / 结构递归”的范畴论版本）的基础。

## 10 代数结构：幺半群与群

### 10.1 幺半群

#### 直觉

**幺半群**（monoid）是“能把东西两两合并，而且有一个‘什么都不做’的元素”的结构。比如：

- 数字的加法：合并就是相加，“什么都不做”是 0。
- 字符串的拼接：合并就是连接，“什么都不做”是空串。
- 列表的拼接：`xs ++ ys`，单位元是 `[]`。

要求合并满足**结合律**：先合并前两个和先合并后两个，结果一样。所以可以不加括号地写 $a \cdot b \cdot c$。

#### 精确定义

幺半群是一个集合 $M$，加上一个二元运算 $\cdot \colon M \times M \to M$ 和一个元素 $e \in M$，满足：

- 结合律：$(a \cdot b) \cdot c = a \cdot (b \cdot c)$；
- 单位律：$e \cdot a = a$，$a \cdot e = a$。

#### 例子与反例

| 集合 | 运算 | 单位元 | 是幺半群吗 |
|---|---|---|---|
| $\mathbb{N}$ | $+$ | $0$ | 是 |
| $\mathbb{N}$ | $\times$ | $1$ | 是 |
| $\mathbb{N}$ | $\max$ | $0$ | 是 |
| 字符串 | 拼接 | 空串 | 是（但不满足交换律：“ab” ≠ “ba”） |
| $\mathtt{Bool}$ | $\wedge$（与） | $\mathtt{true}$ | 是 |
| $A \to A$ 的函数 | 复合 $\circ$ | $\mathrm{id}_A$ | 是 |
| $\mathbb{N}$ | 减法 | ？ | **否**：$(5 - 3) - 1 = 1$，而 $5 - (3 - 1) = 3$，不满足结合律 |

倒数第二行特别重要：从一个集合到它自身的函数，在复合下构成幺半群。[第 1.3 章](/part1/03-categories-great-and-small)会说明，
**幺半群就是只有一个对象的范畴**，而这个例子是理解这一点的钥匙。

#### Lean 中的表达

```lean
namespace Alg

class Monoid (M : Type) where
  op : M → M → M
  e : M
  op_assoc : ∀ a b c : M, op (op a b) c = op a (op b c)
  e_op : ∀ a : M, op e a = a
  op_e : ∀ a : M, op a e = a

instance : Monoid Nat where
  op := (· + ·)
  e := 0
  op_assoc := Nat.add_assoc
  e_op := Nat.zero_add
  op_e := Nat.add_zero

instance {α : Type} : Monoid (List α) where
  op := (· ++ ·)
  e := []
  op_assoc := List.append_assoc
  e_op := List.nil_append
  op_e := List.append_nil

/-- 自同态幺半群：α → α 的函数在复合下构成幺半群。三条定律都是 rfl。 -/
def Endo (α : Type) : Type := α → α

instance {α : Type} : Monoid (Endo α) where
  op g f := g ∘ f
  e := id
  op_assoc _ _ _ := rfl
  e_op _ := rfl
  op_e _ := rfl

end Alg

-- 自然数减法不满足结合律
example : ¬ ∀ a b c : Nat, (a - b) - c = a - (b - c) := by
  intro h
  have := h 5 3 1      -- (5 - 3) - 1 = 5 - (3 - 1)，即 1 = 3
  omega
```

#### 幺半群同态

两个幺半群之间“保持结构”的函数叫**同态**（homomorphism）：$h(e) = e'$，$h(a \cdot b) = h(a) \cdot' h(b)$。
例：`List.length` 是从 $(\text{列表}, \mathbin{+\!\!+}, [\,])$ 到 $(\mathbb{N}, +, 0)$ 的同态：空列表长度为 0，拼接后的长度等于长度之和。

```lean
example : ([] : List Nat).length = 0 := rfl
example (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := List.length_append
```

同态是[第 2.3 章 自由幺半群](/part2/03-free-monoids)的核心概念，也是“保持结构的映射”（函子的前身）的第一个例子。

### 10.2 群

**群**（group）是每个元素都有**逆元**的幺半群：对每个 $a$，有 $a^{-1}$ 使得 $a^{-1} \cdot a = e$（以及 $a \cdot a^{-1} = e$）。
逆元就是“撤销”操作。

- $(\mathbb{Z}, +, 0)$ 是群：$a$ 的逆元是 $-a$。
- $(\mathbb{N}, +, 0)$ 不是群：3 没有“加上以后得 0”的自然数。
- $(\mathtt{Bool}, \oplus, \mathtt{false})$（异或）是群：每个元素是自己的逆元。
- 正方形的旋转 $\{0°, 90°, 180°, 270°\}$ 在“接连旋转”下是群：旋转 90° 的逆是旋转 270°。

```lean
namespace Alg

class Group (G : Type) extends Monoid G where
  inv : G → G
  inv_op : ∀ a : G, op (inv a) a = e

instance : Monoid Int where
  op := (· + ·)
  e := 0
  op_assoc := Int.add_assoc
  e_op := Int.zero_add
  op_e := Int.add_zero

instance : Group Int where
  inv a := -a
  inv_op := Int.add_left_neg

end Alg
```

群在本书中出场不多（[2.5 米田引理](/part2/05-the-yoneda-lemma)的挑战题、[3.8 F-代数](/part3/08-f-algebras)的例子中会提到），
但“对称性”的直觉在数学里无处不在，了解一下没有坏处。

**本书何处用到**：幺半群是全书的线索之一：[1.3](/part1/03-categories-great-and-small)（幺半群即单对象范畴）、
[1.4 Kleisli 范畴](/part1/04-kleisli-categories)（Writer 用幺半群累积日志）、[2.3 自由幺半群](/part2/03-free-monoids)、
[3.6](/part3/06-monads-categorically) 与 [3.15](/part3/15-monads-monoids-and-categories)（“单子就是自函子范畴中的幺半群”，那句著名的话终于会被讲清楚）。

## 11 “唯一存在”

#### 直觉

“存在唯一的 $x$ 使得 $P(x)$”，记作 $\exists!\, x,\ P(x)$，包含**两层**意思：

1. **存在**：至少有一个 $x$ 满足 $P$；
2. **唯一**：至多有一个，即任何两个满足 $P$ 的东西都相等。

#### 例子

- $\exists!\, n \in \mathbb{N},\ n + 3 = 5$：真，$n = 2$，并且只有它。
- $\exists!\, n \in \mathbb{N},\ n > 3$：假，存在但不唯一（4、5、6……）。
- $\exists!\, n \in \mathbb{N},\ n + 5 = 3$：假，唯一性倒是满足（没有两个不同的解），但根本不存在。
- 从空集到任意集合 $B$，**存在唯一**的函数（§7 的空函数）。
- 从任意集合到单元素集合，**存在唯一**的函数（把所有元素映到那个点）。

最后两个例子就是[第 1.5 章](/part1/05-products-and-coproducts)里的**始对象**和**终对象**：空集是集合范畴的始对象，单元素集合是终对象。

#### 精确定义

$\exists!\, x,\ P(x)$ 定义为：$\exists x,\ \big(P(x) \wedge \forall y,\ P(y) \Rightarrow y = x\big)$。
即“存在一个 $x$ 满足 $P$，并且任何满足 $P$ 的 $y$ 都等于这个 $x$”。

证明唯一性的标准套路：**假设另有一个 $y$ 也满足条件，然后证明 $y = x$**。

#### Lean 中的表达

Lean 核心库没有 `∃!` 记号（它在 Mathlib 里），我们自己定义：

```lean
def ExistsUnique' {α : Type} (P : α → Prop) : Prop :=
  ∃ x, P x ∧ ∀ y, P y → y = x

example : ExistsUnique' (fun n : Nat => n + 3 = 5) :=
  ⟨2, rfl, fun y hy => by omega⟩       -- 存在：2；唯一：若 y + 3 = 5 则 y = 2

-- 从 Empty（空集）到任意类型，存在唯一的函数
theorem from_empty_unique (β : Type) : ExistsUnique' (fun _ : Empty → β => True) :=
  ⟨(fun e => nomatch e),               -- 存在：空函数（没有输入，不需要任何分支）
   trivial,
   fun _ _ => funext (fun e => nomatch e)⟩  -- 唯一：任何两个函数在“所有”（零个）输入上都相等

-- 从任意类型到 Unit（单元素集合），存在唯一的函数
theorem to_unit_unique (α : Type) : ExistsUnique' (fun _ : α → Unit => True) :=
  ⟨fun _ => (),                        -- 存在：全部映到 ()
   trivial,
   fun _ _ => funext (fun _ => rfl)⟩   -- 唯一：Unit 只有一个值，g a 只能是 ()
```

`from_empty_unique` 的唯一性证明很有意思：要证两个从 `Empty` 出发的函数相等，用 `funext` 就要对每个输入 `e : Empty` 证明值相等，
但根本没有这样的 `e`，`nomatch e` 直接结束。这就是空真在证明里的样子。

::: tip 唯一存在与“在同构意义下唯一”
注意区分两种“唯一”：

- “**存在唯一的态射**”：态射是严格唯一的，就是这一个，是相等意义下的唯一。
- “**对象在同构意义下唯一**”：可能有很多个满足条件的对象，但两两同构（§6）。

泛构造恰好把两者联系起来：因为满足泛性质的**态射**唯一，所以满足泛性质的**对象**在同构意义下唯一。[第 1.5 章](/part1/05-products-and-coproducts)
会第一次完整地展示这个论证。
:::

在交换图里，“唯一存在的态射”习惯画成**虚线**箭头（见下一节）。

**本书何处用到**：[1.5](/part1/05-products-and-coproducts)（始对象、终对象、积、余积）、[2.2 极限与余极限](/part2/02-limits-and-colimits)、
[3.2 伴随](/part3/02-adjunctions)、[3.8 F-代数](/part3/08-f-algebras)（始代数）……泛性质的地方就有它。

## 12 交换图怎么读

#### 直觉

**交换图**（commutative diagram）是范畴论的“插图语言”。点（或字母）代表对象（比如集合、类型），箭头代表态射（比如函数）。
一条“路径”就是首尾相接的一串箭头，代表它们的复合。

说一个图**交换**（commutes），意思是：**从同一个起点到同一个终点的任意两条路径，复合出来的结果相等。**

### 例子：三角形

```diagram
A: (0, 0)
B: (2, 0)
C: (2, 1.6)
f: A -> B "f"
g: B -> C "g"
h: A -> C "h" side=right
path "路径一：先 f 再 g": f g
path "路径二：直接 h": h color=green
caption: 这个三角形交换，意思就是 h = g ∘ f。
```

从 $A$ 到 $C$ 有两条路：先 $f$ 后 $g$（复合为 $g \circ f$），或者直接走 $h$。图交换意味着 $h = g \circ f$。
一个图就是一个（或一组）等式，只是画出来更容易看清结构。

### 例子：方块

```diagram
TL: (0, 0) "\mathbb{N}"
TR: (2.2, 0) "\mathbb{N}"
BL: (0, 1.6) "\mathbb{N}"
BR: (2.2, 1.6) "\mathbb{N}"
top: TL -> TR "+1"
right: TR -> BR "\times 2" side=left
left: TL -> BL "\times 2" side=right
bottom: BL -> BR "+2" side=right
path "先 +1 再 ×2": top right
path "先 ×2 再 +2": left bottom color=green
caption: 从左上到右下有两条路径：(n + 1) × 2 和 n × 2 + 2。它们总是相等，所以这个方块交换。
```

方块交换的意思是 $(\times 2) \circ (+1) = (+2) \circ (\times 2)$，也就是对所有 $n$，$(n + 1) \times 2 = n \times 2 + 2$。在 Lean 中：

```lean
theorem square_commutes : (· * 2) ∘ (· + 1) = (· + 2) ∘ (fun n : Nat => n * 2) := by
  funext n
  show (n + 1) * 2 = n * 2 + 2
  omega
```

反过来，如果把底边换成 $+1$，方块就**不交换**了：$(n + 1) \times 2 \neq n \times 2 + 1$。“画得出图”不代表“图交换”，交换是需要证明的性质。

```lean
theorem square_fails : (· * 2) ∘ (· + 1) ≠ (· + 1) ∘ (fun n : Nat => n * 2) := by
  intro h
  have := congrFun h 0      -- 在 n = 0 处求值：2 = 1
  simp at this
```

`congrFun h 0` 的意思是：既然两个函数相等，那么它们在 0 处的值也相等。

### 读图的几个约定

- **箭头的方向就是函数的方向**：$f \colon A \to B$ 画成从 $A$ 指向 $B$ 的箭头。复合时，沿着箭头走的顺序和 $\circ$ 的书写顺序**相反**：
  先走 $f$ 再走 $g$，写作 $g \circ f$。
- **虚线箭头**通常表示“存在唯一”的态射（§11），它是由图中其他部分“决定”的。
- **自环箭头**（从一个对象指回自己）常用来画恒等态射 $\mathrm{id}_A$，不过通常省略不画。
- **双线箭头** $\Rightarrow$ 在本书后半部分表示自然变换（[第 1.10 章](/part1/10-natural-transformations)），它连接的是函子而不是对象。
- **追图**（diagram chasing）：拿一个具体的元素，沿着不同的路径走一遍，看结果是否相同。这是检验交换性最朴素的方法，
  也正是本书交换图上“路径动画”按钮的含义：点一下，看光点沿两条路走，殊途同归。

**本书何处用到**：从[第 1.1 章](/part1/01-category)的复合开始，到[第 1.5 章](/part1/05-products-and-coproducts)的泛构造、
[第 1.10 章](/part1/10-natural-transformations)的自然性方块，再到第三部分的伴随与单子，交换图是本书最主要的表达工具。

## 练习

1. 写出 $\{a, b\}$ 到 $\{0, 1, 2\}$ 的所有函数。共有几个？其中几个是单射？有满射吗？用上面的函数性质检查器验证你的答案。
2. 证明：如果 $g \circ f$ 是单射，那么 $f$ 是单射。（提示：仿照 `Toolkit.Injective.comp` 的写法。）
3. 证明：如果 $g \circ f$ 是满射，那么 $g$ 是满射。
4. “$a$ 和 $b$ 的差能被 5 整除”是 $\mathbb{Z}$ 上的等价关系吗？“$a$ 整除 $b$”是 $\mathbb{Z}$ 上的偏序吗？（提示：考虑 $2$ 和 $-2$。）
5. 构造同构 `(α ⊕ β) ≅ (β ⊕ α)`。
6. 用 Lean 证明 $\forall n,\ 2^n \geq n + 1$。（提示：对 $n$ 归纳，归纳步骤中 $2^{k+1} = 2^k \cdot 2$，可以用 `Nat.pow_succ` 改写，然后 `omega`。）

::: details 参考答案

1. 共 $3^2 = 9$ 个函数：$(f(a), f(b))$ 可以是 $(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)$。
   单射是 $f(a) \neq f(b)$ 的那些，共 $3 \times 2 = 6$ 个。没有满射：两个输入最多覆盖两个输出，而陪域有三个元素。
4. 前者是：$a - a = 0$ 能被 5 整除（自反）；若 $5 \mid a - b$ 则 $5 \mid b - a$（对称）；若 $5 \mid a - b$ 且 $5 \mid b - c$ 则 $5 \mid a - c$（传递）。
   后者不是偏序：$2 \mid -2$ 且 $-2 \mid 2$，但 $2 \neq -2$，反对称性不成立。不过它仍然是一个预序。

```lean
namespace Toolkit

-- 2
theorem injective_of_comp {α β γ : Type} {f : α → β} {g : β → γ}
    (h : Injective (g ∘ f)) : Injective f := by
  intro a₁ a₂ hf
  apply h
  show g (f a₁) = g (f a₂)
  rw [hf]

-- 3
theorem surjective_of_comp {α β γ : Type} {f : α → β} {g : β → γ}
    (h : Surjective (g ∘ f)) : Surjective g := by
  intro c
  obtain ⟨a, ha⟩ := h c
  exact ⟨f a, ha⟩

end Toolkit

-- 5
def sumComm (α β : Type) : (α ⊕ β) ≅ (β ⊕ α) where
  toFun
    | .inl a => .inr a
    | .inr b => .inl b
  invFun
    | .inl b => .inr b
    | .inr a => .inl a
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

-- 6
theorem two_pow_ge (n : Nat) : 2 ^ n ≥ n + 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega
```

:::

## 本章小结

- **集合**只关心“谁在里面”；Lean 中类型像集合，子集可以表示为谓词 `α → Prop`。$A \subseteq B$ 意为 $A$ 的元素都在 $B$ 里。
- **积** $A \times B$ 是有序对，**不交并** $A + B$ 是贴了标签的并；它们的大小分别是乘积与和。对应 Lean 的 `α × β` 与 `α ⊕ β`。
- **函数**给每个输入恰好一个输出（良定义）。Lean 的函数天然如此。函数的复合满足结合律与单位律，这正是范畴的雏形。
- **单射**不撞车，**满射**全覆盖，**双射**完美配对；有左逆则单，有右逆则满，有反函数当且仅当双射。
- **等价关系**（自反、对称、传递）表示“某种意义下一样”；**预序**（自反、传递）、**偏序**（再加反对称）、**全序**（再加完全）表示“某种意义下的大小”，它们都能看成范畴。
- **同构**是一对互逆的函数，表示“只差改个名字”；范畴论只在同构意义下谈论对象，“在同构意义下唯一”是它的标准说法。
- 从 $A$ 到 $B$ 的函数有 $|B|^{|A|}$ 个；空集到任何集合恰有一个函数，任何集合到单元素集合恰有一个函数。
- 读带量词的句子时，把 $\forall$ 想成对手出招、$\exists$ 想成你接招；量词顺序不能随便交换。
- 证明方法：直接证明、反证法（证“非”不需要经典逻辑）、归纳法（对归纳类型的递归）、构造性证明（把见证者造出来）。
- **幺半群**：结合的运算加单位元，例如加法、拼接、函数复合；**群**再加逆元。幺半群就是单对象范畴。
- **唯一存在**意为“存在，且任何两个都相等”；**交换图**意为“同起点同终点的路径复合相等”，虚线箭头常表示唯一存在的态射。
