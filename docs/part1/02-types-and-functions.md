# 1.2 类型与函数

```lean hidden
import Std.Data.HashMap
```

类型与函数构成的范畴在编程中扮演着重要角色。所以我们来聊聊：类型是什么？我们为什么需要它？

## 谁需要类型？

关于静态类型与动态类型、强类型与弱类型孰优孰劣，似乎一直有争议。我用一个思想实验来说明这些选择。想象数以百万计的猴子坐在电脑键盘前，快乐地乱敲一气，生成程序、编译、运行。

![敲键盘的猴子](/img/1.2/img_1329.jpg)

如果用机器语言，猴子们敲出的任何字节组合都会被接受并运行。但有了高级语言，我们就会庆幸编译器能检测出词法和语法错误。许多猴子会因此拿不到香蕉，但剩下的程序更有机会是有用的。类型检查又提供了一道屏障，挡住无意义的程序。而且，在动态类型语言里，类型不匹配要到运行时才会被发现；而在强类型、静态检查的语言里，类型不匹配在编译时就会被发现，大量错误的程序还没来得及运行就被淘汰了。

所以问题是：我们是想让猴子们开心，还是想写出正确的程序？

在“猴子打字”思想实验里，通常的目标是敲出莎士比亚全集。如果在流程中加入拼写检查器和语法检查器，成功的几率会大大提高。而类型检查器的类比会更进一步：它能确保一旦罗密欧被声明为人类，他就不会长出叶子，也不会用他强大的引力场捕获光子。

## 类型关乎可复合性

范畴论讲的是箭头的复合。但并不是任意两支箭头都能复合：一支箭头的目标对象必须和下一支箭头的源对象相同。在编程中，我们把一个函数的结果传给另一个函数。如果接收方函数无法正确解读来源函数产出的数据，程序就没法工作。两头必须对得上，复合才能成立。语言的类型系统越强，这种匹配就越能被精确地描述、被机器验证。（上一章你已经看到：在 Lean 的 `Category` 定义里，`comp : Hom b c → Hom a b → Hom a c` 中的那个共同的 `b`，正是“两头对得上”的类型化表述。）

我听到的反对强静态类型检查的唯一严肃论据是：它可能会把一些语义上正确的程序也拒之门外。实践中这种情况极其罕见；而且无论如何，每种语言都提供了某种后门，在真正必要时绕过类型系统。即使 Haskell 也有 `unsafeCoerce`；Rust 有 `unsafe` 和 `std::mem::transmute`；Lean 也有 `unsafeCast`（只能在标记为 `unsafe` 的定义里使用）。但这种手段应该审慎使用。卡夫卡笔下的格里高尔·萨姆沙变成一只巨大的甲虫时，就打破了类型系统——我们都知道结局如何。

我常听到的另一个论据是：处理类型给程序员带来了太多负担。在亲手写过几个 C++ 迭代器的声明之后，我挺能体会这种心情的——只不过，有一种叫做**类型推断**（type inference）的技术，能让编译器根据上下文推导出大部分类型。在 C++ 里你现在可以把变量声明为 `auto`，让编译器去推它的类型；在 Rust 里，`let v = Vec::new();` 之后往里 `push` 一个 `i32`，编译器就知道 `v` 是 `Vec<i32>`。

在 Haskell 里，除了少数情况，类型标注完全是可选的。Lean 的推断同样强大，局部变量、匿名函数的参数、隐式参数几乎都不用标注；按惯例，顶层的 `def` 和 `theorem` 会写出完整签名（Rust 也要求顶层函数写出签名）。程序员无论如何都倾向于写上类型标注，因为它们能说明很多关于代码语义的东西，还能让编译错误更容易理解。用 Haskell（以及 Lean）做项目时，常见的做法是先设计类型。之后，类型标注驱动着实现，成为由编译器强制执行的注释。

强静态类型常常被当作不测试代码的借口。你有时会听到 Haskell 程序员说：“只要编译通过，就一定是对的。”当然，类型正确的程序并不能保证在“输出正确结果”的意义上是正确的。这种满不在乎的态度导致的结果是：在好几项研究中，Haskell 在代码质量上并没有像人们预期的那样遥遥领先。看来在商业环境里，修 bug 的压力只会施加到某个质量水平为止——这完全取决于软件开发的经济学和最终用户的容忍度，而和编程语言或方法论关系不大。更好的标准也许是：统计有多少项目延期，或者交付时功能被大幅砍掉。

::: tip Lean 深入：“编译通过就是对的”——在 Lean 里可以是真的
在 Lean 里，类型不仅能说“这个函数接受 `List Nat` 返回 `List Nat`”，还能说“返回的列表是有序的，并且是输入的一个排列”。一旦把**规格说明**写进类型，“编译通过”就真的意味着“满足规格”。当然，前提是你写对了规格——Lean 能保证程序符合你说的话，却不能保证你说的话符合你的本意。这仍然比“编译通过”有意义得多。
:::

至于“单元测试可以取代强类型”这一论点，考虑强类型语言中常见的一种重构：修改某个函数的参数类型。在强类型语言里，只要改掉这个函数的声明，然后修复所有编译错误就行了。在弱类型语言里，“这个函数现在期望不同的数据”这一事实无法传播到调用点。单元测试也许能捕捉到一部分不匹配，但测试几乎总是一个概率性的过程，而不是确定性的过程。**测试是证明的拙劣替代品。**

## 类型是什么？

关于类型，最简单的直觉是：它们是**值的集合**。`Bool` 类型是由 `true` 和 `false` 组成的两元素集合。`Char` 类型是所有 Unicode 字符的集合，比如 `'a'` 或 `'ą'`。

::: info 数学小课堂：集合
**集合**（set）就是一堆东西放在一起，不计顺序、不计重复。里面的东西叫**元素**（element），记作 $x \in A$（“$x$ 属于 $A$”）。

- $\{\text{true}, \text{false}\}$ 是一个两元素集合；
- $\{0, 1, 2, 3, \dots\}$ 是自然数集合 $\mathbb{N}$，它有无穷多个元素；
- $\varnothing = \{\}$ 是**空集**，一个元素都没有；
- 只有一个元素的集合，如 $\{\star\}$，叫**单元素集**（singleton）。

集合 $A$ 的元素个数记作 $|A|$，例如 $|\{\text{true}, \text{false}\}| = 2$，$|\varnothing| = 0$。

在 Lean 里，“`x` 属于类型 `A`”写作 `x : A`。所以 `true : Bool` 就对应 $\text{true} \in \text{Bool}$。
:::

集合可以是有限的，也可以是无限的。`String` 类型就是一个无限集合的例子：它的元素是所有有限长的字符序列（在 Lean 里你可以用 `String.toList` 把一个字符串变成 `List Char`，它们本质上是同一回事）。

当我们声明 `x` 是一个 `Int` 时：

```lean
def x : Int := 42
```

我们是在说：它是整数集合中的一个元素。Lean 的 `Int`（以及 `Nat`）是无限集合，可以做任意精度的算术——`2 ^ 100` 不会溢出。Lean 也有对应机器类型的有限集合 `Int64`、`UInt64` 等，就像 Rust 的 `i64`、`u64`。

```lean
#guard (2 : Int) ^ 100 == 1267650600228229401496703205376    -- 任意精度，不溢出
#guard (2 : UInt8) * 200 == 144                             -- 机器整数：400 mod 256
```

有一些微妙之处，让“类型即集合”这种等同变得棘手。多态函数会涉及循环定义的问题；而且你不可能有一个“所有集合的集合”。但正如我承诺过的，我不会在数学上吹毛求疵。（如果你好奇 Lean 怎么处理“所有集合的集合”这个坑：答案就是上一章讲过的宇宙分层，`Type : Type 1 : Type 2 : …`，没有哪个类型包含它自己。）好消息是，有一个由集合构成的范畴，叫做 $\mathbf{Set}$，我们就用它。在 $\mathbf{Set}$ 中，对象是集合，态射（箭头）是函数。

$\mathbf{Set}$ 是一个非常特殊的范畴，因为我们真的可以窥视它的对象内部，并从中获得大量直觉。比如，我们知道空集没有元素；我们知道有特殊的单元素集；我们知道函数把一个集合的元素映射到另一个集合的元素——可以把两个元素映到同一个，但不能把一个元素映到两个；我们知道恒等函数把集合的每个元素映到它自身；等等。我们的计划是：逐渐**忘掉**所有这些信息，转而用纯范畴论的语言——也就是对象与箭头的语言——来表达所有这些概念。

### 底（⊥）：Haskell 的世界

在理想世界里，我们可以简单地说：Haskell 的类型就是集合，Haskell 的函数就是集合之间的数学函数。只有一个小问题：数学函数不执行任何代码——它只是“知道”答案。而 Haskell 的函数必须把答案**算**出来。如果答案能在有限步内得到——无论这个步数有多大——那都没问题。但有一些计算涉及递归，而递归可能永远不会终止。我们不能简单地在 Haskell 中禁止不终止的函数，因为区分终止和不终止的函数是**不可判定**的——这就是著名的停机问题。

::: info 数学小课堂：停机问题
图灵在 1936 年证明：**不存在**一个程序，能对任意输入的程序判断它会不会停机。思路是一个“说谎者悖论”：假设有这样的判定器 `halts(p)`，就可以写一个程序 `q`：“如果 `halts(q)` 说我会停，我就死循环；否则我就立刻停。”`q` 停不停都和判定器的结论矛盾。

注意，这并不是说“**没有任何**程序的终止性能被判定”——很多具体程序显然会停。它说的是：没有**万能**的判定方法。这一点对理解下面 Lean 的做法很关键。
:::

于是计算机科学家想出了一个绝妙的主意——或者说一个大号的“黑魔法”，取决于你的视角——给每个类型都扩充一个特殊的值，叫做**底**（bottom），记作 `_|_` 或 Unicode 的 $\bot$。这个“值”对应一个不会终止的计算。所以一个声明为 `Bool → Bool` 的 Haskell 函数，可能返回 `True`、`False` 或者 $\bot$——最后这个表示它永远不会结束。

有意思的是，一旦你接受了底作为类型系统的一部分，就可以方便地把每一种运行时错误都当成底，甚至允许函数显式地返回底。后者通常通过表达式 `undefined` 来实现：在 Haskell 中可以写 `f x = undefined`，它能通过类型检查，因为 `undefined` 求值为底，而底是**任何**类型的成员，包括 `Bool`。你甚至可以写成 `f = undefined`（不带 `x`），因为底也是类型 `Bool -> Bool` 的成员。

可能返回底的函数叫做**偏函数**（partial function），与之相对的是**全函数**（total function）：对每一个可能的参数都返回有效的结果。

由于底的存在，你会看到人们把 Haskell 的类型与函数构成的范畴称作 $\mathbf{Hask}$，而不是 $\mathbf{Set}$。从理论的角度看，这是无穷无尽的麻烦的根源，所以此刻我要挥起屠刀，终止这条推理路线。从实用的角度看，忽略不终止的函数和底、把 $\mathbf{Hask}$ 当作货真价实的 $\mathbf{Set}$ 来对待，是可以的。[^fastloose]

[^fastloose]: Nils Anders Danielsson、John Hughes、Patrik Jansson、Jeremy Gibbons，[《Fast and Loose Reasoning is Morally Correct》](http://www.cs.ox.ac.uk/jeremy.gibbons/publications/fast+loose.pdf)（“快而松的推理在道德上是正确的”）。这篇论文论证了为什么在大多数场合可以忽略底。

### 补充：Lean 的世界没有 ⊥

这正是 Lean 和 Haskell 分道扬镳、而且分得很漂亮的地方。Lean 是一门**严格求值**、**全函数**的语言：用 `def` 定义的每一个函数，都必须对每个输入在有限步内给出结果。Lean 的类型里**没有**额外的 $\bot$。

“等一下，”你会说，“停机问题不是说终止性不可判定吗？”没错——所以 Lean 不去判定**任意**程序的终止性，而是要求你**证明**你的程序会终止。大多数时候这个证明是自动的：如果递归调用的参数在结构上比原参数“小”（比如 `n + 1` 递归到 `n`，或者列表 `x :: xs` 递归到 `xs`），Lean 一眼就能看出来。这叫**结构递归**：

```lean
def factRec : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factRec n      -- 在 n 上递归：n 比 n + 1 小

#guard factRec 5 == 120
```

如果 Lean 看不出来，它就拒绝你的定义：

```lean no-check
def loop (n : Nat) : Nat := loop n
-- error: fail to show termination for
--   loop
-- ...
--   it is unchanged in the recursive calls
```

对于更复杂的递归，你可以用 `termination_by` 告诉 Lean“哪个量在每次递归时变小”，必要时再用 `decreasing_by` 亲手证明它确实变小。停机问题保证了总有一些会终止的程序 Lean 无法自动看出来——这时就轮到你出手证明。这是一笔很划算的交易：判定是不可能的，但**检查一个证明**是容易的。

::: info 数学小课堂：全函数与偏函数
- **全函数**：定义域里的**每一个**元素都有对应的值。$f(n) = n^2$ 在整数上是全函数。
- **偏函数**：有些元素没有对应的值。$f(x) = 1/x$ 在实数上是偏函数（$x = 0$ 时没有定义）；“求列表的第一个元素”在列表上是偏函数（空列表没有第一个元素）。

数学里说的“函数”默认指全函数。Rust 里处理偏函数的标准做法是改返回 `Option`：`v.first()` 返回 `Option<&T>`——这就把一个偏函数变成了一个到更大集合的全函数。Lean 的 `List.head?` 也是这样。
:::

那真正可能不终止的程序怎么办？比如著名的考拉兹（Collatz）猜想：反复“偶数除以 2、奇数乘 3 加 1”，是否总会到达 1？没人能证明，所以也没人能证明下面这个函数总会终止。Lean 让你用 `partial def` 来写它：

```lean
partial def collatz (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatz (n / 2)
  else 1 + collatz (3 * n + 1)

#eval collatz 27    -- 111（27 要走 111 步才到 1）
```

`partial def` 可以编译、可以运行，但它付出了两个代价，而这两个代价恰好就是 Lean 保持“类型即集合”的秘诀：

1. **`partial def` 在逻辑中是不透明的。** 编译器知道怎么运行 `collatz`，但在证明里，Lean 只知道“`collatz` 是**某个** `Nat → Nat` 的函数”，对它的具体行为一无所知。所以你可以 `#eval collatz 27` 得到 `111`，却**不能**用 `rfl` 证明 `collatz 27 = 111`：

```lean no-check
example : collatz 27 = 111 := rfl   -- 错误：Lean 不会在证明中展开 partial def
```

2. **返回类型必须是非空的。** 这一条非常精妙。如果允许 `partial def bad (n : Nat) : Empty := bad n`，那么 `bad 0` 就是空类型 `Empty` 的一个元素——而空类型本不该有元素，逻辑就崩溃了（下面讲 `Empty` 时你会明白为什么这等于证明了“假”）。所以 Lean 拒绝它：

```lean no-check
partial def bad (n : Nat) : Empty := bad n
-- error: failed to compile 'partial' definition `bad`, could not prove that the type
--   Nat → Empty
-- is nonempty.
```

只要返回类型有元素，逻辑上就总可以把 `partial def` 解释成“某个真正的全函数”，于是逻辑依然对应 $\mathbf{Set}$。

运行时错误呢？Haskell 把它们也算作底；Lean 的对应物是 `panic!`。它同样要求返回类型有一个默认值（`Inhabited` 实例）：运行时它会打印错误信息，而在逻辑中它就**等于**那个默认值。这和 Haskell 的 `f x = undefined`、`f = undefined` 一一对应：

```lean
def f₁ (_x : Bool) : Bool := panic! "未定义"
def f₂ : Bool → Bool := panic! "未定义"

example : (default : Bool) = false := rfl     -- Bool 的默认值是 false
```

最后，Lean 里最像 `undefined` 的东西是 `sorry`：它可以充当任何类型的任何值，让你先把程序框架搭起来。但 Lean 会对每一个用到 `sorry` 的声明发出警告，拒绝 `#eval` 它，并且这个“污点”会传染给所有依赖它的定理。（本书的代码校验脚本禁止任何 `sorry`。）

```lean no-check
def f₃ (x : Bool) : Bool := sorry   -- warning: declaration uses 'sorry'
```

::: tip Rust 视角：Rust 也有 ⊥，它叫 `!`
Rust 的 `panic!()`、`loop {}`、`std::process::exit(0)` 的类型都是 `!`（never 类型），它能被当成任何类型使用——`let x: bool = panic!();` 能通过编译。这就是 Haskell 的“底是任何类型的成员”。Rust 和 Haskell 一样无法排除不终止和 panic：任何 Rust 函数 `fn(bool) -> bool` 都可能 panic 或者死循环。所以严格地说，Rust 的类型与函数也不是 $\mathbf{Set}$。

Lean 的不同在于：`def` 定义的函数**保证**终止；`partial def` 和 `panic!` 被逻辑小心地“隔离”了起来。于是在 Lean 里，**类型与全函数真的构成 $\mathbf{Set}$ 的一个好模型**。我们不需要“快而松的推理”——我们的推理可以既严格又正确。
:::

## 为什么需要数学模型？

作为程序员，你对所用编程语言的语法和文法了如指掌。这些方面通常在语言规范的最开头就用形式化的记号描述清楚了。但语言的意义，也就是**语义**，要描述起来困难得多：它要多花很多页，很少足够形式化，而且几乎从来不完整。于是语言律师们争论不休，还催生了一整个家庭手工业：专门出书解读语言标准里的微妙细节。

描述语言语义的形式化工具是有的，但由于它们很复杂，大多只被用在简化过的学术语言上，而不是现实中的庞然大物级编程语言。其中一种工具叫**操作语义**（operational semantics），它描述程序执行的机制：定义一个形式化的、理想化的解释器。工业语言（比如 C++）的语义通常用非形式化的操作推理来描述，往往借助某种“抽象机”。

问题是，用操作语义证明程序的性质非常困难。要展示程序的某个性质，你基本上得让它在理想化的解释器里“跑一遍”。

程序员从不做形式化的正确性证明，这没关系。我们总是“认为”自己写的程序是对的。没有人坐在键盘前说：“哦，我就随便扔几行代码，看看会发生什么。”我们认为自己写的代码会执行某些动作，产生想要的结果。如果没有，我们通常会相当惊讶。这意味着我们确实在对自己写的程序进行推理，而且通常是通过在脑子里运行一个解释器来推理。只是要跟踪所有变量真的很难。计算机擅长运行程序——人类不擅长！要是我们擅长，就不需要计算机了。

但还有另一种选择。它叫做**指称语义**（denotational semantics），基于数学。在指称语义中，每个编程构造都被赋予其数学解释。有了它，如果你想证明程序的某个性质，只需证明一个数学定理。你可能觉得定理证明很难，但事实是，我们人类积累数学方法已经有几千年了，有大量现成的知识可以利用。而且，和职业数学家证明的那类定理相比，我们在编程中遇到的问题通常相当简单，甚至是平凡的。

来看阶乘函数在 Lean 里的定义（Lean 和 Haskell 一样，是很适合指称语义的语言）：

```lean
def fact (n : Nat) : Nat := (List.range' 1 n).prod
```

表达式 `List.range' 1 n` 是从 `1` 开始的 `n` 个连续整数组成的列表，也就是 `[1, 2, …, n]`；`List.prod` 把列表的所有元素乘起来。这和数学课本里的阶乘定义 $n! = \prod_{i=1}^{n} i$ 一模一样。再和一个命令式的版本比一比（原书用的是 C，这里用 Rust）：

```rust
fn fact(n: u64) -> u64 {
    let mut result = 1;
    let mut i = 2;
    while i <= n {
        result *= i;
        i += 1;
    }
    result
}
```

还用我多说吗？

好吧，我第一个承认这一拳打得有点廉价！阶乘函数有一个显而易见的数学指称。（Rust 程序员会抗议说可以写 `(1..=n).product()`——没错，而这恰恰说明函数式的写法是多么自然。）

既然有了数学指称，我们就能做数学：比如证明这个“课本式”的定义和前面那个递归定义 `factRec` 对所有 `n` 都相等。这就是“用证明数学定理来证明程序性质”的一个小样本：

```lean
theorem fact_eq_factRec (n : Nat) : fact n = factRec n := by
  induction n with
  | zero => rfl                                  -- 0! = 1：两边算出来都是 1
  | succ n ih =>                                 -- 假设对 n 成立（ih），证明对 n + 1 成立
    simp only [fact, factRec, List.range'_concat, List.prod_append] at *
    -- 现在目标是：(range' 1 n).prod * (1 + n) * 1 = (n + 1) * factRec n
    simp [ih, Nat.mul_comm, Nat.add_comm]
```

::: tip Lean 深入：数学归纳法与几个新策略
- `induction n with | zero => … | succ n ih => …`：对自然数做**数学归纳法**。先证 `n = 0` 的情形，再在“对 `n` 成立”（归纳假设 `ih`）的前提下证明“对 `n + 1` 成立”。
- `simp only [引理…]`：只用列出的引理和定义去化简目标。`List.range'_concat` 说 `[1, …, n+1] = [1, …, n] ++ [n+1]`，`List.prod_append` 说“拼接的积 = 积的乘积”。`at *` 表示同时化简目标和所有假设。
- `simp [ih, …]`：用归纳假设和交换律收尾。
- 如果你不想动脑，也可以让 Lean 对一个有限范围直接验算：`example : ∀ n < 8, fact n = factRec n := by decide`。但那只是“测试”，归纳法证明的才是“对一切 `n`”。
:::

```lean
example : ∀ n < 8, fact n = factRec n := by decide
```

机敏的读者也许会问：从键盘读取一个字符、通过网络发送一个数据包，它们的数学模型是什么？在很长一段时间里，这都是一个尴尬的问题，只能换来相当绕的解释。看起来，指称语义并不太适合相当多的重要任务——而这些任务对于写出有用的程序必不可少，用操作语义却能轻松应对。突破来自范畴论。Eugenio Moggi 发现，计算效应（computational effect）可以映射为**单子**（monad）。这是一个重要的发现：它不仅给指称语义带来了新生，让纯函数式程序更加实用，还为传统编程带来了新的启发。等我们发展出更多范畴论工具之后，我会再谈单子。

为编程建立数学模型的一个重要好处是：可以对软件的正确性进行形式化证明。当你写消费级软件时，这可能显得不那么重要；但在某些编程领域，失败的代价可能极其高昂，或者人命关天。即使是为医疗系统写 Web 应用，你也许也会欣慰于这样一个想法：标准库中的函数和算法都附带着正确性证明。（在 Lean 里，这不只是一个想法：核心库中就有成千上万条关于 `List`、`Nat`、`Array` 等的定理，比如 `List.length_append` 证明了拼接后的长度等于长度之和，我们刚才用到的 `List.prod_append` 也是其中之一。）

## 纯函数与脏函数

我们在 C++ 或任何其他命令式语言中称为“函数”的东西，和数学家所说的函数不是一回事。数学函数只是值到值的映射。

我们可以在编程语言中实现数学函数：这样的函数，给定一个输入值，就计算出输出值。计算一个数的平方的函数，大概会把输入值和自己相乘。每次调用它都会这样做，而且保证每次用同样的输入调用都产生同样的输出。一个数的平方不会随着月相变化。

此外，计算一个数的平方不应该有“给你的狗发一块美味零食”这种副作用。一个这样做的“函数”，很难被建模为数学函数。

在编程语言中，对同样的输入总是产生同样的结果、并且没有副作用的函数，叫做**纯函数**（pure function）。在 Haskell 这样的纯函数式语言里，所有函数都是纯的。Lean 也一样：普通的 `def` 都是纯函数，凡是要和外部世界打交道的计算（打印、读文件、取随机数……）都必须写在 `IO` 里，而这一点会**明明白白地写在类型上**：

```lean
def square (x : Int) : Int := x * x             -- 纯函数：Int → Int

def feedDog : IO Unit := IO.println "汪！给你一块零食。"   -- 副作用：类型是 IO Unit
```

`square` 的类型告诉你它只是一个映射；`feedDog` 的类型告诉你它是一个“会对世界做点什么”的动作。你不可能在一个类型为 `Int → Int` 的函数里偷偷喂狗。正因为如此，这类语言更容易赋予指称语义，也更容易用范畴论来建模。至于其他语言，总可以把自己限制在一个纯的子集里，或者单独对副作用进行推理。稍后我们会看到，单子如何让我们只用纯函数就能为各种效应建模。所以把自己限制在数学函数之内，我们其实什么都没失去。

::: tip Rust 视角：纯不纯，签名说了不算
在 Rust 里，`fn square(x: i64) -> i64` 完全可以在函数体里 `println!`、修改一个 `static` 变量、读取环境变量——签名对此一言不发。Rust 的所有权系统控制的是**谁能修改什么数据**（`&` vs `&mut`），而不是**能不能和外部世界打交道**。`const fn` 有点接近“纯”的意思，但限制要多得多。在 Lean 里，“纯”是默认，“不纯”必须在类型里出现 `IO`。
:::

## 类型的例子

一旦你意识到类型就是集合，就可以想出一些相当奇特的类型。比如，空集对应的类型是什么？不，它不是 C++ 的 `void`（也不是 Rust 的 `()`），尽管这个类型在 Haskell 里**确实**叫 `Void`。在 Lean 里它叫 `Empty`。这是一个没有任何值居住的类型。你可以定义一个接受 `Empty` 的函数，但你永远调用不了它。要调用它，你得提供一个 `Empty` 类型的值，而这样的值根本不存在。至于这个函数能返回什么，没有任何限制——它可以返回任何类型（尽管它永远不会返回，因为它没法被调用）。换句话说，它是一个在返回类型上多态的函数。Haskell 程序员管它叫 `absurd`；在 Lean 里，它叫 `Empty.elim`：

```lean
#check @Empty.elim        -- @Empty.elim : {C : Sort u_1} → Empty → C
```

我们自己写一遍也很简单：

```lean
def absurd' {α : Type} (e : Empty) : α := nomatch e
```

`nomatch e` 的意思是：“对 `e` 做模式匹配，但一个分支也不写”——因为 `Empty` 没有任何构造子，一个分支都不需要，所有情形都已覆盖。（`{α : Type}` 是任意类型，和上一章 `myId` 里的一样。）

这个名字并非巧合。类型和函数在逻辑上有更深层的解释，叫做**柯里–霍华德同构**（Curry–Howard isomorphism）。类型 `Empty` 代表“假”，而函数 `absurd` 的类型对应于命题“从假可以推出任何东西”，正如那句拉丁格言：*ex falso sequitur quodlibet*（“从谬误中可以推出一切”）。

::: info 数学小课堂：柯里–霍华德同构与 Lean 的 `False`
柯里–霍华德同构说：**命题就是类型，证明就是程序**。

| 逻辑 | 类型 |
|---|---|
| 命题 $P$ | 类型 `P` |
| $P$ 的一个证明 | 类型 `P` 的一个值 |
| $P \Rightarrow Q$（蕴含） | 函数类型 `P → Q` |
| 假（$\bot$） | 空类型 |
| 真（$\top$） | 单元素类型 |

“假”之所以是空类型，是因为“假”不该有证明，正如空类型没有值。

Lean 把这个同构做成了语言本身：它有一个专门放命题的宇宙 `Prop`。`Empty : Type` 是“数据层面的空类型”，而 `False : Prop` 是“命题层面的假”，两者都没有居民。对应地，`Empty.elim : Empty → C` 有一个命题层面的孪生兄弟 `False.elim : False → C`，以及更常用的 `absurd : a → ¬a → b`（“如果 `a` 成立而 `a` 又不成立，那什么都成立”）。上一章证明 `h ∘ (g ∘ f) = (h ∘ g) ∘ f` 时，我们写下的正是一个类型为“这个等式”的值。
:::

::: tip Rust 视角：Rust 的空类型
Rust 也能写空类型：`enum Void {}`——一个没有任何变体的枚举。对它的值可以写 `match v {}`，一个分支都不用写，和 Lean 的 `nomatch` 如出一辙。标准库里的 `std::convert::Infallible` 就是这样一个空枚举，`Result<T, Infallible>` 表示“这个操作不可能失败”。前面提到的 never 类型 `!` 也是空类型，`fn diverge() -> !` 的意思就是“这个函数永远不会正常返回”。
:::

接下来是对应单元素集的类型。这个类型只有一个可能的值。这个值就那么“存在着”。你可能一下子没认出来，但它就是 C++ 的 `void`，在 Rust 里更是一目了然：`()`。想想以它为参数、以它为返回值的函数。以 `void` 为参数的函数总是可以调用。如果它是纯函数，它总会返回同一个结果。这里有一个这样的函数（原书用 C 写作 `int f44() { return 44; }`）：

```rust
fn f44() -> i32 {
    44
}
```

你可能认为这个函数接受的是“空无”，但正如我们刚才看到的，一个接受“空无”的函数永远没法被调用，因为没有表示“空无”的值。那它到底接受什么呢？从概念上说，它接受一个哑元值，这个值永远只有一个实例，所以我们不必显式地提到它。不过在 Haskell 里——也在 Lean 和 Rust 里——这个值有一个符号：一对空括号 `()`。所以，出于一个有趣的巧合（还是说并非巧合？），调用“无参函数”在 C、Rust 和 Lean 中看起来一样：`f44()` 或 `f44 ()`。另外，Lean 中这个类型叫 `Unit`（读作“unit”，单位类型），它唯一的值写作 `()`（全名是 `Unit.unit`）。所以这是 Lean 版的函数：

```lean
def f44 : Unit → Int := fun () => 44

#guard f44 () == 44
```

这一行声明 `f44` 把类型 `Unit` 映射到类型 `Int`，并通过对 `Unit` 唯一的构造子 `()` 做模式匹配来定义它，产出数字 44。你通过提供 unit 值 `()` 来调用这个函数：`f44 ()`。

::: tip Rust 视角：`()` 就是 unit
Rust 的 `()` 和 Lean 的 `Unit` 是同一个东西：只有一个值的类型，值也写作 `()`。Rust 中“不返回任何东西”的函数 `fn log(msg: &str)` 实际上返回的就是 `()`，等价于 `fn log(msg: &str) -> ()`。你也可以写一个真正接受 unit 参数的函数：`fn f44_unit(_: ()) -> i32 { 44 }`，调用时写 `f44_unit(())`。
:::

注意，每个以 unit 为参数的函数，都等价于从目标类型中挑出一个元素（这里挑出的是 `Int` 中的 44）。实际上，你可以把 `f44` 看作数字 44 的另一种表示方式。这就是一个例子，说明我们可以用“谈论函数（箭头）”来代替“显式地提到集合的元素”。从 unit 到任意类型 $A$ 的函数，与集合 $A$ 的元素一一对应。

在 Lean 里，我们可以把这个“一一对应”精确地写出来：两个方向的转换互为逆运算。

```lean
/-- 元素 → 函数：把 a 变成“总是返回 a 的函数”。 -/
def pick {α : Type} (a : α) : Unit → α := fun () => a

/-- 函数 → 元素：把函数作用在唯一的输入 () 上。 -/
def unpick {α : Type} (f : Unit → α) : α := f ()

-- 先 pick 再 unpick，回到原来的元素
theorem unpick_pick {α : Type} (a : α) : unpick (pick a) = a := rfl

-- 先 unpick 再 pick，回到原来的函数
theorem pick_unpick {α : Type} (f : Unit → α) : pick (unpick f) = f := by
  funext u      -- 函数外延性：只需证明它们在每个输入 u 上相等
  cases u       -- u : Unit 只有一种可能：()
  rfl
```

::: tip Lean 深入：`funext` 与 `cases`
- `funext u`：要证明两个函数相等，只需证明它们对任意输入 `u` 给出相同的输出。执行之后，目标从 `pick (unpick f) = f` 变成 `pick (unpick f) u = f u`。
- `cases u`：对 `u` 的所有可能形状逐一讨论。`Unit` 只有一个构造子 `()`，所以只剩一种情形：`u` 就是 `()`。之后两边都化简成 `f ()`，`rfl` 收尾。
:::

那以 `void` 为返回类型的函数呢——在 Lean 里，就是以 unit 为返回类型的函数？在 C++ 里，这类函数是为了副作用而存在的；但我们知道，那不是数学意义上真正的函数。一个返回 unit 的纯函数什么也不做：它只是丢弃自己的参数。

从数学上看，从集合 $A$ 到单元素集的函数，把 $A$ 的每个元素都映到那个单元素集的唯一元素上。对每个 $A$，恰好存在**一个**这样的函数。下面是针对 `Int` 的这个函数：

```lean
def fInt (x : Int) : Unit := ()
```

给它任何整数，它都还你一个 unit。……不过 Lean 会立刻给你一个警告：参数 `x` 没被用到。秉承简洁的精神，Lean（和 Haskell、Rust 一样）允许你用通配符模式——下划线——来表示被丢弃的参数，这样你就不必为它发明一个名字。所以上面的定义可以改写为：

```lean
def fInt' : Int → Unit := fun _ => ()
```

注意，这个函数的实现不仅不依赖于传给它的值，甚至不依赖于参数的类型。

对任何类型都能用同一个公式实现的函数，叫做**参数多态**（parametrically polymorphic）函数。你可以用一个方程实现一整族这样的函数：用类型参数代替具体类型。从任意类型到 unit 类型的多态函数该叫什么名字呢？当然就叫 `unit`：

```lean
def unit {α : Type} : α → Unit := fun _ => ()
```

在 Rust 里你会这样写这个函数：

```rust
fn unit<T>(_: T) {}
```

（注意 Rust 的这个版本会**消耗**掉参数的所有权——丢弃参数在 Rust 里是一个看得见的动作：`drop`。）

“对每个 $A$，恰好有一个从 $A$ 到 unit 的函数”——“恰好一个”在 Lean 里可以证明：任何两个这样的函数都相等。

```lean
theorem toUnit_unique {α : Type} (f g : α → Unit) : f = g :=
  funext fun _ => rfl      -- 每个输入上，两边都是 ()
```

类似地，“从 `Empty` 到任何类型恰好有一个函数”也可以证明：存在性由 `Empty.elim` 给出，唯一性如下——

```lean
theorem fromEmpty_unique {α : Type} (f g : Empty → α) : f = g :=
  funext fun e => nomatch e    -- 根本没有输入需要检查
```

而从一个**有**元素的类型到 `Empty`，一个函数都没有：

```lean
theorem no_fun_to_empty (f : Bool → Empty) : False :=
  nomatch f true    -- 如果有这样的 f，f true 就是 Empty 的一个元素——不可能
```

这三条定理会在后面的章节里以“始对象”和“终对象”的名字重新登场。

类型分类学的下一位成员，是两元素集合。在 C++ 里它叫 `bool`，在 Lean 里可想而知叫 `Bool`。区别在于：C++ 的 `bool`（以及 Rust 的 `bool`）是内建类型，而在 Lean 中，它就是一个普通的定义。核心库里是这样写的（我们放进自己的命名空间重写一遍）：

```lean
namespace MyDefs
inductive Bool where
  | false
  | true
end MyDefs
```

（这个定义的读法是：`Bool` 要么是 `false`，要么是 `true`。`inductive` 用来定义一个由若干**构造子**组成的类型，相当于 Rust 的 `enum`。Lean 核心库把 `false` 写在前面，所以 `false` 是“第 0 个”构造子。）原则上，在 C++ 里也应该能把布尔类型定义为一个枚举，但 C++ 的 `enum` 暗地里是个整数。C++11 的 `enum class` 本可以用来代替，但那样你就得用类名来限定它的值，比如 `bool::true` 和 `bool::false`，更别提还得在每个用到它的文件里包含相应的头文件。

::: tip Rust 视角：`enum` 就是 `inductive`
在 Rust 里你可以写 `enum MyBool { False, True }`，它是一个真正的和类型，不会和整数悄悄互相转换（只能显式地 `as i32`）。用的时候要写 `MyBool::True`，除非 `use MyBool::*`——这和 C++ 的 `enum class` 一样，也和 Lean 一样：Lean 里写 `MyDefs.Bool.true`，或者在类型已知时简写成 `.true`。Rust 的 `enum` 还能带数据（`Option<T>`、`Result<T, E>`），Lean 的 `inductive` 也能，而且能力更强。
:::

以 `Bool` 为参数的纯函数，只是从目标类型中挑出两个值：一个对应 `true`，另一个对应 `false`。

到 `Bool` 的函数叫做**谓词**（predicate）。例如，Lean 的 `Char` 上就有 `Char.isAlpha`、`Char.isDigit` 这样的谓词。C 的 `<cctype>` 库里也定义了 `isalpha`、`isdigit` 等等，但它们返回的是 `int` 而不是布尔值（C++ 真正的谓词定义在 `std::ctype` 里，形如 `ctype::is(alpha, c)`、`ctype::is(digit, c)`）。Rust 的 `char::is_alphabetic`、`char::is_ascii_digit` 则老老实实地返回 `bool`。

```lean
#guard 'a'.isAlpha == true
#guard '7'.isDigit == true
#guard 'ą'.isAlpha == false     -- 注意：Lean 的 Char.isAlpha 只认 ASCII 字母
```

::: warning 易错点：ASCII 还是 Unicode？
Lean 的 `Char.isAlpha` 只判断 ASCII 字母 `a`–`z`、`A`–`Z`，所以 `'ą'.isAlpha` 是 `false`；而 Rust 的 `'ą'.is_alphabetic()` 是 `true`（它按 Unicode 判断），`is_ascii_alphabetic` 才只认 ASCII。同一个名字的谓词，在不同语言里可能是**不同的函数**——它们是 `Char → Bool` 这个集合里的不同元素。
:::

我们已经见过了 `Empty`、`Unit`、`Bool`。在这样小的有限类型之间，可以把所有函数一个不落地列出来。下面的组件就是干这个的。试着回答：从 `Bool` 到 `Bool` 有几个函数？从 `Unit` 到 `Bool` 呢？从 `Empty` 到 `Bool` 呢？从 `Bool` 到 `Empty` 呢？

<div class="ch-widget-host"><Ch1_2FunctionCounter /></div>

::: info 数学小课堂：为什么函数个数是 $|B|^{|A|}$？
要确定一个函数 $f : A \to B$，就要为 $A$ 的**每一个**元素选定它在 $B$ 中的去处。每个元素都有 $|B|$ 种选法，而且各自独立。根据乘法原理，总共有

$$\underbrace{|B| \times |B| \times \cdots \times |B|}_{|A| \text{ 个}} = |B|^{|A|}$$

种选法。几个值得细品的特例：

- $|B|^0 = 1$：从空集出发的函数恰有一个（“什么都不用选”也算一种选法），**哪怕 $B$ 也是空的**：$0^0 = 1$。
- $0^{|A|} = 0$（当 $|A| > 0$）：$A$ 中有元素却无处可去，所以一个函数也没有。
- $1^{|A|} = 1$：到单元素集的函数恰有一个。
- $|B|^1 = |B|$：从单元素集出发的函数和 $B$ 的元素一样多。

这也是后面会把函数类型 $A \to B$ 叫做**指数对象**、记作 $B^A$ 的原因（见 1.9）。
:::

## 挑战

1. 用你最喜欢的语言定义一个高阶函数（或者函数对象）`memoize`。这个函数接受一个纯函数 `f` 作为参数，返回一个行为和 `f` 几乎完全一样的函数，区别只在于：对每个参数，它只调用原函数一次，把结果存在内部，之后每次用同样的参数调用时，都直接返回存好的结果。通过观察性能，你可以区分记忆化后的函数和原函数。比如，试着记忆化一个需要很长时间求值的函数：第一次调用时你得等结果出来，但之后用同样的参数调用，结果应该立刻就出来。
2. 试着记忆化你的标准库里平时用来生成随机数的函数。行得通吗？
3. 大多数随机数生成器都可以用一个种子（seed）来初始化。实现一个函数：接受一个种子，用这个种子调用随机数生成器，返回结果。记忆化这个函数。行得通吗？
4. 下面这些函数中哪些是纯的？（原书是 C++ 函数，这里改写成了 Rust。）试着记忆化它们，观察多次调用时会发生什么：记忆化的和没记忆化的。
   1. 正文中的阶乘函数。
   2. 从标准输入读取一个字节：

      ```rust no-check
      fn getchar() -> Option<u8> { /* 从 stdin 读一个字节 */ }
      ```

   3. 打印问候语：

      ```rust no-check
      fn f() -> bool {
          println!("Hello!");
          true
      }
      ```

   4. 带内部状态的累加器：

      ```rust no-check
      static Y: AtomicI32 = AtomicI32::new(0);
      fn f(x: i32) -> i32 {
          Y.fetch_add(x, Ordering::SeqCst) + x   // y += x; return y;
      }
      ```

5. 从 `Bool` 到 `Bool` 一共有多少个不同的函数？你能把它们全部实现出来吗？
6. 画出一个范畴，它仅有的对象是类型 `Empty`、`Unit` 和 `Bool`，箭头对应这些类型之间所有可能的函数。用函数的名字标注箭头。

::: details 参考答案：第 1 题（Rust 与 Lean）
**Rust。** 用一个闭包捕获一张 `HashMap` 作为缓存。因为闭包要修改它捕获的缓存，返回类型是 `impl FnMut` 而不是 `impl Fn`：

```rust
use std::collections::HashMap;
use std::hash::Hash;

pub fn memoize<A, B, F>(f: F) -> impl FnMut(A) -> B
where
    A: Eq + Hash + Clone,
    B: Clone,
    F: Fn(A) -> B,
{
    let mut cache: HashMap<A, B> = HashMap::new();
    move |a: A| {
        if let Some(b) = cache.get(&a) {
            return b.clone();
        }
        let b = f(a.clone());
        cache.insert(a, b.clone());
        b
    }
}

fn slow_fib(n: u64) -> u64 {
    if n < 2 { n } else { slow_fib(n - 1) + slow_fib(n - 2) }
}

pub fn demo() {
    use std::time::Instant;
    let mut fast_fib = memoize(slow_fib);
    let t = Instant::now();
    println!("{}", fast_fib(40));            // 102334155
    println!("第一次：{:?}", t.elapsed());    // 约 0.2～1 秒
    let t = Instant::now();
    println!("{}", fast_fib(40));            // 102334155
    println!("第二次：{:?}", t.elapsed());    // 不到 1 微秒
}
```

**Lean。** 在 Lean 里，`memoize` 遇到了一个有意思的问题：一个纯函数 `α → β` 不能修改任何东西，可缓存恰恰需要“记住”之前的结果——这是一个副作用。所以诚实的 Lean 版本会把它写在类型里：`memoize` 返回一个 `IO` 中的函数，用一个可变引用 `IO.Ref` 存放 `Std.HashMap`：

```lean
def memoize {α β : Type} [BEq α] [Hashable α] (f : α → β) : IO (α → IO β) := do
  let cache ← IO.mkRef (∅ : Std.HashMap α β)     -- 新建一个空缓存
  return fun a => do
    match (← cache.get)[a]? with                   -- 查缓存
    | some b => return b                           -- 命中：直接返回
    | none =>
      let b := f a                                 -- 未命中：计算
      cache.modify (·.insert a b)                  -- 存起来
      return b

def slowFib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => slowFib n + slowFib (n + 1)

def memoDemo : IO Unit := do
  let fastFib ← memoize slowFib
  let t0 ← IO.monoMsNow
  IO.println (← fastFib 30)       -- 832040，要等一会儿
  let t1 ← IO.monoMsNow
  IO.println (← fastFib 30)       -- 832040，瞬间完成
  let t2 ← IO.monoMsNow
  IO.println s!"第一次 {t1 - t0} ms，第二次 {t2 - t1} ms"
```

（在线运行时加一行 `#eval memoDemo` 就能看到效果。）这里的 `[BEq α] [Hashable α]` 相当于 Rust 的 `A: Eq + Hash` 约束；`do` 记法、`←` 和 `IO` 会在讲单子的章节里详细解释，现在你可以把 `let x ← action` 读成 Rust 的 `let x = action?;`。

值得一提的是：既然 `f` 是纯的，记忆化在**语义上**是不可见的——`memoize f` 和 `f` 返回的值完全一样，只是快慢不同。这正是纯函数的好处：编译器、运行时可以放心地缓存、重排、并行化纯函数的调用，因为没有人能观察到区别。
:::

::: details 参考答案：第 2、3 题
**第 2 题：** 行不通。Rust 标准库没有随机数生成器（通常用 `rand` crate），我们用一个带全局状态的 xorshift 生成器来模拟。它的签名看起来像个函数 `fn() -> u64`，但每次调用的结果都不同——它不是纯函数。把它记忆化之后，你只会一遍又一遍地拿到**第一次**的那个“随机数”：

```rust
use std::cell::Cell;

thread_local! {
    static STATE: Cell<u64> = Cell::new(0x2545F4914F6CDD1D);
}

/// 不纯的“随机数函数”：每次调用都会修改全局状态。
pub fn random() -> u64 {
    STATE.with(|s| {
        let mut x = s.get();
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        s.set(x);
        x
    })
}

/// 第 3 题：纯的“由种子决定的随机数”——同样的种子，同样的结果。
pub fn random_from_seed(seed: u64) -> u64 {
    let mut x = seed ^ 0x9E3779B97F4A7C15;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    x
}

pub fn demo() {
    assert_ne!(random(), random());                          // 不纯：两次不一样
    assert_eq!(random_from_seed(42), random_from_seed(42));  // 纯：两次一样
}
```

在 Lean 里，这个问题甚至无法提出：取随机数的 `IO.rand 0 100` 类型是 `IO Nat`，而不是 `Unit → Nat`，所以你根本没法把它交给要求纯函数 `α → β` 的 `memoize`。类型系统替你回答了“行不行得通”。

**第 3 题：** 行得通。给定种子的随机数生成器是一个纯函数：同样的种子总是产生同样的“随机”序列。Lean 核心库正好提供了这样一个纯的生成器 `StdGen`：

```lean
/-- 用种子初始化生成器，取一个 0～1000 之间的随机数。纯函数！ -/
def randomFromSeed (seed : Nat) : Nat := (randNat (mkStdGen seed) 0 1000).1

example : randomFromSeed 42 = randomFromSeed 42 := rfl   -- 同样的种子，同样的结果
```

既然它是纯函数，对它使用第 1 题的 `memoize` 完全没问题，记忆化前后的行为（除了速度）毫无二致。
:::

::: details 参考答案：第 4 题
1. **阶乘：纯。** 记忆化毫无问题，只是变快了。
2. **`getchar`：不纯。** 它的结果取决于外部世界（用户敲了什么键）。记忆化之后，它只会读一次，此后一直返回第一次读到的字节。
3. **打印 `Hello!` 再返回 `true`：不纯。** 返回值虽然总是 `true`，但打印是副作用。记忆化之后，`Hello!` 只会打印一次。
4. **带 `static` 状态的累加器：不纯。** 同样的输入 `f(1)` 第一次返回 1，第二次返回 2……记忆化之后，它总是返回第一次的结果，行为完全变了。注意 Rust 不让你随便写 C++ 那样的 `static int y`：要么用原子类型 `AtomicI32`，要么用 `unsafe` 的 `static mut`——Rust 至少让“全局可变状态”变得显眼。

```rust
use std::sync::atomic::{AtomicI32, Ordering};

static Y: AtomicI32 = AtomicI32::new(0);

pub fn accum(x: i32) -> i32 {
    Y.fetch_add(x, Ordering::SeqCst) + x
}

pub fn hello() -> bool {
    println!("Hello!");
    true
}

pub fn getchar() -> Option<u8> {
    use std::io::Read;
    let mut buf = [0u8; 1];
    match std::io::stdin().read(&mut buf) {
        Ok(1) => Some(buf[0]),
        _ => None,
    }
}
```

在 Lean 里，这四个函数的**类型**就把答案写在了脸上：

```lean
-- 1. 纯函数：Nat → Nat
#check (fact : Nat → Nat)

-- 2. 读取一行输入：类型是 IO String，不是函数
def getLine : IO String := do
  let stdin ← IO.getStdin
  stdin.getLine

-- 3. 打印再返回 true：类型是 IO Bool
def hello : IO Bool := do
  IO.println "Hello!"
  return true

-- 4. 带状态的累加器：状态被显式地写进类型 StateM Int Int
def accum (x : Int) : StateM Int Int :=
  modifyGet fun y => (y + x, y + x)     -- 新状态 y + x，同时把它作为返回值

-- 从初始状态 0 出发，先 accum 1 再 accum 2：返回 3
#guard Id.run (((do let _ ← accum 1; accum 2) : StateM Int Int).run' 0) == 3
```

只有第 1 个是普通函数类型 `Nat → Nat`，可以交给 `memoize`。第 4 个很有启发性：`StateM Int Int` 本质上就是纯函数 `Int → Int × Int`（“旧状态 ↦ （返回值，新状态）”），状态被显式地传进传出，于是又变回了纯函数。这正是单子为副作用建模的方式，我们会在后面的章节详细展开。
:::

::: details 参考答案：第 5 题（用 `decide` 验证）
一共 $2^2 = 4$ 个：常值 `false`、恒等 `id`、取反 `not`、常值 `true`。

```lean
def allBoolFuns : List (Bool → Bool) :=
  [fun _ => false, fun b => b, fun b => !b, fun _ => true]

/-- 一个 Bool → Bool 函数完全由它的“真值表” (f false, f true) 决定。 -/
def table (f : Bool → Bool) : Bool × Bool := (f false, f true)

-- 列表里恰好有 4 个函数
example : allBoolFuns.length = 4 := by decide

-- 它们的真值表两两不同，所以这是 4 个不同的函数
example : allBoolFuns.map table = [(false, false), (false, true), (true, false), (true, true)] := by
  decide

-- 每一种可能的真值表都出现了，所以没有遗漏
example : ∀ x y : Bool, ∃ f ∈ allBoolFuns, table f = (x, y) := by decide
```

`decide` 策略的意思是：“这个命题是可以机械判定的，请直接算出它是真是假。”对于有限的 `Bool` 上的 `∀`、`∃`、列表成员关系、等式，Lean 都知道怎么判定，于是它把所有情况算了一遍。

上面的验证依赖于“函数由真值表决定”这一事实。我们也可以直接证明：**任何** `Bool → Bool` 的函数都是这四个之一。

```lean
theorem bool_fun_cases (f : Bool → Bool) :
    f = (fun _ => false) ∨ f = (fun b => b) ∨ f = (fun b => !b) ∨ f = (fun _ => true) := by
  -- 按 f false 和 f true 的值分四种情况
  cases h₁ : f false <;> cases h₂ : f true
  -- 每种情况选出对应的那个函数，再用 funext 逐点验证
  · left; funext b; cases b <;> simp [h₁, h₂]
  · right; left; funext b; cases b <;> simp [h₁, h₂]
  · right; right; left; funext b; cases b <;> simp [h₁, h₂]
  · right; right; right; funext b; cases b <;> simp [h₁, h₂]
```

这里的 `cases h₁ : f false` 对 `f false` 的值分情况讨论，并把结果记作假设 `h₁`；`<;>` 表示“对前一步产生的每个目标都执行后一步”；`left` / `right` 选择证明“或”的左边还是右边。
:::

::: details 参考答案：第 6 题
各对象之间的函数个数（$|B|^{|A|}$）：

| 从 \ 到 | `Empty` | `Unit` | `Bool` |
|---|---|---|---|
| `Empty` | 1（`id`，也是 `absurd`） | 1（`absurd`） | 1（`absurd`） |
| `Unit` | 0 | 1（`id`，也是 `unit`） | 2（`fun () => true`、`fun () => false`） |
| `Bool` | 0 | 1（`unit`） | 4（`id`、`not`、`const true`、`const false`） |

一共 11 支箭头。画出来是这样（`Empty` 和 `Unit` 上的自环既是恒等箭头，也分别是 `absurd` 和 `unit`）：

```diagram
E: (0, 0) "\mathtt{Empty}"
U: (4, 0) "\mathtt{Unit}"
B: (2, 2.8) "\mathtt{Bool}"
pad: (2, 3.35) ""
idE: E -> E "\mathrm{id}" loop=left
idU: U -> U "\mathrm{id}" loop=right
aU: E -> U "\mathrm{absurd}"
aB: E -> B "\mathrm{absurd}" side=right
tt: U -> B "\mathrm{true}" bend=-45 side=right
ff: U -> B "\mathrm{false}" side=left
un: B -> U "\mathrm{unit}" bend=-80 side=right
idB: B -> B "\mathrm{id}" loop=down
notB: B -> B "\mathrm{not}" loop=left
ctB: B -> B "\mathrm{const\,true}" loop=right
cfB: B -> B "\mathrm{const\,false}" loop=up
caption: 以 Empty、Unit、Bool 为对象、以它们之间全部 11 个函数为箭头的范畴。
```

注意几件事：从 `Empty` 出发到每个对象都恰有一支箭头；到 `Unit` 的箭头从每个对象出发都恰有一支；没有箭头指向 `Empty`（除了它自己的恒等箭头）。

在 Lean 中，表中的每个数字都能被验证。“恰有一个”我们已经在正文中证明过（`fromEmpty_unique`、`toUnit_unique`），“一个也没有”是 `no_fun_to_empty`。这里补上 `Unit → Bool` 恰有两个：

```lean
theorem unit_to_bool (f : Unit → Bool) :
    f = (fun () => true) ∨ f = (fun () => false) := by
  cases h : f ()          -- f () 要么是 false，要么是 true
  · right; funext u; cases u; exact h
  · left; funext u; cases u; exact h

-- 而且这两个确实不同
example : (fun () => true) ≠ (fun () => false : Unit → Bool) := by
  intro h
  have := congrFun h ()   -- 两边作用于 ()，得到 true = false
  simp at this
```
:::

## 本章小结

- 类型系统的价值在于**可复合性**：只有首尾对得上的函数才能接起来，类型越强，这种“对得上”就越能被机器检查。测试是证明的拙劣替代品。
- 最简单的直觉：**类型就是值的集合**。类型与函数构成的范畴就是（或者几乎就是）集合与函数的范畴 $\mathbf{Set}$。
- Haskell 为了容纳不终止的计算，给每个类型加了一个底值 $\bot$，于是它的范畴严格说来是 $\mathbf{Hask}$ 而非 $\mathbf{Set}$；Rust 的 `!`/`panic!` 也是同样的情形。
- Lean 用**终止性检查**保证 `def` 都是全函数；`partial def` 在逻辑中不透明且要求返回类型非空，`panic!` 在逻辑中等于默认值，`sorry` 会被标记。于是 Lean 的类型与全函数真的是 $\mathbf{Set}$ 的好模型。
- **指称语义**把程序解释为数学对象，使得“证明程序性质”变成“证明数学定理”——例如证明课本式的 `fact` 等于递归式的 `factRec`。
- **纯函数**：同样的输入总给出同样的输出，没有副作用。Lean 中纯是默认，副作用必须出现在类型里（`IO`、`StateM`……）。纯函数可以放心记忆化。
- `Empty`（空集，对应逻辑中的“假”）：从它到任何类型恰有一个函数 `Empty.elim`，从有元素的类型到它没有函数。
- `Unit`（单元素集）：到它的函数恰有一个（`unit`）；从它出发的函数 `Unit → A` 与 $A$ 的元素一一对应——这是“用箭头代替元素”的第一个例子。
- `Bool`（两元素集）：从它出发的函数就是挑两个值；到它的函数叫谓词。$A$ 到 $B$ 的函数共有 $|B|^{|A|}$ 个，可以用 `decide` 让 Lean 机械地验证小情形。
