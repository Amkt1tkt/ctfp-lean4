# 0.1 Lean 4 速成：写给 Rust 程序员

::: tip 关于本章
本章是中文 Lean 4 版**新增**的导读，原书没有对应章节。它的目标很具体：读完以后，你能读懂本书出现的**每一行** Lean 代码，
并且能自己动手改一改、证一证。它不是完整的 Lean 教程。想系统学习的话，章末列出了几本很好的免费书。
:::

你是一位 Rust 程序员。你已经习惯了和借用检查器讨价还价，习惯了 `Option` 和 `Result`，习惯了 trait、泛型和 `match`。
好消息是：这些习惯几乎全都能直接搬到 Lean 4 里来。Lean 4 同样是一门静态类型、严格求值、编译到原生代码的语言，
同样有代数数据类型、模式匹配和类似 trait 的“类型类”。

不同之处在于，Lean 的类型系统强大得多。强大到什么程度？你可以在类型里写下一个数学命题，比如“对所有列表 `xs`，
`xs.reverse.reverse = xs`”，然后写一段“程序”来证明它。编译器检查这段程序的类型，就等于检查了证明。
这正是本书选择 Lean 的原因：原书只能口头说“函子必须保持复合”，我们却可以把这条定律写进类型，并且**真的证明它**。

本章按下面的顺序展开：

| 部分 | 内容 | 第一次读时 |
|---|---|---|
| §1 | 安装、编辑器、在线运行、Unicode 输入 | 必读 |
| §2 ~ §9 | 用 Lean 写程序：定义、函数、结构体、归纳类型、模式匹配、递归、泛型 | 必读 |
| §10 ~ §12 | 类型类、命名空间、自定义记号 | 必读（类型类是重点） |
| §13 ~ §15 | 宇宙、命题即类型、tactic 证明 | 可以先略读，读到第 1.1 章的证明时再回来 |
| §16 ~ §17 | `Functor`、`Monad`、`do` 记法、`IO` | 读第 1.4、1.7 章前看一眼即可 |

每一节都有一个“Rust 视角”对照。先来一张全景图：点一下左边的主题，看看同一件事在 Rust 和 Lean 里分别怎么写。

<div><Ch0_1SyntaxCards /></div>

## 1 安装与工具

### 1.1 elan、lake、lean：对应 rustup、cargo、rustc

Lean 的工具链和 Rust 的几乎一一对应。如果你会用 `rustup` 和 `cargo`，下面这张表你一眼就懂：

| Rust | Lean 4 | 作用 |
|---|---|---|
| `rustup` | `elan` | 工具链版本管理器，按项目自动切换编译器版本 |
| `rust-toolchain.toml` | `lean-toolchain` | 项目固定使用的编译器版本，例如 `leanprover/lean4:v4.34.1` |
| `rustc` | `lean` | 编译器（同时也是证明检查器） |
| `cargo` | `lake` | 构建工具与包管理器 |
| `Cargo.toml` | `lakefile.toml`（或 `lakefile.lean`） | 项目配置 |
| `target/` | `.lake/` | 构建产物 |
| crates.io | [Reservoir](https://reservoir.lean-lang.org/) | 包索引 |
| rust-analyzer | Lean 语言服务器（内置于 `lean`） | 编辑器里的类型提示、报错、跳转 |

安装 `elan`（Linux / macOS）：

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Windows 用户以及不想碰命令行的读者，可以直接装 VS Code 插件（见下一小节），它会在第一次打开 `.lean` 文件时提示你一键安装 `elan`。

新建并运行一个项目，和 `cargo new` / `cargo run` 一样简单：

```bash
lake new hello        # 相当于 cargo new hello
cd hello
lake build            # 相当于 cargo build
lake exe hello        # 相当于 cargo run，输出 Hello, world!
```

`lake new` 生成的目录结构如下：

```text
hello/
├── lean-toolchain     # 固定 Lean 版本
├── lakefile.toml      # 项目配置：一个库 Hello，一个可执行文件 hello
├── Main.lean          # 可执行文件入口，里面有 def main : IO Unit
├── Hello.lean         # 库的根模块
└── Hello/
    └── Basic.lean     # 库的一个子模块
```

如果只想跑单个文件，不需要建项目：`lean Foo.lean` 会编译这个文件并打印所有 `#eval` 的结果和错误信息。

::: tip 本书使用的版本
本书所有代码都用 **Lean 4.34.1** 编译校验，**只用 Lean 核心库**，不依赖数学库 Mathlib。这意味着你在网上看到的一些
写法（例如 `ℕ`、`by_contra`、`∃!`）来自 Mathlib，在本书里不可用；需要它们的地方，我们会自己定义。
:::

### 1.2 VS Code 插件与 Infoview

在 VS Code 扩展市场搜索 **Lean 4**（发布者 `leanprover`）并安装。打开任意 `.lean` 文件，编辑器右侧会出现一个叫
**Infoview** 的面板（没出现的话，按 `Ctrl+Shift+Enter`，macOS 上是 `Cmd+Shift+Enter`）。它是你和 Lean 对话的窗口：

- **光标停在哪一行，Infoview 就显示那一行的信息**：`#eval` 的输出、`#check` 的类型、错误信息。
- **写证明时，它显示当前的“证明目标”（goal）**：已有哪些假设、还需要证明什么。这是写 tactic 证明时最重要的东西，§15 会详细讲。
- 出错的地方会画红色波浪线，和 rust-analyzer 一样；鼠标悬停可以看到类型和文档；`Ctrl` + 点击可以跳转到定义。

Lean 是“边写边检查”的：你不需要手动编译，敲完一行，语言服务器就已经把它检查完了。

### 1.3 不想安装？用 live.lean-lang.org

打开 [live.lean-lang.org](https://live.lean-lang.org/)，就得到一个浏览器里的 Lean 编辑器：左边写代码，右边就是 Infoview。
它适合做实验，也适合配合本书的“在线运行”按钮使用。注意它通常跑的是最新稳定版 Lean，和本书的 4.34.1 可能有细微差别；
万一遇到某个函数名找不到之类的问题，多半是版本差异。

### 1.4 本书的代码块与“在线运行”按钮

本书的 Lean 代码块分三种：

1. **普通代码块**：构建本书时，每一章里所有这样的代码块会**按顺序拼成一个文件**，交给 Lean 4.34.1 编译。
   所以你在正文里看到的每一段 Lean 代码都是能编译通过的，而且其中的 `#guard`、`example ... := rfl` 这些“断言”也都被机器检查过了。
2. **隐藏代码块**：有些章节开头需要一些前导定义（比如范畴的定义），为了不打断阅读，它们被藏了起来，但同样参与编译。
3. **标有“示意（不编译）”的代码块**：故意写错的反例、伪代码，或者给你填空的练习骨架。

把鼠标移到一个普通代码块上，右下角会出现 **“▶ 在线运行”** 按钮（触屏设备上它一直显示）。点击它，浏览器会打开
live.lean-lang.org，里面装着**这一块代码，以及本章在它之前的所有 Lean 代码**（包括隐藏的前导定义）。
这样无论你从哪一块点进去，代码都能独立编译。你可以在那里随意修改、把光标放到各处看 Infoview，弄坏了就回来再点一次。

关于注释的约定：`#eval double 3 -- 6` 里的 `-- 6` 是我们手写的“预期输出”；而 `#guard double 3 == 6` 是
**被编译器检查过**的断言，如果不成立，本书根本构建不出来。所以本书尽量用后者。

### 1.5 Unicode 输入

Lean 代码里到处是 `→`、`×`、`∘`、`α`、`∀` 这样的符号。不用担心，输入它们很简单：在 VS Code（以及 live.lean-lang.org）里，
**先敲反斜杠 `\`，再敲缩写，然后敲空格或 Tab**，缩写就会变成符号。例如敲 `\to` 加空格，得到 `→`。

| 符号 | 输入 | 含义 | ASCII 替代写法 |
|---|---|---|---|
| `→` | `\to` 或 `\r` | 函数类型、蕴涵 | `->` |
| `←` | `\l` 或 `\leftarrow` | `do` 中取出结果、`rw [← h]` | `<-` |
| `↔` | `\iff` 或 `\<->` | 当且仅当 | `<->` |
| `×` | `\x` 或 `\times` | 积类型 | `Prod α β` |
| `⊕` | `\oplus` | 和类型 | `Sum α β` |
| `∘` | `\comp`、`\circ` 或 `\o` | 函数复合 | `Function.comp g f` |
| `λ` | `\la` 或 `\fun` | 匿名函数（也可以写 `fun`） | `fun` |
| `α β γ δ` | `\a` `\b` `\g` `\de` | 希腊字母，常用作类型变量（注意 `\d` 是 `↓`） | 直接用 `A`、`B` 也行 |
| `η μ ε` | `\eta` `\mu` `\epsilon` | 单位、乘法、余单位（第三部分） | |
| `∀` | `\forall` 或 `\all` | 对所有 | `forall` |
| `∃` | `\exists` 或 `\ex` | 存在 | `Exists fun x => ...` |
| `∧` | `\and` | 并且 | `/\` |
| `∨` | `\or` | 或者 | `\/` |
| `¬` | `\not` 或 `\neg` | 非 | `Not p` |
| `≠` | `\ne` | 不等于 | `Ne a b` |
| `≤` `≥` | `\le` `\ge` | 小于等于、大于等于 | `<=` `>=` |
| `⟨ ⟩` | `\<` `\>` | 匿名构造子 | `Prod.mk a b` 等 |
| `⟶` | `\hom` 或 `\-->` | 本书中范畴的态射 | `Category.Hom a b` |
| `𝟙` | `\b1` | 本书中的恒等态射 | `Category.id a` |
| `⟹` | `\==>` | 本书中的自然变换 | `NatTrans F G` |
| `≅` | `\iso` 或 `\cong` | 同构 | |
| `⊢` | `\vdash` 或 `\|-` | Infoview 里“要证明的目标” | |
| `₁ ₂` | `\1` `\2`（或 `\_1`） | 下标，用在名字里，如 `h₁` | `h1` |
| `·` | `\.` 或 `\cdot` | 占位符 / tactic 分支 | `.` |

记不住也没关系：**在 VS Code 里把鼠标悬停在任何符号上，提示框会告诉你它的输入方式**。在本书里遇到陌生符号，
也可以查[附录 A 的符号速查表](/appendix/glossary#符号速查表)。

::: tip Rust 视角
Rust 的标识符也允许 Unicode，但没人这么干；Rust 的运算符是固定的一小撮。Lean 的文化正好相反：数学符号是一等公民，
你甚至可以自己定义新的中缀运算符（§12）。一开始会有点不适应，但读数学的时候，`g ∘ f` 远比 `compose(g, f)` 清楚。
:::

## 2 第一个 Lean 文件：`#eval`、`#check`、`#guard`、`example`

打开一个 `.lean` 文件（或者 live.lean-lang.org），敲下：

```lean
#eval 1 + 2                    -- 3
#eval "Hello, " ++ "Lean"      -- "Hello, Lean"
#eval [1, 2, 3].length         -- 3
#check 1 + 2                   -- 1 + 2 : Nat
#check "abc".length            -- "abc".length : Nat
#guard 1 + 2 == 3
example : 1 + 2 = 3 := rfl
```

逐行解释：

- **`#eval e`**：计算表达式 `e` 并显示结果。相当于一个随时可用的 REPL，结果显示在 Infoview 里（命令行下打印到终端）。
- **`#check e`**：显示 `e` 的类型，不计算。读作“`1 + 2` 的类型是 `Nat`”。冒号 `:` 在 Lean 里永远读作“的类型是”。
  这相当于在 rust-analyzer 里把鼠标悬停在表达式上。
- **`#guard b`**：断言布尔表达式 `b` 为真，否则编译报错。相当于一个在**编译期**执行的 `assert!`。
- **`example : P := 证明`**：一个匿名的“定理”，声明 `1 + 2 = 3` 并给出证明 `rfl`（reflexivity，“两边算出来一样”）。
  `example` 不会留下名字，专门用来写“检查一下这个是对的”。§14 会细讲它。

以 `#` 开头的是**编辑器命令**，它们不是程序的一部分，只是你向 Lean 提问的方式。还有几个偶尔会见到：`#print 名字`
（打印定义）、`#reduce e`（把表达式化简到底，比 `#eval` 更“符号化”）。

::: warning 易错点：`==` 与 `=`
`1 + 2 == 3` 是一个**布尔值**（`Bool`），可以计算出 `true` 或 `false`，类似 Rust 的 `==`。
`1 + 2 = 3` 是一个**命题**（`Prop`），它是一个需要被证明的陈述，不能直接“算”。两者用途不同：
`#guard` 和 `if` 里用 `==`，定理和 `example` 里用 `=`。§14 会解释为什么需要两种相等。
:::

::: tip Rust 视角
`#guard f 3 == 6` 大致相当于 Rust 里一个 `#[test] fn t() { assert_eq!(f(3), 6); }`，区别是 Lean 在你敲代码的同时就运行了它，
不用 `cargo test`。而 `example : f 3 = 6 := rfl` 更进一步：它不是“运行一次看看”，而是让类型检查器确认两边**按定义**相等。
:::

## 3 定义：`def`、`fun`、`let`

### 3.1 `def`

```lean
def double (n : Nat) : Nat := n * 2

def greeting : String := "你好，范畴论"

def add (x y : Nat) : Nat := x + y

#guard double 21 == 42
#guard add 2 3 == 5
#eval greeting                 -- "你好，范畴论"
```

对照 Rust：

```rust
fn double(n: u64) -> u64 { n * 2 }
fn add(x: u64, y: u64) -> u64 { x + y }
const GREETING: &str = "你好，范畴论";
```

几点区别：

- **参数写成 `(名字 : 类型)`**，返回类型写在参数后面的冒号之后，然后是 `:=` 和函数体。同类型的参数可以合写：`(x y : Nat)`。
- **函数体是一个表达式**，没有 `return`，也没有花括号和分号。Rust 里“块的最后一个表达式就是返回值”，Lean 里整个函数体就是那个表达式。
- **没有参数的 `def` 就是一个常量**，比如 `greeting`。
- **返回类型可以省略**，Lean 会推断：`def triple (n : Nat) := n * 3` 也行。但本书通常都写出来，便于阅读。

::: warning 易错点：`Nat` 不是 `u64`
`Nat` 是**任意精度的自然数**（0, 1, 2, …），不会溢出。但它没有负数，所以减法是“截断”的：`2 - 5 = 0`。
需要负数时用 `Int`。Lean 也有定宽整数 `UInt8`、`UInt64` 等，以及浮点数 `Float`、字符 `Char`、字符串 `String`、布尔值 `Bool`。
:::

```lean
#eval (2 : Nat) - 5    -- 0，自然数减法会截断
#eval (2 : Int) - 5    -- -3
```

`(2 : Nat)` 这种写法叫**类型标注**（type ascription）：告诉 Lean “这个 `2` 是 `Nat`”。数字字面量默认是 `Nat`，
需要别的类型时就这样标注，相当于 Rust 的 `2u64` 或 `2_i64`。

### 3.2 匿名函数 `fun`

```lean
#eval (fun x => x + 1) 5               -- 6
#eval (fun (x : Nat) => x * x) 7       -- 49
#eval [1, 2, 3].map (fun x => x * 10)  -- [10, 20, 30]
#eval [1, 2, 3].map (· * 10)           -- [10, 20, 30]
#guard [1, 2, 3].map (· + 1) == [2, 3, 4]
```

`fun x => x + 1` 就是 Rust 的闭包 `|x| x + 1`。也可以写成 `λ x => x + 1` 或 `fun x ↦ x + 1`，意思完全一样。
最后两行的 `(· * 10)` 是简写：`·` 是一个占位符，`(· * 10)` 就是 `fun x => x * 10`。`(· + ·)` 则是两个参数的 `fun x y => x + y`。

和 Rust 不同，Lean 的函数是**纯**的：没有可变状态，没有 `FnMut` 和 `FnOnce` 的区别，同样的输入永远得到同样的输出。
这一点在[第 1.2 章](/part1/02-types-and-functions)里会变得非常重要。

### 3.3 `let` 与 `if`

```lean
def sumOfSquares (a b : Nat) : Nat :=
  let a2 := a * a
  let b2 := b * b
  a2 + b2

#guard sumOfSquares 3 4 == 25

def classify (n : Nat) : String :=
  if n == 0 then "零"
  else if n % 2 == 0 then "偶数"
  else "奇数"

#guard classify 7 == "奇数"
```

`let x := e` 引入一个局部名字，和 Rust 的 `let x = e;` 一样不可变，只是不用写分号：换行就是分隔。
`if c then a else b` 是表达式，`else` 不能省（就像 Rust 中 `if` 作为表达式使用时那样）。

注意**缩进是有意义的**：函数体比 `def` 那一行缩进，`let` 们对齐。Lean 和 Python 一样对空白敏感，但规则宽松得多，
照着本书的格式写就不会出错。

注释有三种：`-- 行注释`、`/- 块注释 -/`，以及文档注释 `/-- 说明 -/`（写在定义前面，相当于 Rust 的 `///`）。

## 4 函数类型与柯里化

### 4.1 箭头是右结合的

问一下 Lean，`add` 的类型是什么：

```lean
#check add        -- add (x y : Nat) : Nat
#check @add       -- @add : Nat → Nat → Nat
#check add 2      -- add 2 : Nat → Nat
```

`Nat → Nat → Nat` 是什么意思？箭头 `→` 是**右结合**的，所以它等于 `Nat → (Nat → Nat)`：
一个函数，吃一个 `Nat`，**返回另一个函数**，那个函数再吃一个 `Nat`，返回 `Nat`。
所以 `add 2` 是完全合法的表达式，它是“加 2”这个函数：

```lean
def addTwo : Nat → Nat := add 2

#guard addTwo 40 == 42
#guard [1, 2, 3].map (add 10) == [11, 12, 13]
```

这种“多参数函数其实是一层层返回函数的函数”的做法叫作**柯里化**（currying），以逻辑学家 Haskell Curry 命名。
相应地，函数应用 `add 2 3` 是**左结合**的：它就是 `(add 2) 3`。函数应用不需要括号和逗号，空格就是“调用”。

函数应用的优先级**最高**：`double 3 + 1` 是 `(double 3) + 1 = 7`，而不是 `double 4`。要传复杂参数时加括号：`double (3 + 1)`。

```lean
#guard double 3 + 1 == 7
#guard double (3 + 1) == 8
```

::: tip Rust 视角
在 Rust 里要得到 `add 2` 这样的“部分应用”，你得手写一个返回闭包的函数：

```rust
fn add(x: u64) -> impl Fn(u64) -> u64 {
    move |y| x + y
}

fn demo() -> u64 {
    let add_two = add(2);
    add_two(40) // 42
}
```

在 Lean 里，所有多参数函数天生就是这样的，不需要任何额外代码。这也是为什么 Lean 的函数签名写作 `Nat → Nat → Nat`
而不是 `(Nat, Nat) → Nat`。
:::

当然，也可以让函数真的吃一个**有序对**（pair）。`Nat × Nat` 是积类型，相当于 Rust 的 `(u64, u64)`：

```lean
def addPair (p : Nat × Nat) : Nat := p.1 + p.2

#guard addPair (2, 3) == 5
#guard Function.uncurry add (2, 3) == 5          -- 把柯里化函数变成吃有序对的函数
#guard Function.curry addPair 2 3 == 5           -- 反过来
```

这两种形式之间可以来回转换（`Function.curry` 和 `Function.uncurry`），这个看似平凡的事实在[第 1.9 章](/part1/09-function-types)
会变成一个深刻的数学结论。

### 4.2 高阶函数与复合

函数可以作为参数，也可以作为返回值：

```lean
def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

#guard twice double 3 == 12
#guard twice (· + 10) 0 == 20
```

对照 Rust 的 `fn twice(f: impl Fn(u64) -> u64, x: u64) -> u64 { f(f(x)) }`。Lean 不需要 `impl Fn` 或泛型参数，
函数类型 `Nat → Nat` 本身就是一个普通的类型。

**函数复合**写作 `g ∘ f`（输入 `\comp`），读作“g 在 f 之后”：先做 `f`，再做 `g`。注意是**从右往左**读的，
因为 `(g ∘ f) x = g (f x)`，`f` 离 `x` 更近。这正是数学的习惯，也是本书从第一章起就要用的东西：

```lean
#guard (double ∘ (· + 1)) 3 == 8      -- 先加 1 得 4，再翻倍得 8
#guard ((· + 1) ∘ double) 3 == 7      -- 先翻倍得 6，再加 1 得 7
example : (double ∘ (· + 1)) 3 = double (3 + 1) := rfl
```

如果你更喜欢从左往右读，Lean 有管道运算符 `|>`：`x |> f |> g` 就是 `g (f x)`，类似 Rust 的方法链。
反方向的 `g <| f x` 等于 `g (f x)`，用来省括号。

```lean
#guard (3 |> (· + 1) |> double) == 8
#guard (double <| 3 + 1) == 8
```

## 5 `structure`：对比 Rust 的 `struct`

### 5.1 定义与构造

```lean
structure Point where
  x : Int
  y : Int
deriving Repr, BEq

def origin : Point := { x := 0, y := 0 }   -- 带字段名的写法
def p1 : Point := ⟨3, 4⟩                    -- 匿名构造子：按字段顺序
def p2 : Point := Point.mk 1 2              -- 显式调用构造函数

#eval p1                        -- { x := 3, y := 4 }
#eval p1.x                      -- 3
#eval { p1 with y := 10 }       -- { x := 3, y := 10 }
#guard p1 == ⟨3, 4⟩
```

对照 Rust：

```rust
#[derive(Debug, Clone, PartialEq)]
struct Point {
    x: i64,
    y: i64,
}

fn demo() -> Point {
    let p1 = Point { x: 3, y: 4 };
    Point { y: 10, ..p1 }
}
```

逐项对照：

- `structure Point where` 后面逐行列出字段，相当于 `struct Point { ... }`。
- `deriving Repr, BEq` 相当于 `#[derive(Debug, PartialEq)]`：`Repr` 让 `#eval` 能把它打印出来，`BEq` 提供 `==`。
  其他常用的还有 `DecidableEq`（可判定的相等，§14）、`Hashable`、`Inhabited`（相当于 `Default`）、`Ord`。
- 每个结构体自动得到一个构造函数 `Point.mk`，以及“投影”函数 `Point.x`、`Point.y`。`p1.x` 就是 `Point.x p1`。
- `⟨3, 4⟩`（输入 `\<` 和 `\>`）是**匿名构造子**：当 Lean 知道期望的类型时，它会自动调用对应的构造函数。
  这个记号在整本书里随处可见，不仅用于结构体，也用于证明（§14）。
- `{ p1 with y := 10 }` 是“复制并修改部分字段”，对应 Rust 的 `Point { y: 10, ..p1 }`。Lean 里一切都不可变，
  所以这是得到“修改后”结构体的唯一方式。

### 5.2 方法与点记号

Rust 用 `impl Point { fn ... }` 给类型加方法。Lean 的做法是：在名字 `Point.xxx` 下定义函数，然后就可以用点记号调用：

```lean
def Point.add (p q : Point) : Point := ⟨p.x + q.x, p.y + q.y⟩

def Point.normSq (p : Point) : Int := p.x * p.x + p.y * p.y

#guard p1.add p2 == ⟨4, 6⟩       -- 等价于 Point.add p1 p2
#guard p1.normSq == 25
```

`p1.add p2` 的规则是：`p1` 的类型是 `Point`，所以 Lean 去找 `Point.add`，并把 `p1` 填到第一个类型为 `Point` 的参数位置上。
这和 Rust 的 `self` 很像，只是没有 `&self`、`&mut self`、`self` 的区分（反正都不可变）。

### 5.3 带类型参数的结构体、默认值，以及“字段可以是证明”

结构体可以有类型参数，字段可以有默认值：

```lean
structure Pair (α β : Type) where
  fst : α
  snd : β
deriving Repr

structure Config where
  verbose : Bool := false
  level : Nat := 1
deriving Repr

#eval (Pair.mk 1 "one")          -- { fst := 1, snd := "one" }
#eval ({ level := 3 } : Config)  -- { verbose := false, level := 3 }
```

`Pair α β` 就相当于 Rust 的 `struct Pair<A, B> { fst: A, snd: B }`。Lean 内置的积类型 `α × β`（即 `Prod α β`）就是这样定义的，
它的值写作 `(1, "one")`，两个分量用 `.1`、`.2`（或 `.fst`、`.snd`）取出。

接下来是 Rust 做不到的事。结构体的字段不仅可以是数据，还可以是**证明**：

```lean
structure PosNat where
  val : Nat
  pos : val > 0          -- 这个字段是一个证明：val 大于 0

def three : PosNat := ⟨3, by decide⟩   -- 必须同时提供 3 和“3 > 0”的证明

#guard three.val == 3
```

`PosNat` 的值永远是正数，这件事由**类型**保证，而不是由运行时检查保证。你没法构造一个 `⟨0, _⟩`，因为你给不出 `0 > 0` 的证明。
（`by decide` 是一个 tactic，意思是“让 Lean 自己算一下这个命题是否成立”，§15 会讲。）

::: tip Rust 视角
Rust 里的惯用法是“newtype + 私有字段 + 检查参数的构造函数”：`struct PosNat(u64); impl PosNat { fn new(n: u64) -> Option<Self> }`。
这能防止别人构造出非法值，但“它是正数”这个事实只活在注释和程序员的脑子里，编译器并不知道。
在 Lean 里，这个事实就在类型里，后续代码可以直接**使用**它（例如证明除以 `val` 是安全的）。

本书会大量使用这个特性：一个“范畴”就是一个结构体，它的字段除了对象、态射、复合之外，还包括**结合律和单位律的证明**。
见[第 1.1 章](/part1/01-category)。
:::

## 6 `inductive`：对比 Rust 的 `enum`

### 6.1 枚举与带数据的变体

```lean
inductive Weekday where
  | monday | tuesday | wednesday | thursday | friday | saturday | sunday
deriving Repr, DecidableEq

inductive Shape where
  | circle (r : Float)
  | rect (w h : Float)
deriving Repr

#eval Weekday.friday            -- Weekday.friday
#eval Shape.rect 2 3            -- Shape.rect 2.000000 3.000000
```

`inductive` 就是 Rust 的 `enum`：

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Weekday { Monday, Tuesday, Wednesday, Thursday, Friday, Saturday, Sunday }

#[derive(Debug)]
enum Shape {
    Circle { r: f64 },
    Rect { w: f64, h: f64 },
}
```

每一行 `| 名字 参数...` 是一个**构造子**（constructor），对应 Rust 的一个变体。
构造子的全名是 `Weekday.friday`，相当于 Rust 的 `Weekday::Friday`。当 Lean 已经知道期望的类型时，
可以只写 `.friday`（前面带点），这一点比 Rust 方便。

构造子也可以写成“类型签名”的形式，这两种写法完全等价，本书两种都会用：

```lean
inductive Shape' where
  | circle : Float → Shape'
  | rect : Float → Float → Shape'
```

### 6.2 递归类型：不需要 `Box`

```lean
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr

def smallTree : Tree Nat := .node (.node .leaf 1 .leaf) 2 .leaf
```

对照 Rust，你必须用 `Box` 打破无限大小：

```rust
enum Tree<T> {
    Leaf,
    Node(Box<Tree<T>>, T, Box<Tree<T>>),
}
```

Lean 自动处理内存（引用计数，没有垃圾回收器停顿），所以递归类型直接写就行。

### 6.3 Lean 内置的归纳类型

你在 Rust 里熟悉的许多类型，在 Lean 里都是用 `inductive` 定义的普通类型：

| Lean | 构造子 | Rust 对应 | 说明 |
|---|---|---|---|
| `Bool` | `true`、`false` | `bool` | |
| `Nat` | `Nat.zero`、`Nat.succ n` | 无（大整数） | 自然数本身就是归纳类型：0，或者某个数的后继 |
| `Option α` | `none`、`some a` | `Option<T>` | |
| `Except ε α` | `.error e`、`.ok a` | `Result<T, E>` | 注意参数顺序：**错误类型在前** |
| `Sum α β`（`α ⊕ β`） | `.inl a`、`.inr b` | 自定义 `enum Either<A, B>` | 本书第 1.5、1.6 章的“余积” |
| `List α` | `[]`、`a :: as` | `Vec<T>`（但是链表） | `[1, 2, 3]` 是 `1 :: 2 :: 3 :: []` 的简写 |
| `Unit` | `()` | `()` | 只有一个值的类型 |
| `Empty` | （没有构造子） | `enum Void {}`、`!` | 没有任何值的类型 |

`Nat` 的定义值得多看一眼，它就两行：

```lean
namespace MyNat

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

end MyNat
```

一个自然数要么是零，要么是另一个自然数的后继。`3` 就是 `succ (succ (succ zero))`。
（Lean 在运行时会用高效的大整数表示 `Nat`，这只是它的逻辑定义。）这个定义方式马上就会和“归纳法证明”联系起来（§15）。

## 7 模式匹配：`match`

### 7.1 `match` 表达式

```lean
def Shape.area (s : Shape) : Float :=
  match s with
  | .circle r => 3.14159 * r * r
  | .rect w h => w * h

#eval (Shape.circle 1).area      -- 3.141590
#guard (Shape.rect 2 3).area == 6.0
```

和 Rust 的 `match` 一个样：

```rust
enum Shape { Circle { r: f64 }, Rect { w: f64, h: f64 } }

fn area(s: &Shape) -> f64 {
    match s {
        Shape::Circle { r } => 3.14159 * r * r,
        Shape::Rect { w, h } => w * h,
    }
}
```

### 7.2 直接“按情况定义”函数

更常见的写法是省略 `match s with`，直接在定义里列出各种情况。Lean 会自动为参数做匹配：

```lean
def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true      -- 一个分支可以列多个模式
  | _ => false                       -- _ 是通配符

#guard Weekday.sunday.isWeekend
#guard !Weekday.monday.isWeekend

def describe : Option Nat → String
  | none => "什么都没有"
  | some 0 => "零"
  | some n => s!"数字 {n}"

#guard describe (some 42) == "数字 42"
#guard describe none == "什么都没有"
```

`s!"数字 {n}"` 是字符串插值，相当于 Rust 的 `format!("数字 {n}")`。

可以同时匹配多个参数，模式也可以嵌套：

```lean
def bothZero : Nat → Nat → Bool
  | 0, 0 => true
  | _, _ => false

def firstTwo : List Nat → Option (Nat × Nat)
  | x :: y :: _ => some (x, y)       -- 至少两个元素
  | _ => none

#guard bothZero 0 0
#guard firstTwo [5, 6, 7] == some (5, 6)
#guard firstTwo [5] == none
```

对 `Nat` 还可以用 `n + 1` 这样的模式，意思是“某个数的后继”，`n` 会绑定到“前一个数”：

```lean
def pred' : Nat → Nat
  | 0 => 0
  | n + 1 => n

#guard pred' 10 == 9
```

### 7.3 穷尽性检查

和 Rust 一样，Lean 要求模式匹配**覆盖所有情况**。漏掉一个，编译器就会报错并告诉你漏了哪些：

```lean no-check
def bad : Weekday → Nat
  | .monday => 1
  | .tuesday => 2
-- error: Missing cases:
-- Weekday.wednesday
-- Weekday.thursday
-- ...
```

这不是吹毛求疵。在 Lean 里，函数必须对**每一个**输入都给出结果（叫作**全函数**，total function），
这是 Lean 能同时作为逻辑系统的前提之一。下一节的终止性检查也是出于同样的原因。

`fun` 也可以直接按情况匹配，`fun | 模式 => ...`：

```lean
#guard [0, 1, 2].map (fun | 0 => "零" | _ => "非零") == ["零", "非零", "非零"]
```

在 `do` 块里还有和 Rust `if let` 对应的 `if let some x := o then ... else ...`，用到时再说。

## 8 递归与终止性检查

### 8.1 结构递归

```lean
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#guard factorial 5 == 120

def Tree.size {α : Type} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

#guard smallTree.size == 2

def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

#guard sumList [1, 2, 3, 4] == 10
```

这些函数在递归调用时，参数都是原参数的“一部分”（`n` 是 `n + 1` 的一部分，`xs` 是 `x :: xs` 的一部分）。
这叫**结构递归**，Lean 能自动看出它一定会结束。

### 8.2 为什么要检查终止？

Rust 允许你写 `fn f(n: u64) -> u64 { f(n) + 1 }`，它会无限递归（直到栈溢出），编译器不管。Lean 会拒绝它：

```lean no-check
def loop (n : Nat) : Nat := loop n + 1
-- error: fail to show termination for
--   loop
-- ...
```

为什么这么严格？因为 Lean 也是一个**逻辑系统**。如果允许这个定义，我们就有了等式 `loop 0 = loop 0 + 1`，
两边同时减去 `loop 0`，得到 `0 = 1`。一个能证明 `0 = 1` 的系统就能证明任何事，也就毫无价值了。
所以，Lean 中的普通函数必须是**全函数**：对每个输入都在有限步内给出结果。

这对本书是好消息：在 Lean 里，类型就是集合，函数就是真正的数学函数，没有原书反复提到的“底”（⊥，即不终止的计算）
来捣乱。[第 1.2 章](/part1/02-types-and-functions)会详细讨论这一点。

### 8.3 不是结构递归时：`termination_by` 与 `decreasing_by`

有些递归一定会结束，但不是结构递归。很多时候 Lean 能自己找出理由：

```lean
def digits (n : Nat) : List Nat :=
  if n < 10 then [n] else digits (n / 10) ++ [n % 10]

#guard digits 2024 == [2, 0, 2, 4]
```

这里 Lean 自动证明了“在 `n ≥ 10` 的情况下，`n / 10 < n`”。当它自己想不出来时，你需要告诉它两件事：
用 `termination_by` 指出“每次递归都在变小的量”，用 `decreasing_by` 证明它确实变小了：

```lean
def gcd' : Nat → Nat → Nat
  | a, 0 => a
  | a, b + 1 => gcd' (b + 1) (a % (b + 1))
termination_by _ b => b                         -- 第二个参数每次都变小
decreasing_by exact Nat.mod_lt _ (by omega)     -- 证明：a % (b+1) < b+1

#guard gcd' 48 18 == 6
```

这是辗转相除法：第二个参数从 `b + 1` 变成了 `a % (b + 1)`，余数总小于除数，所以一定会降到 0。
`Nat.mod_lt` 是核心库里的定理“`x % y < y`（当 `y > 0` 时）”，`by omega` 证明了 `b + 1 > 0`。

### 8.4 逃生舱：`partial def`

如果你实在证明不了终止（或者它确实可能不终止），可以写 `partial def`：

```lean
partial def collatz (n : Nat) (steps : Nat := 0) : Nat :=
  if n ≤ 1 then steps
  else if n % 2 == 0 then collatz (n / 2) (steps + 1)
  else collatz (3 * n + 1) (steps + 1)

#guard collatz 27 == 111
```

（没人知道考拉兹序列是否对所有正整数都会回到 1，这是数学上著名的未解问题，Lean 当然也证明不了它会终止。）

`partial def` 的代价是：Lean 把它当作一个“黑箱”，可以运行，但**不能在证明里展开它**。这样就不会推出 `0 = 1` 了。
另外它的返回类型必须是“有值的”（`Inhabited`），因为 Lean 需要确信这个黑箱不会凭空造出一个不存在的值。
本书主要讨论的是能证明性质的全函数，所以 `partial def` 很少出现。

::: tip 补充：参数默认值与 `where`
上面 `collatz` 的 `(steps : Nat := 0)` 是**参数默认值**，调用时可以省略。另一个常见写法是用 `where` 定义辅助函数：

```lean
def reverseFast {α : Type} (xs : List α) : List α :=
  go xs []
where
  go : List α → List α → List α
    | [], acc => acc
    | y :: ys, acc => go ys (y :: acc)

#guard reverseFast [1, 2, 3] == [3, 2, 1]
```

`where` 后面的 `go` 只在 `reverseFast` 里面可见（全名是 `reverseFast.go`），相当于 Rust 里在函数体内定义的嵌套函数。
:::

## 9 多态与隐式参数

### 9.1 隐式参数 `{α : Type}`

```lean
def myId {α : Type} (x : α) : α := x

#eval myId 5               -- 5
#eval myId "hi"            -- "hi"
#check @myId               -- @myId : {α : Type} → α → α
#eval @myId Nat 5          -- 显式给出类型参数
#eval myId (α := Nat) 5    -- 按名字给出类型参数
```

对照 Rust：

```rust
fn my_id<T>(x: T) -> T { x }

fn demo() -> u32 {
    my_id::<u32>(5) // turbofish：显式给出类型参数
}
```

`{α : Type}` 用花括号括起来，表示它是**隐式参数**：调用时不用写，Lean 根据其他参数推断出来（`myId 5` 中 `α` 推断为 `Nat`）。
这和 Rust 的泛型参数 `<T>` 完全对应。要显式给出时，用 `@myId Nat 5`（`@` 让所有隐式参数变成显式的），
或者 `myId (α := Nat) 5`，后者相当于 Rust 的 turbofish `my_id::<u32>(5)`。

但这里有一个根本区别：在 Lean 里，**`α` 是一个普通的参数**，它的类型是 `Type`。类型本身就是值，可以传来传去。
`{α : Type}` 和 `(x : α)` 是同一种东西，只不过一个用花括号（自动推断），一个用圆括号（手动传入）。
你也可以把类型参数写成显式的：

```lean
def replicateOf (α : Type) (x : α) (n : Nat) : List α := List.replicate n x

#guard replicateOf Nat 7 3 == [7, 7, 7]
```

### 9.2 自动绑定的隐式参数

本书经常省略 `{α : Type}` 这样的声明，直接使用小写希腊字母：

```lean
def swap (p : α × β) : β × α := (p.2, p.1)

#check @swap               -- @swap : {α : Type u_1} → {β : Type u_2} → α × β → β × α
#guard swap (1, "a") == ("a", 1)
```

Lean 看到未声明的 `α`、`β`，会自动把它们当作隐式类型参数（这个特性叫 auto-bound implicit）。
你注意到 `#check` 显示的是 `Type u_1` 而不是 `Type`，这和“宇宙”有关，§13 会讲；现在可以把它当作 `Type` 来读。

### 9.3 类型也是值：类型构造器

既然类型是值，那么“输入类型、输出类型”的函数也就顺理成章了：

```lean
#check List                 -- List.{u} (α : Type u) : Type u
#check (List : Type → Type)
#check (Option : Type → Type)

def NatPair : Type := Nat × Nat
def Endo (α : Type) : Type := α → α   -- 从 α 到 α 的函数类型

def incr : Endo Nat := fun n => n + 1
#guard incr 41 == 42
```

`List` 本身不是一个类型，它是一个**类型构造器**：给它一个类型 `Nat`，它返回类型 `List Nat`。它的类型是 `Type → Type`。
在 Rust 里，`Vec` 不加 `<T>` 是不能单独出现的；在 Lean 里，`List` 可以单独出现、可以作为参数传递。
这一点在 §10.4 讲类型类时会变得极其重要。

类型甚至可以依赖于**值**，这叫**依值类型**（dependent type）。例如核心库的 `Vector α n` 是长度恰好为 `n` 的数组：

```lean
#check (#v[1, 2, 3] : Vector Nat 3)
```

`n` 是一个普通的 `Nat` 值，却出现在类型里。本书很少直接用到 `Vector`，但“类型依赖于值”的思想正是下文“命题即类型”的基础：
`∀ n : Nat, n + 0 = n` 就是一个依赖于 `n` 的类型。

## 10 类型类：`class` 与 `instance`

### 10.1 从 trait 说起

Rust 的 trait 描述“一个类型支持哪些操作”。比如“幺半群”（monoid，[第 1.3 章](/part1/03-categories-great-and-small)的主角）：
有一个单位元，有一个二元运算。

```rust
trait Monoid {
    fn empty() -> Self;
    fn op(self, other: Self) -> Self;
}

impl Monoid for u64 {
    fn empty() -> Self { 0 }
    fn op(self, other: Self) -> Self { self + other }
}

impl Monoid for String {
    fn empty() -> Self { String::new() }
    fn op(self, other: Self) -> Self { self + &other }
}

fn mconcat<M: Monoid>(xs: Vec<M>) -> M {
    xs.into_iter().fold(M::empty(), M::op)
}
```

Lean 里的对应物叫**类型类**（type class）：

```lean
namespace MyAlg

class Monoid (α : Type) where
  empty : α
  op : α → α → α

instance : Monoid Nat where
  empty := 0
  op := (· + ·)

instance : Monoid String where
  empty := ""
  op := (· ++ ·)

instance {α : Type} : Monoid (List α) where
  empty := []
  op := (· ++ ·)

def mconcat {α : Type} [Monoid α] (xs : List α) : α :=
  xs.foldr Monoid.op Monoid.empty

#guard mconcat [1, 2, 3, 4] == 10
#guard mconcat ["范", "畴", "论"] == "范畴论"
#guard mconcat [[1], [2, 3], []] == [1, 2, 3]

end MyAlg
```

（我们把它放在 `namespace MyAlg` 里，免得和别处的同名定义冲突，§11 会讲命名空间。）

逐项对照：

| Rust | Lean |
|---|---|
| `trait Monoid { ... }` | `class Monoid (α : Type) where ...` |
| `Self` | 类型类的参数 `α` |
| `impl Monoid for u64 { ... }` | `instance : Monoid Nat where ...` |
| 泛型约束 `M: Monoid` | **实例参数**（instance argument）`[Monoid α]` |
| `M::empty()` | `Monoid.empty`（类型由上下文推断） |
| 泛型 impl：`impl<T> Monoid for Vec<T>` | `instance {α : Type} : Monoid (List α)` |

方括号 `[Monoid α]` 是第三种参数（前两种是圆括号的显式参数和花括号的隐式参数）。它的意思是：
“调用者不用传，请编译器在已有的 `instance` 里**找一个** `Monoid α` 填进来。”这个过程叫**实例解析**，和 Rust 的 trait 解析一样发生在编译期。

### 10.2 实例只是值

一个让人豁然开朗的事实：类型类其实就是一个**结构体**，实例就是这个结构体的一个**值**，`[Monoid α]` 只是“自动填写的参数”。
所以，你完全可以手动构造一个实例，再手动传进去：

```lean
abbrev natMul : MyAlg.Monoid Nat := { empty := 1, op := (· * ·) }

#guard @MyAlg.mconcat Nat natMul [1, 2, 3, 4] == 24      -- 用乘法幺半群
#guard MyAlg.mconcat [1, 2, 3, 4] == 10                  -- 默认找到的是加法幺半群
```

（`abbrev` 和 `def` 一样是定义，区别是它告诉 Lean“需要时可以随意展开我”。手写的实例值通常用 `abbrev` 定义。）

自然数在加法下是幺半群，在乘法下也是。Rust 的“一致性规则”（coherence）规定一个类型对一个 trait 只能有一个 `impl`，
于是你不得不写 `struct Sum(u64)`、`struct Product(u64)` 这样的 newtype。Lean 没有这么严格，你可以有多个实例，
默认使用优先级最高的（通常是最后声明的），需要时显式指定。不过实践中，Lean 程序员也常用 newtype 来避免混淆。

### 10.3 定律可以写进类型类

Rust 的 trait 没法要求 `op` 满足结合律，你最多在文档里写一句“实现者必须保证……”。Lean 可以把定律写成类型类的字段：

```lean
namespace MyAlg

class LawfulMonoid (α : Type) extends Monoid α where
  empty_op : ∀ a : α, op empty a = a
  op_empty : ∀ a : α, op a empty = a
  op_assoc : ∀ a b c : α, op (op a b) c = op a (op b c)

instance : LawfulMonoid Nat where
  empty_op := Nat.zero_add
  op_empty := Nat.add_zero
  op_assoc := Nat.add_assoc

end MyAlg
```

`extends Monoid α` 表示“在 `Monoid` 的基础上再加几个字段”，类似 Rust 的 supertrait `trait LawfulMonoid: Monoid`。
新加的三个字段是**命题**（`∀ a : α, ...` 读作“对所有 α 中的 a，……”），要构造这个实例，就必须提供三条定律的**证明**。
这里我们直接用了核心库里现成的定理 `Nat.zero_add`（`0 + n = n`）等。如果你给 `String` 写了一个不满足结合律的 `op`，
你就永远构造不出它的 `LawfulMonoid` 实例。

本书的核心定义 `Category` 就是这样一个类型类：它有对象、态射、复合、恒等，**外加**单位律和结合律。见[第 1.1 章](/part1/01-category)。

### 10.4 重点：对“类型构造器”写类型类（Rust 缺少的 HKT）

现在来看本书最依赖、也最让 Rust 程序员羡慕的特性。

`Option` 和 `Vec` 都有 `map`：`Option<A>` 加一个函数 `A -> B` 得到 `Option<B>`，`Vec<A>` 同理。
在 Rust 里，你想把“有 `map` 的容器”抽象成一个 trait，就会撞墙：

```rust no-check
// 这不是合法的 Rust：Rust 没有“类型构造器的类型参数”
trait Functor<F<_>> {
    fn fmap<A, B>(fa: F<A>, f: impl Fn(A) -> B) -> F<B>;
}
```

问题在于，我们要抽象的不是某个类型 `Option<i32>`，而是**类型构造器** `Option` 本身。用 §9.3 的话说，
它的“类型”是 `Type → Type`。能对这种东西做抽象的能力叫**高阶类型**（higher-kinded types，HKT），Rust 没有。

在 Lean 里，`Type → Type` 只是又一个普通的类型，所以直接写就行：

```lean
namespace MyFunctor

class Functor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

instance : Functor List where
  map := List.map

instance : Functor Option where
  map g
    | none => none
    | some a => some (g a)

def doubleAll {f : Type → Type} [Functor f] (xs : f Nat) : f Nat :=
  Functor.map (· * 2) xs

#guard doubleAll [1, 2, 3] == [2, 4, 6]
#guard doubleAll (some 21) == some 42

end MyFunctor
```

看清楚 `class Functor (f : Type → Type)`：类型类的参数 `f` 不是类型，而是类型构造器。`instance : Functor List` 里的
`List` 也没有带参数。`doubleAll` 对**任何**函子都能用，无论它是列表、`Option`，还是你以后定义的树。
这个 `Functor` 正是[第 1.7 章](/part1/07-functors)的主角。

::: tip Rust 视角：GAT 能模拟到什么程度？
Rust 1.65 起稳定的泛型关联类型（GAT）可以部分模拟：

```rust
trait Functor {
    type Elem;
    type Mapped<B>;
    fn fmap<B>(self, f: impl FnMut(Self::Elem) -> B) -> Self::Mapped<B>;
}

impl<A> Functor for Option<A> {
    type Elem = A;
    type Mapped<B> = Option<B>;
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Option<B> {
        self.map(f)
    }
}

impl<A> Functor for Vec<A> {
    type Elem = A;
    type Mapped<B> = Vec<B>;
    fn fmap<B>(self, f: impl FnMut(A) -> B) -> Vec<B> {
        self.into_iter().map(f).collect()
    }
}
```

它能用，但很别扭：`impl` 是针对 `Option<A>` 这个具体类型写的，而不是针对 `Option` 本身；没有任何东西保证
`Mapped<B>` 和 `Self` 是“同一个容器”（你完全可以让 `Option<A>` 映射成 `Vec<B>`）；而函子定律更是无从表达。
在 Lean 里，这些问题都不存在，而且（见 §16）连函子定律都可以写进类型类。
:::

Lean 甚至可以更进一步：本书会对 `Type → Type → Type`（两个参数的类型构造器，比如 `Prod`，第 1.8 章的双函子）写类型类，
也会对“一族对象加上对象之间的态射类型”写类型类（`Category`）。类型类的参数可以是任何东西。

### 10.5 运算符也是类型类

Lean 的 `+`、`*`、`==`、`toString` 等都是由类型类提供的，就像 Rust 的 `std::ops::Add`、`PartialEq`、`Display`：

```lean
instance : Add Point where
  add := Point.add

#guard p1 + p2 == ⟨4, 6⟩

instance : ToString Point where
  toString p := s!"({p.x}, {p.y})"

#guard toString p1 == "(3, 4)"
```

| Rust trait | Lean 类型类 | 提供 |
|---|---|---|
| `Add`、`Mul` | `Add`、`Mul`（以及更一般的 `HAdd`、`HMul`） | `+`、`*` |
| `PartialEq` | `BEq` | `==` |
| `Eq` + 可判定性 | `DecidableEq` | `if a = b then ...`、`decide` |
| `PartialOrd`、`Ord` | `LT`、`LE`、`Ord` | `<`、`≤`、`compare` |
| `Debug` | `Repr` | `#eval` 的输出 |
| `Display` | `ToString` | `toString`、`s!"{x}"` |
| `Default` | `Inhabited` | `default` |
| `Hash` | `Hashable` | `hash` |

## 11 `namespace`、`open`、`section`、`variable`

### 11.1 命名空间

```lean
namespace Geometry

def unitArea : Nat := 1

namespace Inner
def secret : Nat := 42
end Inner

end Geometry

#guard Geometry.unitArea == 1
#guard Geometry.Inner.secret == 42

open Geometry in
#guard unitArea == 1        -- open ... in 只对紧跟的这一条命令生效
```

`namespace X ... end X` 相当于 Rust 的 `mod x { ... }`，`open X` 相当于 `use x::*`。区别：

- Lean 的命名空间只管**名字**，不管可见性；默认一切都是公开的（`private def` 可以把定义限制在当前文件内）。
- 命名空间可以随时重新打开、往里添加东西。事实上 `def Point.add` 就是在往命名空间 `Point` 里添加 `add`，
  这就是点记号的原理。
- `open X in 命令` 只在一条命令里打开 `X`，很适合临时使用。
- `open X (a b)` 只引入指定的名字，`open X hiding a` 引入除 `a` 之外的所有名字。

本书各章都把自己定义的东西放在命名空间里，例如 `MyAlg.Monoid`、`MyFunctor.Functor`，以免与 Lean 核心库同名的定义冲突。

### 11.2 `section` 与 `variable`

写一连串关于同一组变量的定义或定理时，每次都写 `{α β γ : Type} (f : α → β) (g : β → γ)` 很烦。`variable` 可以一次声明好：

```lean
section Composition

variable {α β γ : Type}
variable (f : α → β) (g : β → γ)

def compose' : α → γ := fun x => g (f x)

theorem compose'_apply (x : α) : compose' f g x = g (f x) := rfl

end Composition

#check @compose'     -- @compose' : {α β γ : Type} → (α → β) → (β → γ) → α → γ
```

`variable` 声明的变量，会被**自动加到用到它们的定义前面**作为参数（花括号的成为隐式参数，圆括号的成为显式参数）。
`section ... end` 限定这些 `variable` 的作用范围：出了 `end Composition`，`f`、`g` 就不再自动添加了。
`namespace` 里同样可以用 `variable`。

## 12 记号：`infixl`、`infixr`、`notation`

Lean 允许你定义自己的运算符。比如给函数复合定义一个新符号：

```lean
def compose {α β γ : Type} (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)

infixr:90 " ⊙ " => compose

#guard ((· + 1) ⊙ (· * 2)) 5 == 11
#guard ((· + 1) ⊙ (· * 2) ⊙ (· - 1)) 5 == 9
```

`infixr:90 " ⊙ " => compose` 的意思是：“把 `a ⊙ b` 解析为 `compose a b`，优先级 90，**右结合**”。

- **优先级**（precedence）决定不加括号时谁先结合：数字越大结合越紧。作为参考：`+` 是 65，`*` 是 70，`=` 是 50，
  `∧` 是 35，`∨` 是 30，`→` 是 25，函数应用最高（1024）。所以 `a + b * c` 是 `a + (b * c)`，`a = b ∧ c = d` 是 `(a = b) ∧ (c = d)`。
- **结合性**：`infixr`（右结合）让 `a ⊙ b ⊙ c` 成为 `a ⊙ (b ⊙ c)`；`infixl`（左结合）让它成为 `(a ⊙ b) ⊙ c`。
  `+`、`*` 是左结合的；`→`、`∘`、`::` 是右结合的。
- 还有 `prefix`（前缀）、`postfix`（后缀），以及最灵活的 `notation`：

```lean
notation "⟪" a ", " b "⟫" => Prod.mk b a     -- 一个故意“反着放”的有序对记号

#guard ⟪1, "x"⟫ == ("x", 1)
```

本书的公共前导（`lean/Prelude.lean`）定义了三个贯穿全书的记号：

```lean no-check
infixr:10 " ⟶ " => Category.Hom    -- a ⟶ b：从 a 到 b 的态射（输入 \hom）
infixr:80 " ⊚ " => Category.comp   -- g ⊚ f：g 在 f 之后（范畴中的复合）
notation "𝟙" => Category.id        -- 𝟙 a：a 上的恒等态射（输入 \b1）
```

读到[第 1.1 章](/part1/01-category)时，你会看到它们的完整定义。

::: tip Rust 视角
Rust 只能通过 `std::ops` 里的 trait 重载固定的那几个运算符，不能发明新符号，也不能改优先级。
Lean 的做法更接近“可编程的语法”。本书只在确实让公式更清楚的地方定义新记号，而且总会告诉你它展开成什么。
:::

## 13 宇宙：`Type`、`Type u`、`Sort`、`Prop`

### 13.1 类型的类型

既然类型是值，它们自己也该有类型。问问 Lean：

```lean
#check Nat          -- Nat : Type
#check Nat → Nat    -- Nat → Nat : Type
#check Type         -- Type : Type 1
#check Type 1       -- Type 1 : Type 2
#check Prop         -- Prop : Type
```

`Nat` 的类型是 `Type`，`Type` 的类型是 `Type 1`，`Type 1` 的类型是 `Type 2`……这一层层的 `Type`、`Type 1`、`Type 2`
叫作**宇宙**（universe）。为什么不干脆让 `Type : Type`？因为那会导致悖论（Girard 悖论），和集合论里“所有集合组成的集合”
引起的罗素悖论是一回事：一个“包含自己”的东西太大了，会让逻辑崩溃。所以 Lean 让每一层只能装下比它低的层。

日常编程里，你几乎只和 `Type` 打交道：`Nat`、`String`、`List Nat`、`Nat → Bool` 都住在 `Type` 里。

### 13.2 宇宙多态：`Type u`

麻烦出在“以类型为元素”的时候。§9.1 的 `myId` 要求 `α : Type`，那么能不能把类型 `Nat` 本身传给它？

```lean no-check
#check myId Nat
-- error: Application type mismatch: The argument
--   Nat
-- has type
--   Type
-- of sort `Type 1` but is expected to have type
--   ?m.1
-- of sort `Type` ...
```

不行：`myId Nat` 中 `α` 应该是 `Nat` 的类型，也就是 `Type`；但 `Type` 本身住在 `Type 1` 里，而 `myId` 只接受住在 `Type` 里的 `α`。
解决办法是让定义对宇宙层级也多态：

```lean
universe u

def idU {α : Type u} (x : α) : α := x

#check idU 5        -- idU 5 : Nat        （此时 u = 0）
#check idU Nat      -- idU Nat : Type     （此时 u = 1）
```

`universe u` 声明一个宇宙变量，`Type u` 表示“第 u 层宇宙”，`u` 可以是 0、1、2……（`Type` 就是 `Type 0` 的简写）。
§9.2 里 `#check @swap` 显示的 `Type u_1` 也是这么回事：自动绑定的类型参数会被自动赋予宇宙变量。

本书什么时候需要 `Type u`？最典型的是“类型与函数组成的范畴”：这个范畴的**对象**就是类型。
所以对象的类型是 `Type u`，而 `Type u` 本身住在 `Type (u+1)`。公共前导里的 `instance typeCategory : Category (Type u)`
就是这样写的。遇到 `Category.{u, v}` 这种花括号里带宇宙参数的写法，读作“对象在第 u 层，态射在第 v 层”即可，
不必深究。STYLE 上我们的原则是：能用 `Type` 就用 `Type`，确实需要时才引入 `Type u`。

### 13.3 `Sort` 与 `Prop`

最后一块拼图：Lean 还有一个特殊的宇宙 `Prop`，专门装**命题**（下一节的主角）。为了统一，Lean 用 `Sort` 给所有宇宙编号：

| `Sort` 写法 | 常用名 | 里面住着什么 |
|---|---|---|
| `Sort 0` | `Prop` | 命题，例如 `1 + 1 = 2`、`∀ n, n + 0 = n` |
| `Sort 1` | `Type`（即 `Type 0`） | 普通的数据类型：`Nat`、`String`、`List Nat` |
| `Sort 2` | `Type 1` | `Type` 本身，以及“以类型为元素”的东西 |
| `Sort (u + 1)` | `Type u` | |

你会在核心库的签名里看到 `Sort u`，比如 `@Function.comp : {α : Sort u_1} → ...`。它的意思是
“`α` 可以是任意宇宙里的东西，包括命题”。读的时候把它当成“任意类型”就好。

`Prop` 有两个特别之处，现在只需知道名字：

- **证明无关性**（proof irrelevance）：同一个命题的任意两个证明都被认为是相等的。我们只关心命题**是否**成立，不关心是**怎么**证的。
- 编译后，所有 `Prop` 里的东西都会被**擦除**，不占运行时空间。`PosNat` 里那个 `pos` 字段在运行时是不存在的。

::: tip Rust 视角
Rust 没有对应物：Rust 的类型不是值，你不能写一个“接受类型、返回类型”的普通函数，也不能问“`u32` 的类型是什么”。
最接近的是 Rust 的“零大小类型”和 `PhantomData`：它们只在编译期存在，运行时被擦掉，就像 `Prop` 中的证明一样。
:::

## 14 命题即类型、证明即程序

### 14.1 `theorem`：一个类型为命题的定义

```lean
#check 1 + 1 = 2               -- 1 + 1 = 2 : Prop
#check ∀ n : Nat, n + 0 = n    -- ∀ (n : Nat), n + 0 = n : Prop

theorem one_add_one : 1 + 1 = 2 := rfl

theorem add_zero_any : ∀ n : Nat, n + 0 = n := fun n => (rfl : n + 0 = n)
```

这就是 Lean 最核心的思想，叫作**命题即类型、证明即程序**（propositions as types，也叫 Curry–Howard 对应）：

- 一个**命题**就是一个**类型**（住在 `Prop` 里）。`1 + 1 = 2` 是一个类型。
- 一个命题的**证明**就是这个类型的一个**值**（一个程序）。`rfl` 是类型 `1 + 1 = 2` 的一个值。
- **检查证明**就是**类型检查**。Lean 编译通过，证明就是对的。

`theorem` 和 `def` 几乎一样，只是约定用于命题，并且 Lean 不会去“运行”它。

`rfl` 是什么？它是“相等的自反性”：`a = a` 的证明。Lean 检查 `1 + 1 = 2` 时，会把两边都**计算**一下，发现都是 `2`，
于是接受 `rfl`。这种“算一算就相等”叫**定义相等**（definitional equality）。

再看 `add_zero_any`。`∀ n : Nat, n + 0 = n` 的证明是一个**函数**：给它任意一个 `n`，它返回 `n + 0 = n` 的证明。
这就是“对所有”的含义：你能为每一个 `n` 都造出证明。（`n + 0` 按 `Nat` 加法的定义直接算出 `n`，所以 `rfl` 有效。
反过来的 `0 + n = n` 就没法直接算了，需要归纳法，§15 会证明它。）

### 14.2 逻辑连接词就是类型构造器

| 逻辑 | Lean | 它“是”什么 | 证明它需要 | Rust 中的类比 |
|---|---|---|---|---|
| 若 p 则 q | `p → q` | 函数类型 | 一个把 p 的证明变成 q 的证明的函数 | `fn(P) -> Q` |
| p 并且 q | `p ∧ q`（`And p q`） | 结构体，两个字段 | `⟨hp, hq⟩` | 元组 `(P, Q)` |
| p 或者 q | `p ∨ q`（`Or p q`） | 归纳类型，两个构造子 | `Or.inl hp` 或 `Or.inr hq` | `enum Either { L(P), R(Q) }` |
| 真 | `True` | 只有一个值的类型 | `trivial` | `()` |
| 假 | `False` | 没有值的类型 | （无法证明） | `!`、`enum Void {}` |
| 非 p | `¬p` | 就是 `p → False` | 一个“从 p 推出矛盾”的函数 | `fn(P) -> !` |
| p 当且仅当 q | `p ↔ q`（`Iff p q`） | 结构体，两个方向的函数 | `⟨p → q 的证明, q → p 的证明⟩` | `(fn(P)->Q, fn(Q)->P)` |
| 对所有 x，P x | `∀ x, P x` | 依值函数类型 | 一个对每个 x 返回 P x 证明的函数 | 泛型函数 `fn<T>`（粗略） |
| 存在 x，P x | `∃ x, P x`（`Exists`） | 依值有序对 | `⟨具体的 x, P x 的证明⟩` | `(witness, proof)` |
| a 等于 b | `a = b`（`Eq a b`） | 归纳类型，唯一构造子 `rfl` | `rfl`，或者一串推理 | 无 |

有了这张表，很多证明就是普通的函数式编程：

```lean
namespace Logic

-- p ∧ q → q ∧ p：拿到一个“有序对”，交换两个分量
theorem and_swap (p q : Prop) : p ∧ q → q ∧ p :=
  fun h => ⟨h.2, h.1⟩

-- p ∨ q → q ∨ p：对“枚举”做模式匹配
theorem or_swap (p q : Prop) : p ∨ q → q ∨ p :=
  fun h => match h with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq

-- 三段论：函数复合！
theorem imp_trans (p q r : Prop) : (p → q) → (q → r) → (p → r) :=
  fun hpq hqr hp => hqr (hpq hp)

-- 从假可以推出任何东西：对一个没有构造子的类型做模式匹配，不需要任何分支
theorem false_elim (p : Prop) : False → p :=
  fun h => nomatch h

-- ¬p 就是 p → False
theorem not_not_intro (p : Prop) : p → ¬¬p :=
  fun hp hnp => hnp hp

-- 存在性：给出一个具体的见证者，再加上证明
theorem exists_square : ∃ n : Nat, n * n = 49 := ⟨7, rfl⟩

-- 当且仅当：两个方向各给一个函数
theorem and_swap_iff (p q : Prop) : p ∧ q ↔ q ∧ p :=
  ⟨and_swap p q, and_swap q p⟩

end Logic
```

注意 `imp_trans` 的证明 `hqr (hpq hp)`：先用 `hpq` 把 `p` 的证明变成 `q` 的证明，再用 `hqr` 变成 `r` 的证明。
这就是函数复合 `hqr ∘ hpq`。三段论就是函数复合，这是范畴论与逻辑之间深刻联系的第一个迹象。

`nomatch h` 是对 `h : False` 做模式匹配：`False` 没有构造子，所以一个分支都不需要，Lean 就接受了。
这就是“从假命题可以推出任何结论”。对照 Rust：一个返回 `!` 的函数可以被当作返回任何类型来用。

::: tip 命名习惯
证明的名字通常以 `h` 开头（hypothesis，假设）：`hp : p` 读作“`hp` 是 `p` 的证明”，`hpq : p → q` 读作“`hpq` 是 p 蕴涵 q 的证明”。
定理名通常描述它说了什么，比如 `Nat.add_comm`（加法交换律）、`List.map_id`（对列表 map 恒等函数）。
:::

### 14.3 两种相等，以及可判定性

现在可以解释 §2 里的 `==` 和 `=` 了：

- `a == b : Bool` 是一个**计算**，由 `BEq` 类型类提供，可以在程序里用。
- `a = b : Prop` 是一个**命题**，是关于数学对象的陈述，需要**证明**。

为什么需要后者？因为很多相等关系没法计算。最典型的就是**函数的相等**：两个函数相等，是指它们对**每一个**输入都给出相同的输出。
对于 `Nat → Nat` 这样有无穷多个输入的函数，你不可能逐个比较，所以不存在函数的 `==`。但你可以**证明**它们相等：

```lean
example : (fun (x : Nat) => x + 0) = (fun x => x) := by
  funext x       -- 两个函数相等，只需对每个 x 证明它们的值相等
  rfl            -- x + 0 = x，按定义成立
```

本书中几乎所有的定律（函子定律、自然性条件、单子定律……）都是**函数之间的相等**，所以都用 `=` 表达，用证明来确立。

对那些**可以**计算的命题（比如 `2 ^ 10 = 1024`、`17 < 20`），Lean 通过类型类 `Decidable` 把它们和 `Bool` 联系起来：
`decide` tactic 直接算出命题的真假，`if a = b then ... else ...` 里的条件也可以是命题。`deriving DecidableEq` 就是在提供这种能力。

::: info 数学小课堂：构造性与经典逻辑
Lean 默认是**构造性**的：要证明“存在 x 使得 P x”，你得真的把 x 造出来（像 `exists_square` 那样给出 7）。
数学家平时用的**经典逻辑**还允许“排中律”：对任何命题 p，`p ∨ ¬p` 成立，即使你不知道是哪一边。Lean 也提供它，叫 `Classical.em`，
需要时可以用，但用了它的证明就不再能“算出”见证者了。本书的大部分证明都不需要它。[0.2 数学工具箱](/guide/math-toolkit)
会更详细地讨论各种证明方法。
:::

## 15 tactic 证明入门

### 15.1 什么是 tactic

上一节的证明是直接写出“证明项”（一个程序）。对于简单的命题这很优雅，但复杂一点就很难一口气写出来。
**tactic** 是另一种写证明的方式：你写 `by`，然后一步一步地发出指令，每条指令把“还需要证明的东西”（**目标**，goal）变换成更简单的目标，
直到什么都不剩。tactic 在背后替你拼出证明项。

打个比方：证明项像是直接写出一段完整的程序；tactic 像是在调试器里单步执行，每一步都能看到当前状态。

### 15.2 如何看 goal 状态

**这是学习 tactic 最重要的一件事：一定要看 Infoview。**

在 VS Code 或 live.lean-lang.org 里，把光标放在 `by` 之后，或者某一行 tactic 的末尾，Infoview 的“Tactic state”面板会显示：

```text
p q r : Prop
hpq : p → q
hqr : q → r
hp : p
⊢ r
```

横线 `⊢`（读作“推出”，turnstile）**之上**是你手里已有的东西：变量和假设（每行一个，`名字 : 类型`）。
`⊢` **之后**是当前要证明的目标。有多个目标时会依次列出，每个前面有 `case 名字` 标签。
全部证完时显示 **No goals**。如果证明结束了还有目标没解决，Lean 会报错 `unsolved goals` 并列出剩下的目标。

下面这个组件替你“单步执行”几个完整的证明。点“下一步”，左边高亮当前执行到的行，右边显示**执行完这一行之后**
Infoview 里的内容。这些 goal 状态都是由 Lean 4.34.1 实际生成的，和你在编辑器里看到的完全一样。

<div><Ch0_1TacticReplay /></div>

这几个证明的完整代码如下（可以点“在线运行”亲自把光标挪来挪去）：

```lean
namespace TacticDemo

theorem imp_trans (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  apply hqr
  apply hpq
  exact hp

theorem and_swap (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq =>
    constructor
    · exact hq
    · exact hp

theorem comp_assoc' {α β γ δ : Type} (f : α → β) (g : β → γ) (h : γ → δ) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by
  funext x
  show h (g (f x)) = h (g (f x))
  rfl

theorem not_not_bool (b : Bool) : (!(!b)) = b := by
  cases b
  · rfl
  · rfl

theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ]
    rw [ih]

end TacticDemo
```

### 15.3 常用 tactic 一览

下面每个 tactic 配一个最小的例子。建议你点开“在线运行”，在每一行末尾看看 goal 的变化。

**`rfl`**：目标是 `a = a`（或者两边按定义算出来相同）时，直接结束。

```lean
example : 2 + 3 = 5 := by rfl
example : [1, 2] ++ [3] = [1, 2, 3] := by rfl
```

**`intro`**：目标是 `p → q` 或 `∀ x, ...` 时，把前提（或变量）移到横线上面，作为假设。对应于证明项里的 `fun`。

```lean
example (p : Prop) : p → p := by
  intro hp       -- 现在有 hp : p，目标变成 p
  exact hp
```

**`exact e`**：如果你手里的某个表达式 `e` 的类型**恰好**是目标，就用它结束。

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  exact ⟨hp, hq⟩
```

**`apply f`**：目标是 `r`，而你有 `f : q → r`。`apply f` 的意思是“我打算用 f 来得到 r”，于是目标**倒退**成 `q`。
这是“从结论往回推”的推理方式。

```lean
example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  apply hqr      -- 要得到 r，只需得到 q
  apply hpq      -- 要得到 q，只需得到 p
  exact hp       -- p 正好有
```

**`constructor`**：目标是 `p ∧ q`（或 `p ↔ q`、某个结构体）时，把它拆成每个字段一个子目标。
多个子目标用 `·`（输入 `\.`）分别处理，每个 `·` 后面的缩进块负责一个目标。

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp     -- 第一个目标：p
  · exact hq     -- 第二个目标：q
```

**`cases h`**：对假设 `h`（或一个变量）按它的构造子分情况讨论。对 `h : p ∧ q`，只有一种情况，得到两个分量；
对 `h : p ∨ q`，有两种情况；对 `b : Bool`，有 `false` 和 `true` 两种情况。可以用 `with | 构造子 名字... =>` 给新变量起名。

```lean
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (b : Bool) : (b && true) = b := by
  cases b <;> rfl     -- `<;>`：对 cases 产生的每个目标都执行 rfl
```

**`induction n`**：对自然数（或列表、树等递归类型）做数学归纳法。它产生两个目标：基础情况 `zero`，
和归纳步骤 `succ`。在后者里你得到**归纳假设** `ih`（“对 k 成立”），要证明对 `k + 1` 成立。

```lean
theorem sumList_append (xs ys : List Nat) :
    sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]                    -- [] ++ ys = ys
  | cons x xs ih => simp [sumList, ih]; omega
```

（`ih : sumList (xs ++ ys) = sumList xs + sumList ys`，要证的是 `x :: xs` 的情形。）

**`rw [h]`**：重写（rewrite）。`h : a = b` 时，把目标里的 `a` 全部换成 `b`；`rw [← h]` 反过来把 `b` 换成 `a`。
重写完如果目标变成了 `c = c` 的形式，`rw` 会自动用 `rfl` 结束。

```lean
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  rw [h₁]        -- 目标变成 b = c
  rw [h₂]        -- 目标变成 c = c，自动结束
```

**`simp`**：化简器。它用一大批标记为 `@[simp]` 的引理（比如 `x + 0 = x`、`List.map id xs = xs`）反复重写目标，
直到无法再化简。很多“显然”的步骤交给它即可。`simp [f, h]` 额外使用定义 `f` 的展开和假设 `h`；
`simp only [...]` 只用你列出的引理；`simp at h` 化简假设 `h`。

```lean
example (xs : List Nat) : (xs ++ []).map id = xs := by simp

example (f : Nat → Nat) (h : ∀ x, f x = x + 1) : f (f 0) = 2 := by
  simp [h]
```

**`funext x`**：函数外延性（function extensionality）。要证明两个函数相等，只需证明它们在每个点 `x` 上的值相等。
这是本书最常用的 tactic 之一，因为范畴论中的定律多半是函数的相等。

```lean
example : (fun (n : Nat) => n * 2) = (fun n => n + n) := by
  funext n       -- 目标变成 n * 2 = n + n
  omega
```

**`calc`**：把一串等式（或不等式）写成数学课本上的“链式推导”，每一步单独给出理由。可读性极好。

```lean
example (a b c : Nat) (h₁ : a = b + 1) (h₂ : b = 2 * c) : a = 2 * c + 1 := by
  calc a = b + 1 := h₁
    _ = 2 * c + 1 := by rw [h₂]
```

`_` 代表上一行的右边。每一步 `:= ...` 后面是那一步的证明，可以是项，也可以是 `by` 加 tactic。

**`decide`**：对可以“算出来”的命题（有限的、可判定的），让 Lean 直接计算真假。

```lean
example : 2 ^ 10 = 1024 := by decide
example : ∀ b : Bool, (b || false) = b := by decide   -- 有限多种情况，逐个检查
```

**`omega`**：自动证明关于整数和自然数的**线性算术**（加、减、乘常数、比较大小）命题。凡是“小学算术显然成立”的不等式都交给它。

```lean
example (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega
example (n : Nat) : 2 * n + 3 > n := by omega
```

**`show t`**：把目标换一种（定义上相等的）写法显示出来。它不改变要证的东西，只是让你（和 Lean）更清楚地看到目标的形状，
常用于展开复合之类的定义。

```lean
example (f g : Nat → Nat) (x : Nat) : (g ∘ f) x = g (f x) := by
  show g (f x) = g (f x)
  rfl
```

**`unfold f`**：把目标里的 `f` 换成它的定义。

```lean
theorem double_eq_add (n : Nat) : double n = n + n := by
  unfold double       -- 目标变成 n * 2 = n + n
  omega
```

### 15.4 其他偶尔会见到的 tactic

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  left              -- 选择证明左边（right 选右边）
  exact hp

example : ∃ n : Nat, n + 2 = 5 := by
  exists 3          -- 给出见证者，剩下的目标 3 + 2 = 5 自动证明

example (p q : Prop) (h : p ∧ q) : q := by
  obtain ⟨hp, hq⟩ := h   -- 一步拆开结构
  exact hq

example (n : Nat) (h : n + 1 = 0) : False := by
  contradiction          -- 假设中有明显的矛盾（这里 n + 1 = 0 不可能）

example (a b : Nat) (h : a = b) : b = a := by
  have h' : b = a := h.symm   -- 引入一个中间结论
  exact h'
```

### 15.5 读不懂报错时

- **`unsolved goals`**：证明结束了，但还有目标没证完。看报错里列出的目标，继续写。
- **`type mismatch`**：你给的表达式类型和目标不一致。比较 Infoview 中的目标和你给的东西，常见原因是方向反了（`a = b` 与 `b = a`，用 `.symm` 或 `rw [← h]`）。
- **`simp made no progress`**：`simp` 什么都没做到。试试 `simp [相关定义]`，或者先 `unfold`。
- **`omega could not prove the goal`**：目标不是线性算术，或者需要先把某个定义展开。

最好的学习方式是动手。如果想系统练习 tactic，强烈推荐 [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)：
它用游戏的方式，从零开始带你用 Lean 证明自然数的加法、乘法定律。

## 16 `Functor`、`Monad` 与 `do` 记法

### 16.1 Lean 自带的 `Functor`

§10.4 我们自己写了一个 `Functor`。Lean 核心库里有一个几乎一样的，名字就叫 `Functor`，方法叫 `Functor.map`，
中缀写法是 `<$>`：

```lean
#guard (· + 1) <$> [1, 2, 3] == [2, 3, 4]
#guard (· + 1) <$> some 1 == some 2
#guard ((· + 1) <$> (none : Option Nat)) == none
#guard Functor.map toString [1, 2] == ["1", "2"]
```

`f <$> x` 就是“把 `f` 作用到容器 `x` 里面的值上”，对应 Rust 的 `Option::map`、`Iterator::map`。
Lean 还有 `LawfulFunctor` 类型类，它把**函子定律**作为字段：`id <$> x = x`，以及 `(g ∘ f) <$> x = g <$> (f <$> x)`。

```lean
#check @LawfulFunctor.id_map     -- id <$> x = x
example (o : Option Nat) : id <$> o = o := id_map o
```

函子是什么、为什么这两条定律重要，是[第 1.7 章](/part1/07-functors)的内容。

### 16.2 `Monad`：`pure` 与 `>>=`

`Monad` 类型类有两个基本操作：

- `pure : α → m α`：把一个普通值放进“容器”。对 `Option` 来说就是 `some`，对应 Rust 的 `Some(x)` / `Ok(x)`。
- `bind`，写作 `x >>= f`：取出 `x` 里的值，交给返回容器的函数 `f`。对 `Option` 来说，`x` 是 `none` 时直接返回 `none`。
  这正是 Rust 的 `Option::and_then`。

```lean
def safeDiv (a b : Nat) : Option Nat :=
  if b == 0 then none else some (a / b)

#guard (some 100 >>= fun x => safeDiv x 5) == some 20
#guard (some 100 >>= fun x => safeDiv x 0) == none
#guard (none >>= fun x => safeDiv x 5) == none
```

### 16.3 `do` 记法：Lean 的 `?`

一连串的 `>>=` 写起来很啰嗦，于是有了 `do` 记法：

```lean
def compute (a b c : Nat) : Option Nat := do
  let x ← safeDiv a b      -- 如果是 none，整个函数立刻返回 none
  let y ← safeDiv x c
  return x + y

#guard compute 100 5 2 == some 30
#guard compute 100 0 2 == none
```

对照 Rust：

```rust
fn safe_div(a: u64, b: u64) -> Option<u64> {
    if b == 0 { None } else { Some(a / b) }
}

fn compute(a: u64, b: u64, c: u64) -> Option<u64> {
    let x = safe_div(a, b)?;
    let y = safe_div(x, c)?;
    Some(x + y)
}
```

`let x ← e`（输入 `\l` 得到 `←`）几乎就是 Rust 的 `let x = e?;`：取出成功的值，失败就提前返回。`return v` 相当于 `Some(v)`。
区别在于，Rust 的 `?` 只对 `Option` 和 `Result`（以及实现了 `Try` 的类型）有效，而 Lean 的 `do` 对**任何单子**都有效：
`Option`、`Except`、状态单子、`IO`……甚至你自己定义的单子。这种统一性就是[第 3.4 章](/part3/04-monads-programmers-definition)要讲的故事，
而它的数学根源在[第 1.4 章 Kleisli 范畴](/part1/04-kleisli-categories)就已经埋下了。

`Except ε α` 对应 Rust 的 `Result<α, ε>`，`throw e` 对应 `return Err(e)`：

```lean
def parseAge (s : String) : Except String Nat := do
  let some n := s.toNat? | throw s!"“{s}” 不是数字"
  if n > 150 then throw s!"{n} 岁？不太可能"
  return n

#eval parseAge "42"       -- Except.ok 42
#eval parseAge "abc"      -- Except.error "“abc” 不是数字"
#guard (parseAge "42").toOption == some 42
#guard (parseAge "300").toOption == none
```

`let some n := e | 失败时做什么` 是 Rust `let Some(n) = e else { ... };`（let-else）的对应物。

### 16.4 `Id.run do`：在纯函数里写“命令式”代码

`do` 记法还支持 `let mut`、`for` 循环、提前 `return`。配合“什么效果都没有”的单子 `Id`，你可以在纯函数里写出命令式风格的代码：

```lean
def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n+1] do      -- [0:n+1] 是 0 到 n 的范围，类似 Rust 的 0..=n
    s := s + i
  return s

#guard sumTo 100 == 5050
```

`let mut` 看起来像可变变量，但它只是语法糖：Lean 把它翻译成一系列不可变的绑定。函数依然是纯的。

## 17 `IO` 与 `main`

和 Rust 一样，可执行程序的入口是 `main`：

```lean
def main : IO Unit := do
  IO.println "你好，范畴论！"
  let xs := [3, 1, 2]
  IO.println s!"排序前：{xs}，排序后：{xs.mergeSort}"
  for i in [1, 2, 3] do
    IO.println s!"第 {i} 行"

#eval main
```

`main` 的类型是 `IO Unit`：一个“会执行输入输出、最后返回 `()`”的动作。`IO` 是一个单子，所以用 `do` 记法串联各个动作。
在编辑器里 `#eval main` 会直接运行它，输出显示在 Infoview 中；在 `lake` 项目里则用 `lake exe 名字` 运行。

读取输入、读写文件也都在 `IO` 里：

```lean
def greet : IO Unit := do
  let stdin ← IO.getStdin
  IO.print "你叫什么名字？"
  let name ← stdin.getLine
  IO.println s!"你好，{name.trimAscii}！"
```

（我们没有 `#eval greet`，因为在构建本书时没有人来敲键盘。）

`main` 也可以接收命令行参数并返回退出码：`def main (args : List String) : IO UInt32`，相当于 Rust 的
`std::env::args()` 加 `std::process::exit`。

::: tip Rust 视角：效果写在类型里
在 Rust 里，`fn f(x: u64) -> u64` 可能偷偷打印日志、读文件、改全局变量，签名上看不出来。在 Lean 里，
`f : Nat → Nat` **保证**没有任何副作用；想做输入输出，类型就必须是 `Nat → IO Nat`。这让“纯函数”成为一个可以由编译器检查的性质。
原书[第 1.2 章](/part1/02-types-and-functions)和[第 3.5 章](/part3/05-monads-and-effects)会讨论这件事的意义：
纯函数才能构成范畴，而副作用可以用单子优雅地表达。
:::

## 18 速查表：Rust ↔ Lean

| Rust | Lean 4 | 本章 |
|---|---|---|
| `fn f(x: u64) -> u64 { x + 1 }` | `def f (x : Nat) : Nat := x + 1` | §3 |
| `\|x\| x + 1` | `fun x => x + 1` 或 `(· + 1)` | §3 |
| `let y = x * 2;` | `let y := x * 2` | §3 |
| `f(a, b)` | `f a b` | §4 |
| `impl Fn(A) -> B` | `α → β` | §4 |
| `(a, b)`、`p.0` | `(a, b)`、`p.1` | §4 |
| `struct P { x: i64 }` | `structure P where x : Int` | §5 |
| `P { x: 1 }`、`P { x: 2, ..p }` | `{ x := 1 }` 或 `⟨1⟩`、`{ p with x := 2 }` | §5 |
| `impl P { fn m(&self) }` | `def P.m (p : P) ...`，调用 `p.m` | §5 |
| `#[derive(Debug, PartialEq)]` | `deriving Repr, BEq` | §5 |
| `enum E { A, B(u64) }` | `inductive E where \| a \| b (n : Nat)` | §6 |
| `E::A` | `E.a` 或 `.a` | §6 |
| `Option<T>`、`Result<T, E>` | `Option α`、`Except ε α` | §6 |
| `match x { P => e, _ => d }` | `match x with \| p => e \| _ => d` | §7 |
| `format!("{x}")` | `s!"{x}"` | §7 |
| `fn id<T>(x: T) -> T` | `def id {α : Type} (x : α) : α` | §9 |
| `id::<u32>(5)` | `@id Nat 5` 或 `id (α := Nat) 5` | §9 |
| `trait T { ... }` | `class T (α : Type) where ...` | §10 |
| `impl T for X { ... }` | `instance : T X where ...` | §10 |
| `fn g<A: T>(a: A)` | `def g {α : Type} [T α] (a : α)` | §10 |
| （不支持 HKT） | `class F (f : Type → Type)` | §10 |
| `mod m { ... }`、`use m::*` | `namespace M ... end M`、`open M` | §11 |
| `assert_eq!(a, b)` | `#guard a == b` 或 `example : a = b := rfl` | §2 |
| `x.map(f)`（`Option`） | `f <$> x` 或 `x.map f` | §16 |
| `x.and_then(f)` | `x >>= f` | §16 |
| `let y = x?;` | `let y ← x`（在 `do` 中） | §16 |
| `fn main() { println!("hi") }` | `def main : IO Unit := IO.println "hi"` | §17 |

## 19 继续学习

本章只覆盖了读这本书所需的部分。想深入学习 Lean 4，下面这些都是免费的：

- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)：把 Lean 当编程语言学，最适合程序员。
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)：系统讲解依值类型论和证明。
- [Lean 4 参考手册](https://lean-lang.org/doc/reference/latest/)：语言的权威说明。
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)：用游戏学 tactic。
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)：用 Mathlib 做数学（本书不用 Mathlib，但它是数学形式化的主战场）。
- [Lean Zulip 社区](https://leanprover.zulipchat.com/)：遇到问题时可以去提问，社区非常友好。

## 练习

1. 定义一个函数 `applyN (f : Nat → Nat) (n : Nat) (x : Nat) : Nat`，把 `f` 作用 `n` 次。验证 `applyN double 3 1 = 8`。
2. 为 `Bool` 写一个 `MyAlg.Monoid` 实例，运算是“与”（`&&`），单位元是什么？再写出它的 `LawfulMonoid` 实例。
3. 为 `Tree` 写一个 `MyFunctor.Functor` 实例，并验证把 `smallTree` 中每个数翻倍后得到的树。
4. 用 tactic 证明：对所有 `n : Nat`，`double n = 2 * n`。
5. 用证明项（不用 tactic）证明 `(p → q) → ¬q → ¬p`（这叫“逆否命题”，0.2 会讲）。
6. 证明：对所有列表 `xs : List Nat`，`sumList (xs.map (fun _ => 0)) = 0`。提示：对 `xs` 做归纳。

::: details 参考答案

```lean
-- 1
def applyN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => f (applyN f n x)

#guard applyN double 3 1 == 8

-- 2：单位元是 true，因为 true && b = b
namespace MyAlg

instance : Monoid Bool where
  empty := true
  op := (· && ·)

instance : LawfulMonoid Bool where
  empty_op := by intro a; cases a <;> rfl
  op_empty := by intro a; cases a <;> rfl
  op_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

#guard mconcat [true, true, false] == false

end MyAlg

-- 3
def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | .leaf => .leaf
  | .node l x r => .node (l.map f) (f x) (r.map f)

instance : MyFunctor.Functor Tree where
  map := Tree.map

def Tree.toList {α : Type} : Tree α → List α
  | .leaf => []
  | .node l x r => l.toList ++ [x] ++ r.toList

#guard (MyFunctor.doubleAll smallTree).toList == [2, 4]

-- 4
theorem double_eq_two_mul (n : Nat) : double n = 2 * n := by
  unfold double
  omega

-- 5：拿到 hpq : p → q、hnq : ¬q，以及 hp : p，要推出 False
theorem contrapositive (p q : Prop) : (p → q) → ¬q → ¬p :=
  fun hpq hnq hp => hnq (hpq hp)

-- 6
theorem sumList_map_zero (xs : List Nat) : sumList (xs.map (fun _ => 0)) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumList] at *; exact ih
```

:::

## 本章小结

- Lean 的工具链和 Rust 一一对应：`elan` ≈ `rustup`，`lake` ≈ `cargo`，`lean-toolchain` ≈ `rust-toolchain.toml`。
  用 VS Code 插件或 live.lean-lang.org，**永远开着 Infoview**。本书代码块右下角的“在线运行”会带上本章此前的全部代码。
- `def` 定义函数和常量，函数体是表达式；`fun x => e` 是闭包；`#eval` 计算，`#check` 看类型，`#guard` 和 `example` 是被检查的断言。
- 多参数函数是柯里化的：`α → β → γ` 即 `α → (β → γ)`，`f a b` 即 `(f a) b`；`g ∘ f` 是“g 在 f 之后”。
- `structure` ≈ `struct`，`inductive` ≈ `enum`，`match` ≈ `match`，同样有穷尽性检查；递归类型不需要 `Box`。
- Lean 的函数必须是全函数：模式匹配要穷尽，递归要终止（结构递归自动通过，否则用 `termination_by`，或者退到 `partial def`）。
- `{α : Type}` 是隐式参数（≈ 泛型 `<T>`），`[C α]` 是实例参数（≈ trait bound）。类型是值，类型构造器 `List : Type → Type` 也是值，
  所以 Lean 可以对 `Type → Type` 写类型类，这是 Rust 缺少的高阶类型。
- 类型类的字段可以是**定律的证明**，本书的 `Category`、函子、单子都会把定律写进类型。
- 宇宙：`Prop`（命题）、`Type`（普通类型）、`Type 1`……；需要“以类型为元素”时才用 `Type u`。
- 命题即类型、证明即程序：`→` 是函数，`∧` 是有序对，`∨` 是枚举，`¬p` 是 `p → False`，`∀` 是依值函数，`∃` 是“见证者 + 证明”。
- tactic 证明是单步变换目标：`intro`、`exact`、`apply`、`constructor`、`cases`、`induction`、`rw`、`simp`、`funext`、`calc`、
  `decide`、`omega`、`show`、`unfold`。看不懂时，看 Infoview 里的 `⊢`。
- `Functor` 的 `<$>` ≈ `map`，`Monad` 的 `>>=` ≈ `and_then`，`do` 中的 `←` ≈ `?`，但对任意单子都有效；副作用写在类型 `IO` 里。
