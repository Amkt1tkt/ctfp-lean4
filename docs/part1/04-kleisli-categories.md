# 1.4 Kleisli 范畴

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

你已经看到了怎样把类型和纯函数建模成一个范畴。我也提到过，范畴论里有办法给副作用——也就是不纯的函数——建模。我们来看一个这样的例子：会记录或追踪自己执行过程的函数。在命令式语言里，这种东西多半是靠修改某个全局状态来实现的。用 Rust 写，大概是这样：

```rust
use std::sync::Mutex;

static LOGGER: Mutex<String> = Mutex::new(String::new());

fn negate(b: bool) -> bool {
    LOGGER.lock().unwrap().push_str("Not so! ");
    !b
}
```

（Rust 不会让你随随便便地写一个可变全局变量：要么像上面这样套一层 `Mutex`，要么用 `static mut` 加上 `unsafe`，要么用 `thread_local!`。编译器的这份啰嗦本身就是在提醒你：这里有危险。）

你知道这不是纯函数，因为它的记忆化版本（见 [1.2 类型与函数](/part1/02-types-and-functions) 的挑战题）会漏掉日志：第二次调用时直接从缓存里拿结果，`"Not so! "` 就不会再被写进去了。这个函数有**副作用**（side effect）。

在现代编程里，我们尽可能远离全局可变状态——哪怕只是因为它让并发变得一团糟。你也绝不会把这样的代码放进一个库里。

幸运的是，这个函数是可以变纯的。你只需要把日志显式地传进去、再传出来。我们给它加一个字符串参数，并把正常的输出和一个装着更新后日志的字符串配成一对：

```rust
fn negate(b: bool, logger: String) -> (bool, String) {
    (!b, logger + "Not so! ")
}
```

这个函数是纯的：它没有副作用，用相同的参数调用它，每次都返回同一对值，需要的话也可以记忆化。不过，考虑到日志是不断累积的，你得把所有可能导致这次调用的“历史”都记下来。下面两次调用要各占一个独立的缓存条目：

```rust no-check
negate(true, "It was the best of times. ".to_string());
```

和

```rust no-check
negate(true, "It was the worst of times. ".to_string());
```

依此类推。（这两句出自狄更斯《双城记》的开头：“那是最好的时代，那是最坏的时代。”——对缓存来说，这两个时代确实是两码事。）

对于一个库函数来说，这也不是什么好接口。调用者可以无视返回值里的字符串，所以这部分负担不算太大；但他们**被迫**传入一个字符串作为输入，这可能相当不方便。

有没有办法用一种不那么“侵入”的方式做同样的事？有没有办法把关注点分离开？在这个简单的例子里，函数 `negate` 的主要目的是把一个布尔值变成另一个布尔值，记日志是次要的。诚然，被记下的那条消息是这个函数特有的，但把消息汇总成一份连续日志，是另一件独立的事。我们仍然希望函数产生一个字符串，但想让它从“维护日志”的负担中解脱出来。于是有了这样一个折中方案：

```rust
fn negate(b: bool) -> (bool, String) {
    (!b, "Not so! ".to_string())
}
```

想法是：日志将在函数调用**之间**被汇总起来。

为了看清这件事怎么做，我们换一个稍微现实一点的例子。我们有一个从字符串到字符串的函数，把小写字母转成大写：

```rust
fn to_upper(s: String) -> String {
    s.chars().map(|c| c.to_ascii_uppercase()).collect()
}
```

还有一个函数，按空白字符把一个字符串拆成一串字符串：

```rust no-check
fn to_words(s: String) -> Vec<String> {
    words(s)
}
```

真正干活的是辅助函数 `words`：

```rust
fn words(s: String) -> Vec<String> {
    let mut result = vec![String::new()];
    for c in s.chars() {
        if c.is_whitespace() {
            result.push(String::new());
        } else {
            result.last_mut().unwrap().push(c);
        }
    }
    result
}
```

（地道的 Rust 会直接写 `s.split_whitespace()`。这里故意照着原书的命令式写法手写一遍，好让你看清它在做什么。）

我们想修改 `to_upper` 和 `to_words`，让它们在常规返回值之上再“驮”一条消息字符串。

![驮着消息的函数](/img/1.4/piggyback.jpg "让函数的返回值“背”上一条额外的消息。")

我们要“修饰”这些函数的返回值。用一种通用的方式来做：定义一个泛型类型别名 `Writer`，它封装一个二元组，第一个分量是任意类型 `A` 的值，第二个分量是一个字符串：

```rust no-check
type Writer<A> = (A, String);
```

修饰之后的函数是这样的：

```rust
type Writer<A> = (A, String);

fn words(s: &str) -> Vec<String> {
    s.split_whitespace().map(String::from).collect()
}

fn to_upper(s: String) -> Writer<String> {
    let result = s.chars().map(|c| c.to_ascii_uppercase()).collect();
    (result, "toUpper ".to_string())
}

fn to_words(s: String) -> Writer<Vec<String>> {
    (words(&s), "toWords ".to_string())
}

// 我们想把这两个函数复合成另一个修饰函数：先转大写、再拆成单词，同时产生一份记录这些动作的日志。
fn process(s: String) -> Writer<Vec<String>> {
    let p1 = to_upper(s);
    let p2 = to_words(p1.0);
    (p2.0, p1.1 + &p2.1)
}
```

最后那个 `process` 就是我们想要的复合：把字符串转成大写、拆成单词，同时产生一份记录了这些动作的日志。

我们达到了目标：汇总日志不再是各个函数自己的事了。它们只产生自己的消息，然后由外部把这些消息拼接成一份更大的日志。

现在想象一下，一整个程序都用这种风格来写。那将是一场由重复、易错的代码组成的噩梦。但我们是程序员，我们知道怎么对付重复代码：把它抽象出来！不过，这可不是你平常做的那种抽象——我们要抽象的是**函数复合**（function composition）本身。而复合正是范畴论的本质，所以在写更多代码之前，先从范畴的角度分析一下这个问题。

## Writer 范畴

为了“驮”上一些额外功能而去修饰一批函数的返回类型——这个想法后来被证明极其富有成果。我们会看到它的很多很多例子。出发点是我们熟悉的那个由类型和函数构成的范畴。我们保留类型作为对象，但把态射重新定义为**修饰函数**（embellished function）。

例如，假设我们想修饰一个从 `i32` 到 `bool` 的函数 `is_even`。我们把它变成一个态射，这个态射由一个修饰函数来表示。关键在于：尽管这个修饰函数返回的是一个二元组，这个态射**仍然被看作对象 `i32` 和 `bool` 之间的箭头**：

```rust no-check
fn is_even(n: i32) -> (bool, String) {
    (n % 2 == 0, "isEven ".to_string())
}
```

按照范畴的定律，我们应该能把这个态射和另一个从对象 `bool` 出发、去往随便哪里的态射复合起来。特别地，应该能把它和前面的 `negate` 复合：

```rust no-check
fn negate(b: bool) -> (bool, String) {
    (!b, "Not so! ".to_string())
}
```

显然，我们没法像复合普通函数那样复合这两个态射，因为输入和输出对不上：`is_even` 吐出的是一对 `(bool, String)`，而 `negate` 想要的只是一个 `bool`。它们的复合应该长成这样：

```rust
fn is_even(n: i32) -> (bool, String) {
    (n % 2 == 0, "isEven ".to_string())
}

fn negate(b: bool) -> (bool, String) {
    (!b, "Not so! ".to_string())
}

fn is_odd(n: i32) -> (bool, String) {
    let p1 = is_even(n);
    let p2 = negate(p1.0);
    (p2.0, p1.1 + &p2.1)
}
```

于是，在我们正在构造的这个新范畴里，复合两个态射的配方是：

1. 执行第一个态射对应的修饰函数；
2. 取出结果二元组的第一个分量，传给第二个态射对应的修饰函数；
3. 把第一个结果的第二个分量（字符串）和第二个结果的第二个分量（字符串）拼接起来；
4. 返回一个新的二元组：第一个分量取自最终结果，第二个分量是拼接后的字符串。

下面这个小组件就是这份配方的“慢动作回放”。你可以自己拼一条修饰函数链，然后一步一步执行，看看值是怎样沿着链条往下传、而日志又是怎样在“幕后”被拼接起来的。

<div><Ch1_4KleisliStepper /></div>

如果想把这种复合抽象成一个高阶函数，在 Rust 里我们需要一个以三个类型为参数的泛型函数，这三个类型对应范畴中的三个对象。它接受两个按我们的规则可以复合的修饰函数，返回第三个修饰函数。最直白的写法是用装箱的 trait 对象（`Box<dyn Fn>`），它大致相当于其他语言里“函数对象”的概念：

```rust
type Writer<A> = (A, String);

fn compose<A: 'static, B: 'static, C: 'static>(
    m1: Box<dyn Fn(A) -> Writer<B>>,
    m2: Box<dyn Fn(B) -> Writer<C>>,
) -> Box<dyn Fn(A) -> Writer<C>> {
    Box::new(move |x| {
        let p1 = m1(x);
        let p2 = m2(p1.0);
        (p2.0, p1.1 + &p2.1)
    })
}

fn to_upper(s: String) -> Writer<String> {
    (s.to_uppercase(), "toUpper ".to_string())
}

fn to_words(s: String) -> Writer<Vec<String>> {
    (s.split_whitespace().map(String::from).collect(), "toWords ".to_string())
}

fn process(s: String) -> Writer<Vec<String>> {
    compose::<String, String, Vec<String>>(Box::new(to_upper), Box::new(to_words))(s)
}
```

现在我们可以回到前面的例子，用这个新的 `compose` 来实现 `to_upper` 和 `to_words` 的复合了。但传类型参数、装箱，噪音还是太多。原书在这里借助 C++14 的泛型 lambda 和返回类型推导消除了这些噪音（Milewski 特别注明，那段代码出自 Eric Niebler 之手）。在 Rust 里，泛型配合 `impl Fn` 同样可以让编译器自己推断所有类型，而且不需要堆分配：

```rust
type Writer<A> = (A, String);

fn compose<A, B, C>(
    m1: impl Fn(A) -> Writer<B>,
    m2: impl Fn(B) -> Writer<C>,
) -> impl Fn(A) -> Writer<C> {
    move |x| {
        let (y, s1) = m1(x);
        let (z, s2) = m2(y);
        (z, s1 + &s2)
    }
}

fn to_upper(s: String) -> Writer<String> {
    (s.to_uppercase(), "toUpper ".to_string())
}

fn to_words(s: String) -> Writer<Vec<String>> {
    (s.split_whitespace().map(String::from).collect(), "toWords ".to_string())
}

fn process(s: String) -> Writer<Vec<String>> {
    compose(to_upper, to_words)(s)
}
```

用了这个新定义，`process` 的实现简化成了一行 `compose(to_upper, to_words)(s)`。

::: tip Rust 视角
`impl Fn(A) -> Writer<B>` 出现在参数位置时，意思是“某个实现了 `Fn(A) -> Writer<B>` 的具体类型，由调用者决定”；
出现在返回位置时，意思是“某个实现了这个 trait 的具体类型，由函数自己决定，但调用者不必知道它叫什么”。
`compose` 返回的闭包用 `move` 把 `m1`、`m2` 的所有权搬进去，这样闭包就可以活得比 `compose` 的调用更久。
这正是“把复合本身抽象成一个函数”在 Rust 中的样子。
:::

但我们还没完。我们定义了新范畴里的复合，可恒等态射是什么呢？它们可不是我们平常的恒等函数！它们必须是从类型 A 回到类型 A 的态射，也就是说，它们是这种形式的修饰函数：

```rust no-check
fn identity<A>(x: A) -> Writer<A>;
```

它们必须在复合中表现得像“单位”一样。看看我们对复合的定义，你会发现：恒等态射应当原封不动地传递它的参数，并且只往日志里贡献一个空字符串：

```rust
type Writer<A> = (A, String);

fn identity<A>(x: A) -> Writer<A> {
    (x, String::new())
}
```

你很容易就能说服自己，我们刚刚定义的确实是一个合法的范畴。特别是，我们的复合显然满足结合律：如果只盯着每个二元组的第一个分量看，发生的事情就是普通的函数复合，而函数复合满足结合律；第二个分量则是被拼接起来的，而拼接也满足结合律。（在本章后面的“补充”里，我们会让 Lean 来替我们“说服自己”。）

敏锐的读者也许会注意到：把这个构造推广到任意幺半群，而不只是字符串幺半群，是很容易的。我们只需在 `compose` 里使用幺半群的二元运算（Haskell 里叫 `mappend`），在 `identity` 里使用幺半群的单位元（`mempty`），来代替 `+` 和 `""`。真的没有理由把自己局限于只记录字符串。一个好的库作者应该能找出让库能工作的**最低限度**的约束——这里，日志库唯一的要求就是：日志具有幺半群的性质。

::: info 数学小课堂：再看一眼幺半群
回忆 [1.3 大大小小的范畴](/part1/03-categories-great-and-small)：**幺半群**（monoid）是一个集合，配上一个二元运算 $\cdot$ 和一个特殊元素 $e$，满足

- 结合律：$(x \cdot y) \cdot z = x \cdot (y \cdot z)$；
- 单位律：$e \cdot x = x$，$x \cdot e = x$。

字符串配上拼接 `++`、空串 `""` 是一个幺半群；自然数配上加法、`0` 也是；自然数配上乘法、`1` 也是；
`bool` 配上 `&&`、`true` 也是。所以“日志”完全可以是一个计数器（每一步加 1），也可以是一串警告信息、一个耗时总和……
只要它能“合并”、合并满足结合律、并且有一个“什么都没有”的元素就行。
:::

## Lean 中的 Writer

同样的东西在 Lean 里写起来更简洁，编译器也能给我们多得多的帮助。先定义 `Writer` 类型：

```lean
abbrev Writer (α : Type) : Type := α × String
```

这里我只是定义了一个类型别名，相当于 Rust 里的 `type Writer<A> = (A, String);`。类型 `Writer` 以一个类型变量 `α` 为参数，它就等同于 `α` 与 `String` 的二元组。二元组（积类型）的类型写作 `α × String`（`×` 用 `\x` 输入），而二元组的值的写法极其简洁：两个元素放在圆括号里、用逗号隔开，例如 `(42, "hello")`。

::: tip Lean 深入：`abbrev` 与 `def`
`abbrev` 是“可约（reducible）的定义”：Lean 在类型检查、类型类实例搜索、`simp` 化简时都会毫不犹豫地把 `Writer α` 展开成 `α × String`。
这正是类型别名该有的行为——`Writer α` 和 `α × String` 是**同一个**类型，只是名字不同。

如果改用 `def Writer (α : Type) : Type := α × String`，Lean 就会把 `Writer` 当成一个更“不透明”的名字：
许多自动化（例如实例搜索、`rfl` 在可约透明度下的检查）就不再自动看穿它。那样写也能用，但会在证明里给自己添麻烦。
经验法则：想要“只是起个别名”，用 `abbrev`；想要“新的抽象，内部表示是实现细节”，用 `def` 或 `structure`。
:::

我们的态射是从任意类型到某个 `Writer` 类型的函数：

```lean no-check
α → Writer β
```

我们把复合声明成一个有趣的中缀运算符，有时被称作“鱼”（fish）：

```lean no-check
fish : (α → Writer β) → (β → Writer γ) → (α → Writer γ)
```

它是一个二元函数，两个参数本身都是函数，返回值也是一个函数。第一个参数的类型是 `α → Writer β`，第二个是 `β → Writer γ`，结果是 `α → Writer γ`。

下面是这个函数的定义，以及把它变成中缀运算符 `>=>` 的记号声明。两个参数 `m1` 和 `m2` 分别出现在这条“鱼”的两侧：

```lean
def fish {α β γ : Type} (m1 : α → Writer β) (m2 : β → Writer γ) : α → Writer γ :=
  fun x =>
    let (y, s1) := m1 x
    let (z, s2) := m2 y
    (z, s1 ++ s2)

infixr:55 " >=> " => fish
```

结果是一个单参数 `x` 的 lambda 函数。Lean 里的 lambda 写作 `fun x => ...`；你也可以直接写希腊字母 `λ x => ...`。（Haskell 程序员就没这么好的福气了：他们的键盘上没有 λ，只好用反斜杠 `\` 来代替——你可以把它想象成一个被截掉了一条腿的 λ。）

`let` 让你声明辅助变量。这里，调用 `m1` 的结果被模式匹配成一对变量 `(y, s1)`；用第一个模式里得到的 `y` 去调用 `m2`，结果再被匹配成 `(z, s2)`。

在 Lean（以及 Haskell）里，用模式匹配来拆二元组比用访问器（`.1`、`.2`，或者 `Prod.fst`、`Prod.snd`）更常见——我们在 Rust 版本里第一次写的是 `p1.0`、`p1.1`，第二次就改成了 `let (y, s1) = m1(x);`。除此之外，两种实现几乎是逐行对应的。

整个 `fun` 的值由最后一行给出：这里是一个二元组，第一个分量是 `z`，第二个分量是两个字符串的拼接 `s1 ++ s2`。

::: tip Lean 深入：`let` 模式匹配与自定义中缀记号
- Lean 的 `let (y, s1) := m1 x` 和 Rust 的 `let (y, s1) = m1(x);` 几乎一模一样，只是用 `:=` 而不是 `=`，行尾也不需要分号。
  每个 `let` 之后另起一行，最后一行的表达式就是整个块的值（就像 Rust 块里最后一个不带分号的表达式）。
  Haskell 需要 `let ... in ...`，Lean 不需要 `in`。
- `infixr:55 " >=> " => fish` 声明了一个**右结合**（`infixr`，r 指 right）、优先级为 55 的中缀记号：
  从此 `f >=> g` 就是 `fish f g`，而 `f >=> g >=> h` 被解析成 `f >=> (g >=> h)`。
  Lean 允许你用几乎任何 Unicode 符号串定义新记号，这是它作为“证明助手”的传统：数学家喜欢自己的记号。
- 细心的你可能会问：Lean 核心库不是已经有一个 `>=>` 了吗？没错（后面会讲到）。Lean 允许记号**重载**：
  遇到 `f >=> g` 时，它会尝试每一种含义，只保留能通过类型检查的那一个。对我们的 `Writer` 来说，只有我们自己的 `fish` 说得通。
:::

我还要为我们的范畴定义恒等态射。出于一些很久以后才会讲清楚的原因，Haskell 里把它叫做 `return`。可 `return` 在 Lean 里是关键字（用于 `do` 记号中的提前返回，和 Rust 的 `return` 差不多），所以我们叫它 `ret`：

```lean
def ret {α : Type} (x : α) : Writer α := (x, "")
```

::: tip Lean 深入：关键字作标识符
如果你执意要用 `return` 作为名字，Lean 也有办法：用书名号括起来，写作 `«return»`，任何字符串都能变成合法的标识符。
不过那样每次使用都得带着书名号，我们还是老老实实叫它 `ret` 吧。在 Lean 的 `Monad` 类型类中，这个角色叫 `pure`。
:::

为了完整起见，下面是修饰函数 `upCase` 和 `toWords` 的 Lean 版本：

```lean
/-- 按空白字符切分，并丢掉空串（相当于 Haskell 的 `words`、Rust 的 `split_whitespace`）。 -/
def words (s : String) : List String :=
  let spaced := s.map (fun c => if c.isWhitespace then ' ' else c)
  (spaced.splitOn " ").filter (· ≠ "")

def upCase (s : String) : Writer String :=
  (s.map Char.toUpper, "upCase ")

def toWords (s : String) : Writer (List String) :=
  (words s, "toWords ")
```

`String.map` 把一个字符函数作用到字符串的每个字符上，相当于 Rust 的 `s.chars().map(...).collect()`；这里作用的是 `Char.toUpper`。Haskell 的标准库自带 `words`，Lean 核心库没有，所以我们自己写了一个：先把所有空白字符换成空格，再按空格切开，最后用 `filter` 扔掉切出来的空串。`(· ≠ "")` 是 `fun x => x ≠ ""` 的简写，`·` 表示“参数放在这里”。

最后，借助“鱼”运算符，两个函数的复合一行就写完了：

```lean
def process : String → Writer (List String) :=
  upCase >=> toWords

#guard process "hello kleisli world" == (["HELLO", "KLEISLI", "WORLD"], "upCase toWords ")
```

`#guard` 会在编译时求值它后面的布尔表达式，如果结果不是 `true` 就报错。所以你在书里看到的这些输出，都是被机器检查过的。

同样，`isEven` 和 `negate` 也可以复合成 `isOdd`：

```lean
def isEven (n : Int) : Writer Bool := (n % 2 == 0, "isEven ")

def negate (b : Bool) : Writer Bool := (!b, "Not so! ")

def isOdd : Int → Writer Bool := isEven >=> negate

#guard isOdd 3 == (true, "isEven Not so! ")
#guard isOdd 10 == (false, "isEven Not so! ")
```

## Kleisli 范畴

你也许已经猜到了，这个范畴不是我当场发明的。它是所谓 **Kleisli 范畴**（Kleisli category）的一个例子——一种建立在单子（monad）之上的范畴。我们还没准备好讨论单子，但我想先让你尝尝它们能做什么。就我们目前有限的目的而言，一个 Kleisli 范畴以底层编程语言的类型作为对象。从类型 $A$ 到类型 $B$ 的态射，是那些从 $A$ 出发、去往“由 $B$ 经过特定修饰而得到的类型”的函数。每个 Kleisli 范畴都定义了自己复合这种态射的方式，以及相对于这种复合的恒等态射。（以后我们会看到，“修饰”这个不太精确的说法，对应的是范畴中**自函子**（endofunctor）的概念。）

```diagram
A: (0, 0) "a"
B: (2, 0) "b"
C: (4, 0) "c"
f: A -> B "f" side=left
g: B -> C "g" side=left
gf: A -> C "f \mathbin{>=>} g" bend=-45 side=right color=green
pad: (2, 0.8) ""
idA: A -> A "\mathtt{ret}" loop=up
idC: C -> C "\mathtt{ret}" loop=up
path "先走 f 再走 g": f g
path "直接走 f >=> g": gf color=green
caption: Writer 范畴中的箭头。f 实际上是一个函数 a → Writer b，g 是 b → Writer c，但在这个范畴里我们把它们画成 a 到 b、b 到 c 的箭头；它们的复合由“鱼”给出，恒等态射由 ret 给出。
```

我在本章中用作范畴基础的那个特定单子，叫做 **Writer 单子**（writer monad），它被用来记录或追踪函数的执行。它也是一种更一般的机制的例子：把副作用嵌入到纯计算之中。你之前已经看到，我们可以在集合范畴中为编程语言的类型和函数建模（照例忽略底 ⊥——在 Lean 里，因为所有函数都是全函数，连这个“照例”都省了）。在这里，我们把这个模型扩展到了一个稍有不同的范畴：它的态射由修饰函数表示，而它们的复合所做的，不仅仅是把一个函数的输出传给另一个函数的输入。我们多了一个可以玩的自由度：复合本身。事实证明，正是这个自由度，使得我们可以为那些在命令式语言里传统上靠副作用实现的程序，给出简单的**指称语义**（denotational semantics）。

::: info 数学小课堂：同样的对象，不同的箭头
初学者很容易在这里打结：Writer 范畴的对象和 **Set**（或者说 Lean 的 `Type`）的对象**完全一样**，都是类型；
不同的只是箭头。在 **Set** 里，从 `Int` 到 `Bool` 的箭头是函数 `Int → Bool`；在 Writer 范畴里，从 `Int` 到 `Bool` 的箭头是函数
`Int → Bool × String`。

所以“范畴”从来不只是“一堆对象”。同一堆对象，配上不同的箭头和不同的复合规则，就是不同的范畴。
这有点像同一群人，按“谁认识谁”连线是一张图，按“谁欠谁钱”连线又是另一张图。
:::

## 补充：用 Lean 证明 Writer 范畴真的是范畴

原书说：“你很容易就能说服自己，这确实是一个合法的范畴。”在 Lean 里，我们可以不止说服自己——我们可以说服编译器。

需要证明三条定律。把 Writer 范畴里的复合 $g \circ f$ 写成 `f >=> g`（注意顺序：鱼是“先左后右”，而 $\circ$ 是“先右后左”），恒等态射写成 `ret`：

- 左单位律：`ret >=> f = f`；
- 右单位律：`f >=> ret = f`；
- 结合律：`(f >=> g) >=> h = f >=> (g >=> h)`。

这三条最终都归结为字符串拼接的性质。Lean 核心库已经为我们证好了：

```lean
#check @String.empty_append   -- "" ++ s = s
#check @String.append_empty   -- s ++ "" = s
#check @String.append_assoc   -- s₁ ++ s₂ ++ s₃ = s₁ ++ (s₂ ++ s₃)
```

（`#check` 会显示一个名字的类型；对定理来说，类型就是它所陈述的命题。`@` 表示把隐式参数也显示出来。）

于是：

```lean
/-- 左单位律：先 `ret` 再 `f`，等于 `f`。 -/
theorem ret_fish {α β : Type} (f : α → Writer β) : ret >=> f = f := by
  funext x                    -- 两个函数相等 ⇐ 对每个输入 x，输出相等
  simp only [fish, ret]       -- 展开 fish 和 ret 的定义
  rcases f x with ⟨y, s⟩      -- 把 f x 拆成一对 (y, s)
  simp only [String.empty_append]  -- 剩下 (y, "" ++ s) = (y, s)

/-- 右单位律：先 `f` 再 `ret`，等于 `f`。 -/
theorem fish_ret {α β : Type} (f : α → Writer β) : f >=> ret = f := by
  funext x
  simp only [fish, ret, String.append_empty]

/-- 结合律：两种加括号的方式给出同一个修饰函数。 -/
theorem fish_assoc {α β γ δ : Type}
    (f : α → Writer β) (g : β → Writer γ) (h : γ → Writer δ) :
    (f >=> g) >=> h = f >=> (g >=> h) := by
  funext x
  simp only [fish]
  rcases f x with ⟨y, s₁⟩     -- 第一步的结果
  rcases g y with ⟨z, s₂⟩     -- 第二步的结果
  rcases h z with ⟨w, s₃⟩     -- 第三步的结果
  -- 现在目标是 (w, s₁ ++ s₂ ++ s₃) = (w, s₁ ++ (s₂ ++ s₃))
  simp only [String.append_assoc]
```

::: tip Lean 深入：这几个 tactic 在干什么
- `by` 进入“tactic 模式”：不直接写出证明项，而是一步步告诉 Lean 怎么把目标变简单。
- `funext x`：**函数外延性**（function extensionality）。要证两个函数相等，只需证它们对任意输入 `x` 给出相等的输出。
- `simp only [...]`：只用方括号里列出的等式（和定义）去改写目标。这里先用它展开 `fish` 和 `ret`，把 `let` 模式匹配摊开。
- `rcases e with ⟨y, s⟩`：把一个二元组类型的表达式 `e` 拆成两个分量，并把目标里所有的 `e` 都换成 `(y, s)`。
  拆开之后，`let (y, s1) := (y, s); ...` 这样的匹配就能被计算掉了。
- 最后再用一次 `simp only`，用库里的字符串引理收尾。
:::

注意这三个证明的结构，正好对应原书那句口头论证：“第一个分量就是普通的函数复合，第二个分量是在拼接，而拼接满足结合律。”我们把每个函数的结果拆成“值”和“日志”两半，值的部分根本不需要证明（它们自然相等），日志的部分则交给 `String.append_assoc` 这类引理。

有了这些定理，就可以构造一个货真价实的 `CTFP.Category` 实例了。这里有个小问题：`Type` 已经有一个范畴实例 `typeCategory` 了（箭头是普通函数），Lean 根据**对象的类型**来挑选实例，同一个对象类型不能同时有两套箭头。解决办法是给“同一批对象”换一个新名字：

```lean
/-- Writer 范畴的对象：就是一个类型，只是穿了件新马甲。 -/
structure WriterObj where
  carrier : Type

/-- 方便的写法：`W Int` 表示“作为 Writer 范畴对象的 `Int`”。 -/
abbrev W (α : Type) : WriterObj := ⟨α⟩

instance writerCategory : Category WriterObj where
  Hom a b := a.carrier → Writer b.carrier   -- 从 a 到 b 的箭头是修饰函数
  id _ := ret                                -- 恒等态射是 ret
  comp g f := f >=> g                        -- g ⊚ f 是“先 f 后 g”，即 f >=> g
  id_comp f := fish_ret f
  comp_id f := ret_fish f
  assoc f g h := fish_assoc f g h
```

::: tip Rust 视角：newtype 模式
这和 Rust 的 **newtype 模式**如出一辙。假设你想给 `Vec<T>` 换一种 `Display` 的实现，但 `Vec<T>` 已经（或者不能）有那个 trait 实现了，
你就写 `struct Pretty(Vec<T>);`，再为 `Pretty` 实现 `Display`。Lean 的类型类实例和 Rust 的 trait 实现一样，
是按类型来查找的，想要“同一个东西的另一种实现”，就得先给它一个新名字。
:::

现在，`isEven` 和 `negate` 摇身一变就成了 Writer 范畴里的箭头，可以用全书统一的复合记号 `⊚` 来复合：

```lean
def isEvenW : W Int ⟶ W Bool := isEven
def negateW : W Bool ⟶ W Bool := negate

-- 在 Writer 范畴中，“negate 在 isEven 之后”
def isOddW : W Int ⟶ W Bool := negateW ⊚ isEvenW

#guard isOddW 7 == (true, "isEven Not so! ")

-- 恒等态射什么也不记
example : (𝟙 (W Bool) ⊚ negateW) = negateW := Category.id_comp negateW
```

注意 `isEvenW` 的定义就是 `isEven` 本身——这句话再朴素不过地说明了：Writer 范畴的箭头**就是**修饰函数，只是我们换了一副眼镜去看它。

### 推广到任意幺半群

原书说，这个构造可以推广到任意幺半群。我们把这句话也变成代码和定理。为了避免与将来可能出现的其他定义冲突，我们把它放进命名空间 `General` 里：

```lean
namespace General

/-- 幺半群：一个带结合二元运算和单位元的类型。定律直接写进类型类。 -/
class Monoid (w : Type) where
  empty : w
  append : w → w → w
  empty_append : ∀ x, append empty x = x
  append_empty : ∀ x, append x empty = x
  append_assoc : ∀ x y z, append (append x y) z = append x (append y z)

/-- 以幺半群 `w` 为日志的 Writer。 -/
abbrev Writer (w : Type) (α : Type) : Type := α × w

def fish {w α β γ : Type} [Monoid w]
    (m1 : α → Writer w β) (m2 : β → Writer w γ) : α → Writer w γ :=
  fun x =>
    let (y, s1) := m1 x
    let (z, s2) := m2 y
    (z, Monoid.append s1 s2)

def ret {w α : Type} [Monoid w] (x : α) : Writer w α := (x, Monoid.empty)

theorem ret_fish {w α β : Type} [Monoid w] (f : α → Writer w β) : fish ret f = f := by
  funext x
  simp only [fish, ret]
  rcases f x with ⟨y, s⟩
  simp only [Monoid.empty_append]

theorem fish_ret {w α β : Type} [Monoid w] (f : α → Writer w β) : fish f ret = f := by
  funext x
  simp only [fish, ret, Monoid.append_empty]

theorem fish_assoc {w α β γ δ : Type} [Monoid w]
    (f : α → Writer w β) (g : β → Writer w γ) (h : γ → Writer w δ) :
    fish (fish f g) h = fish f (fish g h) := by
  funext x
  simp only [fish]
  rcases f x with ⟨y, s₁⟩
  rcases g y with ⟨z, s₂⟩
  rcases h z with ⟨_, s₃⟩
  simp only [Monoid.append_assoc]

/-- 对每个幺半群 `w`，都有一个 Writer 范畴。 -/
structure Obj (w : Type) where
  carrier : Type

instance writerCategory (w : Type) [Monoid w] : Category (Obj w) where
  Hom a b := a.carrier → Writer w b.carrier
  id _ := ret
  comp g f := fish f g
  id_comp f := fish_ret f
  comp_id f := ret_fish f
  assoc f g h := fish_assoc f g h

/-- 字符串是幺半群：定律直接用核心库的引理。 -/
instance : Monoid String where
  empty := ""
  append := (· ++ ·)
  empty_append _ := String.empty_append
  append_empty _ := String.append_empty
  append_assoc _ _ _ := String.append_assoc

/-- 自然数配加法也是幺半群：于是“日志”可以是一个步数计数器。 -/
instance : Monoid Nat where
  empty := 0
  append := (· + ·)
  empty_append := Nat.zero_add
  append_empty := Nat.add_zero
  append_assoc := Nat.add_assoc

def double (n : Nat) : Writer Nat Nat := (2 * n, 1)   -- 每做一步，计数加 1
def succ' (n : Nat) : Writer Nat Nat := (n + 1, 1)

#guard fish double (fish succ' double) 5 == (22, 3)   -- 结果 22，一共走了 3 步

end General
```

整个证明里，我们**一次也没有用到“日志是字符串”这件事**，只用到了幺半群的三条定律。这就是原书那句话的精确含义：“日志库唯一的要求，就是日志具有幺半群的性质。”Lean 不但让你写出这个最小约束，还替你检查了它确实足够。

## 补充：预告——Lean 的 `Monad` 与核心库里的 `>=>`

Lean 核心库其实已经定义了“鱼”运算符，只不过它不是专门为 `Writer` 写的，而是对**任何**单子都适用：

```lean
#check @Bind.kleisliRight
-- @Bind.kleisliRight : {α : Type u_1} → {m : Type u_2 → Type u_3} → {β γ : Type u_2} →
--   [Bind m] → (α → m β) → (β → m γ) → α → m γ
```

它的定义就是 `fun a => f₁ a >>= f₂`，记号正是 `>=>`（反方向的版本 `Bind.kleisliLeft` 记作 `<=<`）。这里的 `m` 就是那个“修饰”：`Option`、`List`、`IO`、`Except ε`……只要它是一个单子（更准确地说，只要它有 `bind` 操作，也就是 `>>=`），就自动拥有一个 Kleisli 复合。

为了让核心库的 `>=>` 认得我们的日志类型，我们需要告诉 Lean：它是一个 `Monad`。这里把日志类型包成一个结构体 `Logged`（这样它就不会被误认成上面那个二元组版的 `Writer`，重载的 `>=>` 也不会产生歧义）：

```lean
structure Logged (α : Type) where
  val : α
  log : String
  deriving BEq, Repr

instance : Monad Logged where
  pure x := ⟨x, ""⟩                         -- 恒等态射：值不变，日志为空
  bind m k :=                               -- m >>= k：先算 m，再把值交给 k
    let r := k m.val
    ⟨r.val, m.log ++ r.log⟩                 -- 日志拼接

def upCase' (s : String) : Logged String := ⟨s.map Char.toUpper, "upCase "⟩
def toWords' (s : String) : Logged (List String) := ⟨words s, "toWords "⟩

-- 这次用的是核心库的 >=>（Bind.kleisliRight）
def process' : String → Logged (List String) := upCase' >=> toWords'

#guard process' "a b" == ⟨["A", "B"], "upCase toWords "⟩

-- 同一个复合，也可以用 do 记号写：看上去就像命令式代码，日志在幕后自动拼接
def process'' (s : String) : Logged (List String) := do
  let t ← upCase' s
  toWords' t

#guard process'' "a b" == ⟨["A", "B"], "upCase toWords "⟩
```

`do` 记号里的 `let t ← upCase' s` 读作“执行 `upCase' s`，把结果的**值**绑定到 `t`”——日志去哪儿了？被 `bind` 悄悄拼接起来了。这正是本章开头那个“全局日志变量”想要的效果，只不过现在它是纯函数实现的。到了 [3.4 单子：程序员的定义](/part3/04-monads-programmers-definition)，我们会正式讲清楚这一切；那时你会看到，Kleisli 范畴的三条定律，恰好就是单子的三条定律（Lean 中的 `LawfulMonad` 类型类把它们写进了类型）。

::: tip Rust 视角
你其实每天都在用 Kleisli 复合，只是不叫这个名字。`Option::and_then`、`Result::and_then`、`Iterator::flat_map`、
以及 `?` 运算符，做的都是同一件事：把“返回修饰值的函数”一个接一个地串起来，而修饰（`None`、`Err`、多个结果）由组合子在幕后处理。
Lean 的 `>>=` 就是泛化的 `and_then`，`>=>` 就是把两个 `and_then` 的“回调”预先粘在一起。
:::

## 挑战

一个并非对其参数的所有可能取值都有定义的函数，叫做**偏函数**（partial function）。它并不是数学意义上真正的函数，所以不符合标准的范畴论模子。不过，它可以用一个返回修饰类型 `Option` 的函数来表示。Rust 程序员对此再熟悉不过了：

```rust no-check
enum Option<A> {
    None,
    Some(A),
}
```

例如，下面是修饰函数 `safe_root` 的实现：

```rust
fn safe_root(x: f64) -> Option<f64> {
    if x >= 0.0 { Some(x.sqrt()) } else { None }
}
```

Lean 版本：

```lean
def safeRoot (x : Float) : Option Float :=
  if x ≥ 0 then some x.sqrt else none
```

挑战如下：

1. 为偏函数构造 Kleisli 范畴（定义复合与恒等态射）。
2. 实现修饰函数 `safe_reciprocal`：当参数不为零时，返回它的倒数。
3. 把 `safe_root` 和 `safe_reciprocal` 复合起来，实现 `safe_root_reciprocal`：只要可能，就计算 `sqrt(1/x)`。
4. （Lean 追加题）证明你在第 1 题中定义的复合满足结合律和单位律，并把它做成一个 `CTFP.Category` 实例。

::: details 参考答案

**第 1 题与第 4 题。** 对象仍然是类型，从 `α` 到 `β` 的箭头是函数 `α → Option β`。
恒等态射是 `some`（原样返回，并且“总是成功”）；复合是：先执行第一个函数，如果得到 `none` 就直接返回 `none`，
否则把 `some` 里面的值交给第二个函数。这正是 `Option.bind`（Rust 的 `and_then`）：

```lean
/-- 偏函数的 Kleisli 复合：先 f 后 g。 -/
def optFish {α β γ : Type} (f : α → Option β) (g : β → Option γ) : α → Option γ :=
  fun x =>
    match f x with
    | none   => none        -- 第一步失败，整体失败
    | some y => g y         -- 第一步成功，把结果交给第二步

def optRet {α : Type} : α → Option α := some

theorem optRet_fish {α β : Type} (f : α → Option β) : optFish optRet f = f := by
  funext x; rfl             -- optRet x = some x，匹配直接走 some 分支

theorem optFish_ret {α β : Type} (f : α → Option β) : optFish f optRet = f := by
  funext x
  simp only [optFish, optRet]
  cases f x <;> rfl         -- 分 none / some 两种情况，各自都是 rfl

theorem optFish_assoc {α β γ δ : Type}
    (f : α → Option β) (g : β → Option γ) (h : γ → Option δ) :
    optFish (optFish f g) h = optFish f (optFish g h) := by
  funext x
  simp only [optFish]
  cases f x with
  | none => rfl             -- 第一步就失败：两边都是 none
  | some y => rfl           -- 第一步成功：两边都化为“从 g y 开始”的同一个表达式

structure OptObj where
  carrier : Type

abbrev O (α : Type) : OptObj := ⟨α⟩

instance optionCategory : Category OptObj where
  Hom a b := a.carrier → Option b.carrier
  id _ := optRet
  comp g f := optFish f g
  id_comp f := optFish_ret f
  comp_id f := optRet_fish f
  assoc f g h := optFish_assoc f g h
```

（`cases f x <;> rfl` 里的 `<;>` 表示“把右边的 tactic 作用到左边产生的**每一个**子目标上”。）

**第 2 题。**

```rust
fn safe_reciprocal(x: f64) -> Option<f64> {
    if x != 0.0 { Some(1.0 / x) } else { None }
}
```

```lean
def safeReciprocal (x : Float) : Option Float :=
  if x != 0 then some (1 / x) else none
```

**第 3 题。** 先求倒数，再开平方。在 Rust 里用 `and_then`：

```rust
fn safe_root(x: f64) -> Option<f64> {
    if x >= 0.0 { Some(x.sqrt()) } else { None }
}

fn safe_reciprocal(x: f64) -> Option<f64> {
    if x != 0.0 { Some(1.0 / x) } else { None }
}

fn safe_root_reciprocal(x: f64) -> Option<f64> {
    safe_reciprocal(x).and_then(safe_root)
}

// 或者用 ? 运算符，看上去像普通的顺序代码
fn safe_root_reciprocal2(x: f64) -> Option<f64> {
    let r = safe_reciprocal(x)?;
    safe_root(r)
}
```

在 Lean 里，可以用我们自己的 `optFish`，也可以用 Writer 范畴实例那样的 `⊚`，还可以直接用核心库的 `>=>`（`Option` 是核心库里的单子）：

```lean
def safeRootReciprocal : Float → Option Float :=
  optFish safeReciprocal safeRoot

-- 用核心库的 Kleisli 复合（Bind.kleisliRight）
def safeRootReciprocal' : Float → Option Float :=
  safeReciprocal >=> safeRoot

-- 用全书统一的范畴记号：safeRoot 在 safeReciprocal 之后
def safeRootReciprocal'' : O Float ⟶ O Float :=
  (safeRoot : O Float ⟶ O Float) ⊚ (safeReciprocal : O Float ⟶ O Float)

#guard safeRootReciprocal 4 == some 0.5
#guard safeRootReciprocal 0 == none         -- 0 没有倒数
#guard safeRootReciprocal (-4) == none      -- 倒数是负数，没有实数平方根
#guard safeRootReciprocal' 0.25 == some 2
#guard safeRootReciprocal'' 16 == some 0.25
```

:::

## 本章小结

- 有副作用的函数（比如往全局日志里写东西）可以改写成纯函数：把“副作用”变成返回值的一部分，即返回一个**修饰**过的结果 `(值, 日志)`。
- 修饰函数不能用普通的函数复合串起来，因为输出 `(b, String)` 和下一个函数的输入 `b` 对不上。我们需要**重新定义复合**：传递值、拼接日志。
- 以类型为对象、以修饰函数 `a → Writer b` 为从 `a` 到 `b` 的箭头，配上“鱼”复合 `>=>` 和恒等态射 `ret`（`(x, "")`），就得到 **Writer 范畴**。
- Writer 范畴的定律归结为日志的幺半群定律：拼接满足结合律、空串是单位元。在 Lean 中我们用 `String.append_assoc` 等引理把这三条定律**证明**了出来，并构造了 `CTFP.Category` 实例。
- 这个构造对任意幺半群都成立：日志可以是字符串、计数器、耗时……这就是“找出最小约束”的威力。
- Writer 范畴是 **Kleisli 范畴**的一个例子。每个单子都给出一个 Kleisli 范畴：对象是类型，箭头是 `a → m b`。`Option` 给出偏函数的 Kleisli 范畴，其复合就是 `Option.bind`（Rust 的 `and_then`）。
- Lean 核心库已经提供了通用的 Kleisli 复合 `>=>`（`Bind.kleisliRight`），适用于任何单子；`do` 记号则把 Kleisli 复合写得像命令式代码一样。
- 核心思想：在 Kleisli 范畴里，我们多了一个自由度——**复合本身**。正是它让我们能用纯函数为副作用给出语义。
