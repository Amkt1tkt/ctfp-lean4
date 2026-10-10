# 写作规范（所有章节作者必读）

本书是 Bartosz Milewski《Category Theory for Programmers》（CTFP）的**中文 Lean 4 改写版**。
本文件是全书统一的写作、代码、排版规范。动笔前请完整读完。

---

## 1. 读者是谁、我们要做到什么

**目标读者**：职业 Rust 开发者，正在学 Lean 4；**数学基础薄弱**（大致是高中数学 + 一点离散数学的感觉），
不熟悉 Haskell 和 C++，也不打算学它们。

**目标**：读者读完这本书，就能一次性真正学懂范畴论，同时把 Lean 4 学到能读写证明的程度。

据此：

1. **忠实且完整**。原书每一节、每一段论证、每个例子、每个笑话、每道挑战题都要保留，**不得删减、不得压缩成摘要**。
   正文篇幅应**不少于原书**。Milewski 的口语化、幽默、“深入浅出”的语气要用自然流畅的中文再现
   （不是逐字硬译；读起来要像中文作者写的）。
2. **编程语言彻底换掉**：原书的 Haskell 一律改写为 **Lean 4**；原书用 C++ 说明命令式/底层观点的地方改写为 **Rust**
   （Rust 只在确有帮助时出现，Lean 是主角）。原文中讲解 Haskell 语法/特性的句子，要改写为讲解对应的 Lean 4 语法/特性，
   而不是保留 Haskell 再“翻译一下”。不要出现 Haskell / C++ 代码块。偶尔提一句“Haskell 中写作……”可以，但不要依赖它。
3. **鼓励超越原书**（这是本书的核心价值，请认真做）：
   - **用 Lean 把定律变成定理**。原书只能口头说“函子必须保持复合”，我们可以把它写进类型并**真的证明**出来。
     凡是原书说“读者可以验证……”的地方，尽量给出 Lean 证明（可以放在 `::: details` 里）。
   - **照顾数学基础**：遇到集合论、函数性质、同构、等价关系、归纳法、“对所有…存在…”等概念，第一次出现时给出直观解释、
     具体小例子，放进 `::: info 数学小课堂` 盒子里。宁可多解释一句，不要让读者卡住。
   - **Lean 特性讲解**：章节中第一次用到某个 Lean 特性（结构体、类型类、隐式参数、宇宙、tactic……）时，简短讲清楚，
     必要时链接到 [Lean 4 速成](/guide/lean-for-rustaceans)。放进 `::: tip Lean 深入` 盒子或直接写在正文。
   - **Rust 对照**：当 Rust 的某个概念能帮读者秒懂时（`Option`/`Result`、trait、`impl Fn`、`Iterator::map`、
     `and_then`、生命周期之外的所有权直觉等），给出 `::: tip Rust 视角` 盒子。
   - **交互式可视化**：在真正有助于理解的地方（不是为了炫技）做交互组件或带动画的交换图，见 §6。
   - 你自己额外加的大段内容，请放在上述带标题的提示盒里，或者明确是“补充”小节（例如 `## 补充：用 Lean 证明……`），
     以便读者区分原书内容与扩展内容。正文中的小幅润色和解释不需要标注。
4. **术语统一**：严格使用 §8 术语表。术语第一次出现时附英文：`**态射**（morphism）`。

---

## 2. 文件与结构

- 章节文件路径、标题、编号见 `docs/.vitepress/chapters.mjs`，**不要改动它**。
- 原书 LaTeX 源在 `/agent/repos/milewski-ctfp-pdf/src/content/<编号>/`：
  - `*.tex` 正文；`\src{snippetNN}` 引用 `code/haskell/snippetNN.hs`（务必对照着读，代码就在那里）；
  - `code/scala`、`code/ocaml` 是其它语言版本，可作参考；
  - 插图已复制到 `docs/public/img/<编号>/`，在 md 中引用为 `/img/<编号>/<文件名>`。
- 每章 Markdown 结构：

```md
# 1.7 函子

（正文……原书每个 \section 对应一个 ## 二级标题，\subsection 对应 ###）

## 挑战

1. ……（原书挑战题全部翻译；可以追加 Lean 版本的题目）

::: details 参考答案
……（尽量给出，Lean 答案要能通过编译）
:::

## 本章小结      ← 新增：用 5~10 条要点回顾本章（帮助基础薄弱的读者）
```

- 原书中的 LaTeX 宏：`\cat{C}` → `$\mathcal{C}$`；`\Set` → `$\mathbf{Set}$`；`\Cat` → `$\mathbf{Cat}$`；
  `\id` → `$\mathrm{id}$`；`\code{x}` → `` `x` ``（并改为对应的 Lean 名字）；`\newterm{x}` → `**x**（英文）`；
  `\emph{x}` → `*x*` 或中文强调；`\urlref`/`\hyperref` → markdown 链接（章节内部链接用 chapters.mjs 中的路径）。
- `lettrine`（首字下沉）忽略即可。

---

## 3. 代码约定（极其重要）

### 3.1 代码块类型

| 写法 | 含义 |
|---|---|
| ```` ```lean ```` | 显示，**会被编译校验**，并带“在线运行”按钮（自动拼上本章此前所有 lean 块） |
| ```` ```lean hidden ```` | 不显示，但参与编译与在线运行。用来放本章需要的前导定义 |
| ```` ```lean no-check ```` | 只显示、不编译。仅用于：故意写错的反例、伪代码、给读者填空的练习骨架 |
| ```` ```rust ```` | 显示，每块**单独**按 lib crate 编译校验（rustc stable, edition 2021） |
| ```` ```rust no-check ```` | 只显示 |
| ```` ```diagram ```` | 交换图 DSL（见 §5） |

**同一章内所有 `lean` / `lean hidden` 块按出现顺序拼接成一个文件编译**（`::: details` 里的也算）。所以：

- 后面的块可以使用前面块定义的东西；
- 同一章内不能重复定义同名东西（需要“换个写法再定义一次”时，用 `namespace Version2 ... end Version2` 包起来，
  或者起不同的名字，如 `fmap'`）；
- 各章之间互相独立。每章必须自包含：需要的定义要在本章（hidden 块里也行）给出。

### 3.2 校验命令（写完必须跑通）

```bash
export PATH=$HOME/.elan/bin:$PATH
node scripts/check-code.mjs docs/part1/07-functors.md     # 只校验你的文件；报错行号已映射回 md
scripts/build-isolated.sh <你的名字>                       # 隔离构建站点，确认没有 Vue/Markdown 编译错误
```

- Lean 版本：4.34.1（见 `lean-toolchain`），**不使用 Mathlib**，只用 Lean 核心库。
- 已校验的代码块中**禁止 `sorry`**（脚本会判失败）。
- 生成的拼接文件在 `build/lean/<路径>.lean`，调试时可以直接 `lean build/lean/xxx.lean`。
- **不要运行任何 git 命令**（多人并行写作，提交由总编统一完成）。
- 不要运行 `npm run build`/`vitepress build docs`（会和别人冲突），只用 `scripts/build-isolated.sh`。

### 3.3 公共前导 `lean/Prelude.lean`

全书统一的范畴论基础定义都在 `lean/Prelude.lean`（已编译通过）：`CTFP.Category`（记号 `a ⟶ b`、`g ⊚ f`、`𝟙 a`）、
`CTFP.typeCategory`（类型与函数的范畴）、`CTFP.CFunctor`（范畴间函子）、`CTFP.NatTrans`（记号 `F ⟹ G`）、`CTFP.Op`（对偶范畴）。

- 章节需要这些时，**原样复制所需片段**（包括 `universe` 声明和 `namespace CTFP ... end CTFP`）到章首的 `lean hidden` 块，
  然后 `open CTFP`。不要自创与之冲突的另一套记号。
- **但在概念第一次被引入的章节**（例如 1.1/1.3 引入范畴、1.7 引入函子、1.10 引入自然变换），应在正文里**展示**这个定义
  并逐行讲解，而不是藏起来。之后的章节再用 hidden 块引入。
- 复合方向与原书一致：`g ⊚ f` = “g 在 f 之后”。对普通 Lean 函数，直接用 Lean 自带的 `g ∘ f`。
- 已知的坑：
  - 对裸 lambda 使用 `⊚` 时，Lean 推断不出用哪个范畴实例。先 `def inc : Nat ⟶ Nat := fun n => n + 1` 起名，再复合。
  - 结构体字段 `obj := List` 之后，`funext xs` 得到的 `xs` 类型是 `F.obj a` 而不是 `List a`，simp 可能失败；
    用 `funext (xs : List a)` 明确标注类型即可。
  - 若在 `typeCategory` 中证明，常用 `funext x; rfl`、`simp [Category.comp, Category.id]`。

### 3.4 与 Lean 核心库的关系

- 编程层面的抽象，**优先使用 Lean 自带的**：`Functor`、`Applicative`、`Monad`、`LawfulFunctor`、`LawfulMonad`、
  `Option`、`Except`、`StateM`/`StateT`、`ReaderT`、`Id`、`Prod`（`α × β`）、`Sum`（`α ⊕ β`）、`Unit`、`Empty`、`List`、`Function.comp` 等，
  并向读者介绍它们（Lean 的 `LawfulFunctor` 把函子定律写进了类型类——这是讲解的好素材）。
- 当需要“从零定义一遍以便讲解”时，放进自己的命名空间避免冲突：

```lean no-check
namespace MyDefs
class Functor (f : Type → Type) where
  fmap : (α → β) → f α → f β
end MyDefs
```

- 与核心库重名的常见名字：`Functor Monad Applicative Id Option Except Prod Sum List Unit Empty Nat Bool id comp
  Function.const Monoid`（核心库没有 `Monoid`，但 Mathlib 有，起名 `Monoid` 也可以，放在命名空间中更安全）。
- `#eval` 的结果请在注释里写出：`#eval double 3 -- 6`。更好的做法是**用能被检查的形式**：
  `example : double 3 = 6 := rfl`，或 `#guard double 3 == 6`。这样读者看到的输出就是被机器验证过的。
- 证明风格：可读优先。多用 `rfl`、`funext`、`simp`、`cases`、`induction`、`intro`、`exact`、`calc`、`decide`，
  并用注释（`-- 中文注释`）解释每一步在干什么。第一次使用某个 tactic 时用一两句话讲清楚它的作用。
- 宇宙（universe）：能用 `Type` 就用 `Type`；只有确实需要时才引入 `Type u`，并解释原因（第一次出现时讲）。
- Lean 是**严格求值、全函数**的语言（没有 Haskell 的惰性和 ⊥ 无处不在）。原书涉及惰性、bottom、`undefined`、无限列表的段落，
  要如实讲清原书观点，再说明 Lean 中的对应（`partial def`、`panic!`、`Thunk`、`Stream`/coinduction 的缺失与替代等）。
  这往往恰好是 Lean 讲得比 Haskell 更清楚的地方：在 Lean 里类型与全函数真的构成范畴 **Set** 的一个好模型。
- 函数复合 `∘`（`\comp`）、积 `×`（`\x`）、和 `⊕`（`\oplus`）、`→`（`\to`）、`fun x => …`、`λ`。

### 3.5 Rust 代码

- 必须能被 stable rustc 编译（`#![allow(dead_code, unused…)]` 已自动加上）；不能用外部 crate。
- 原书 C++ 模板/重载的例子，用 Rust 的泛型、trait、闭包、`impl Fn` 表达。

---

## 4. 盒子（VitePress 容器）

```md
::: info 数学小课堂
给数学基础薄弱的读者补课：直观解释 + 小例子。
:::

::: tip Lean 深入
讲解 Lean 语法或特性；或展示用 Lean 证明定律。
:::

::: tip Rust 视角
用 Rust 程序员熟悉的东西类比。
:::

::: warning 易错点
常见误解。
:::

::: details 参考答案（或：完整证明）
折叠内容。
:::
```

注意：`:::` 容器内部可以放代码块；代码块必须顶格写（不要缩进）。

---

## 5. 图

### 5.1 原书手绘插图

原书插图（猪、烟花……）是本书风格的一部分，**全部保留**，图注翻译成中文：

```md
![复合的示意图](/img/1.1/img_1330.jpg "在范畴中，若有从 A 到 B 的箭头和从 B 到 C 的箭头，就必须有一条从 A 到 C 的直接箭头——它们的复合。")
```

（引号里的 title 会显示为图注。）

### 5.2 交换图 DSL：```` ```diagram ````

原书中 tikz-cd 画的交换图、以及你想额外添加的图，用 diagram 围栏画。**围栏内不能有空行之外的奇怪内容；`#` 开头为注释**。

```diagram
# 节点：  id: (x, y) "KaTeX 标签"   —— 坐标单位约 110px，y 向下；省略标签则用 id
A: (0, 0)
B: (2, 0)
C: (2, 1.5)
AxB: (1, 1) "a \times b"
# 箭头：  id: 起点 -> 终点 "KaTeX 标签" 选项...
f: A -> B
g: B -> C
gf: A -> C "g \circ f" side=right
idA: A -> A "\mathrm{id}_A" loop=left
h: A -> B "h" bend=30 dashed color=red
# 选项：bend=像素（正数向箭头左侧弯）  side=left|right（标签在哪侧） pos=0~1（标签位置）
#       loop=up|down|left|right（自环方向） dashed  color=brand|red|green|orange|purple|gray|任意CSS色  width=线宽
# 箭头种类：->  普通；-->  虚线（表示“唯一存在”的态射）；=>  双线箭头（自然变换）；<->  双向（同构）
# 节点选项：shape=dot（画成小圆点，适合画集合元素）
# 路径动画：path "按钮文字": 箭头id1 箭头id2 ...  color=...   —— 点击按钮，一个光点沿路径依次走过并高亮
path "先 f 再 g": f g
path "直接走 g∘f": gf color=green
caption: 图注文字（可选）
size: 1        # 整体缩放（可选）
```

**交换图的“路径动画”是本书的标志性交互**：凡是“这个图交换”（两条路径相等）的地方，给两条路径各一个 path 按钮，
让读者亲眼看到“走哪条路结果都一样”。

### 5.3 自定义交互组件

需要比交换图更强的交互（例如：可拖拽的范畴构造器、积的泛构造“候选者排名”、Kleisli 复合的逐步执行、
Yoneda 的映射表、F-代数的折叠动画……）时，写 Vue 3 组件：

- 放在 `docs/.vitepress/theme/components/ch/`，文件名 `Ch<编号下划线>Xxx.vue`，例如 `Ch1_5ProductRanking.vue`。
  会被自动全局注册，直接在 md 中 `<Ch1_5ProductRanking />` 使用（独占一行，前后留空行，必须是自闭合 `/>` 写法；
  markdown 插件会自动给它包一层 `<div>`，因为 markdown-it 不认含下划线的标签名）。
- 使用 `<script setup>`，纯前端、无外部依赖（可以用已安装的 `katex`：`import katex from 'katex'`）。
- **必须 SSR 安全**：不要在 setup 顶层访问 `window`/`document`，放到 `onMounted` 里。
- 外层用 `<div class="ctfp-widget">`，标题用 `<div class="ctfp-widget-title">`，按钮可用 `class="ctfp-btn"`；
  颜色用 VitePress CSS 变量（`var(--vp-c-brand-1)`、`var(--vp-c-text-1)`、`var(--vp-c-divider)`、`var(--vp-c-bg-soft)`…），
  这样暗色模式自动适配。样式写在组件的 `<style scoped>` 里。
- 组件里的文字用中文。要有简短的操作提示。移动端宽度下不能溢出（`max-width: 100%`）。
- 每章 1~3 个高质量交互足矣。质量 > 数量。
- 在 markdown 中给组件传复杂 props 时注意：组件标签所在的 HTML 块内**不能有空行**。

---

## 6. 数学公式

- 行内 `$...$`，独立公式 `$$...$$`（独占行）。由 MathJax 渲染，不支持自定义宏，也不支持 tikz-cd（交换图用 §5.2）。
- `$` 内外与中文之间不需要空格，但 `$` 紧挨着的内侧不要有空格：写 `$a \to b$`，不要写 `$ a \to b $`。
- 常用：`\mathcal{C}`、`\mathbf{Set}`、`\circ`、`\to`、`\times`、`+`、`\cong`、`\Rightarrow`、`\mathrm{id}_a`、
  `\mathcal{C}(a, b)`（hom-set）、`\int_c`（端）、`\eta`、`\mu`、`\varepsilon`。

---

## 7. 中文写作风格

- 用“你”称呼读者，保持原书和读者聊天的感觉。可以保留 Milewski 的个人叙述（“我”指原作者）。
- 中文标点（，。：；“”（）），中英文之间加空格（`Lean 4 的类型类`），代码标识符用反引号。
- 不要使用 emoji。
- 长句拆短。先给直觉和例子，再给定义，再给 Lean 代码，再给证明。
- 原书中针对 Haskell/C++ 程序员的文化梗，可以替换为 Rust/Lean 程序员能会心一笑的版本，但原意要保留。

---

## 8. 术语表（必须统一）

| English | 中文 | 备注 |
|---|---|---|
| category | 范畴 | |
| object | 对象 | |
| morphism / arrow | 态射 / 箭头 | 两者混用，同原书 |
| composition | 复合 | 不用“组合” |
| identity (morphism) | 恒等态射 | |
| associativity | 结合律 | |
| hom-set | hom-集 | 首次出现解释为“态射集合” |
| monoid | 幺半群 | |
| preorder / partial order / total order | 预序 / 偏序 / 全序 | |
| thin category | 瘦范畴 | |
| free category | 自由范畴 | |
| Kleisli category | Kleisli 范畴 | |
| embellished function | 修饰函数 | 原书 Kleisli 章 |
| universal construction / property | 泛构造 / 泛性质 | |
| initial / terminal object | 始对象 / 终对象 | |
| isomorphism / isomorphic | 同构 | |
| unique up to isomorphism | 在同构意义下唯一 | |
| duality / dual | 对偶 | |
| opposite category | 对偶范畴（反范畴） | 记 $\mathcal{C}^{op}$ |
| product / coproduct | 积 / 余积 | |
| projection / injection | 投影 / 内射 | |
| algebraic data type | 代数数据类型 | |
| sum type / product type | 和类型 / 积类型 | |
| record | 记录（结构体） | Lean 中为 `structure` |
| functor / endofunctor | 函子 / 自函子 | |
| bifunctor / profunctor | 双函子 / 剖函子（profunctor） | |
| covariant / contravariant | 协变 / 逆变 | |
| functoriality | 函子性 | |
| function type / exponential | 函数类型 / 指数对象 | |
| currying | 柯里化 | |
| cartesian closed category | 笛卡尔闭范畴 | |
| natural transformation | 自然变换 | |
| naturality condition / square | 自然性条件 / 自然性方块 | |
| functor category | 函子范畴 | |
| horizontal / vertical composition | 水平 / 垂直复合 | |
| 2-category | 2-范畴 | |
| limit / colimit | 极限 / 余极限 | |
| cone / cocone | 锥 / 余锥 | |
| pullback / pushout | 拉回 / 推出 | |
| equalizer / coequalizer | 等化子 / 余等化子 | |
| continuity (of functors) | 连续性 | |
| free monoid | 自由幺半群 | |
| forgetful functor | 遗忘函子 | |
| representable functor | 可表函子 | |
| Yoneda lemma / embedding | 米田引理 / 米田嵌入 | 首次出现注“Yoneda” |
| presheaf | 预层 | |
| adjunction / left adjoint / right adjoint | 伴随 / 左伴随 / 右伴随 | |
| unit / counit | 单位 / 余单位 | |
| monad / comonad | 单子 / 余单子 | |
| Kleisli arrow | Kleisli 箭头 | |
| monoidal category | 幺半范畴 | |
| tensor product | 张量积 | |
| F-algebra / coalgebra | F-代数 / F-余代数 | |
| initial algebra / terminal coalgebra | 始代数 / 终余代数 | |
| catamorphism / anamorphism | 卡塔态射（catamorphism）/ 安娜态射（anamorphism） | 首次出现附英文 |
| fixed point | 不动点 | |
| Eilenberg–Moore category | Eilenberg–Moore 范畴 | |
| end / coend | 端 / 余端 | |
| Kan extension | Kan 扩张 | |
| enriched category | 富集范畴 | |
| topos / subobject classifier | 拓扑斯 / 子对象分类子 | |
| Lawvere theory | Lawvere 理论 | |
| section / retraction | 截面 / 收缩 | |
| monomorphism / epimorphism | 单态射 / 满态射 | |
| injective / surjective / bijective | 单射 / 满射 / 双射 | |
| type class | 类型类 | |
| instance | 实例 | |
| pure function | 纯函数 | |
| side effect | 副作用 | |
| total / partial function | 全函数 / 偏函数 | |
| bottom | 底（⊥） | |
| lens | 透镜（lens） | |
| writer / reader / state monad | Writer / Reader / State 单子 | 名字保留英文 |
