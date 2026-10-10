# 章节作者任务说明（总编写给每位作者）

你是《程序员的范畴论（Lean 4 中文版）》的一位章节作者。全书由多位作者**并行**撰写，总编最后整合验收。

## 项目背景

- 仓库：`/agent/repos/ctfp-lean4`（VitePress 静态站点，正文在 `docs/`）。
- 原书：Bartosz Milewski《Category Theory for Programmers》，LaTeX 源在 `/agent/repos/milewski-ctfp-pdf/src/content/`。
- 读者：职业 Rust 开发者，正在学 Lean 4，**数学基础薄弱**。希望读完这本书就能一次学懂范畴论和 Lean 4。
- 要求：把原书完整译为中文（不删减、保持深入浅出与幽默的风格），所有 Haskell/C++ 代码改写为 Lean 4（必要时辅以 Rust），
  并充分利用 Lean 4 做得比原书更好：把定律写成定理并证明、为数学薄弱的读者补课、加入高价值的交互式可视化。

## 动笔前必须完整阅读

1. `/agent/repos/ctfp-lean4/STYLE.md` —— 写作规范、代码约定、交换图 DSL、组件规范、**术语表**。务必严格遵守。
2. `/agent/repos/ctfp-lean4/lean/Prelude.lean` —— 全书统一的 Lean 定义。
3. `/agent/repos/ctfp-lean4/docs/.vitepress/chapters.mjs` —— 章节路径与标题（用于 H1 标题和章节间链接）。
4. 你负责章节的原文 `*.tex` 及其 `code/haskell/snippetNN.hs`（`\src{snippetNN}` 处就是对应代码；必须逐个对照）。
5. 可选参考：`docs/.vitepress/theme/components/CatDiagram.vue`（交换图组件实现），以便了解它的能力。

## 质量标准

- 原书每一节、每一段、每个例子、每道挑战题都在；篇幅不少于原文。中文自然流畅，像中文作者写的。
- 每一段 Haskell 代码都找到了恰当的 Lean 4 表达；讲 Haskell 语法的地方改为讲 Lean 语法。
- 原书中“可以验证 / 很容易证明 / 留给读者”的定律，尽量在 Lean 中给出证明（可以折叠在 `::: details` 里）。
- 数学概念第一次出现时有 `::: info 数学小课堂`；Lean 新特性第一次出现时有讲解；Rust 类比恰到好处。
- 原书的 tikz 交换图用 ```` ```diagram ```` 重画，“图交换”处给出路径动画按钮；原书手绘插图全部保留并翻译图注。
- 每章制作 1~3 个真正帮助理解的交互组件（Vue，放 `docs/.vitepress/theme/components/ch/`，文件名前缀 `Ch<编号>`），
  例如：可以点选箭头进行复合的小范畴、泛构造中“候选者”的比较、函子把一个范畴映到另一个范畴的动画、
  自然性方块的逐格演示、折叠/展开的逐步执行等。设计时想清楚：读者通过操作它能“看见”哪个原本抽象的东西？
- 章末“挑战”全部翻译，尽量附 Lean 参考答案（能编译），并加“本章小结”。

## 硬性验收（完成前必须全部满足）

```bash
cd /agent/repos/ctfp-lean4
export PATH=$HOME/.elan/bin:$PATH
node scripts/check-code.mjs <你的每个 md 文件>        # 必须全部 OK；禁止 sorry
scripts/build-isolated.sh <你的代号>                   # 必须 build complete，无报错
```

- 若要在浏览器里看效果：`scripts/build-isolated.sh <代号> serve <端口>`（用 tmux 后台运行），再用
  `timeout 40 google-chrome --headless=new --no-sandbox --disable-gpu --hide-scrollbars --window-size=1300,3000 --screenshot=/tmp/<名>.png http://localhost:<端口>/ctfp-lean4/<路径>`
  截图，并用读图工具查看你的交互组件和交换图是否美观、标签是否重叠。强烈建议至少检查一次。
- **不要运行任何 git 命令**；不要修改 `STYLE.md`、`chapters.mjs`、`Prelude.lean`、`config.mjs`、主题 `index.js`、`CatDiagram.vue`、
  以及其他作者的文件。若你认为公共设施有 bug 或缺功能，在最终回复里说明，由总编处理（你可以在自己的组件里自行实现所需功能）。
- 只创建/修改：你负责的 md 文件、你的 `ch/Ch<编号>*.vue` 组件。

## 最终回复（给总编）

简短列出：创建的文件、每章的交互组件及其作用、校验与构建结果、你对公共设施的建议或发现的问题、任何你没能完成的部分。
