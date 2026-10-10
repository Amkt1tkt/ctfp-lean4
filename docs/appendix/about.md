# B 关于本书与版权

## 原书

本书改写自 **Bartosz Milewski** 的《Category Theory for Programmers》（《程序员的范畴论》）。原书最初以
[博客文章](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)形式连载，
后由 Igal Tabachnik 整理为 [LaTeX 版本](https://github.com/hmemcpy/milewski-ctfp-pdf)。

原书文字与插图以 [知识共享 署名-相同方式共享 4.0 国际许可协议（CC BY-SA 4.0）](https://creativecommons.org/licenses/by-sa/4.0/deed.zh-hans) 发布。
本书沿用原书全部手绘插图，版权归原作者所有。

## 本书做了什么

- 全文翻译为中文，保留原书的全部章节、论证与挑战题；
- 原书的 Haskell 与 C++ 代码全部改写为 **Lean 4**（必要时辅以 **Rust**）；
- 借助 Lean 4 的依值类型，把原书中“请读者自行验证”的定律写成定理并给出证明；
- 为数学基础薄弱的读者增加了“数学小课堂”、Rust 对照、交互式交换图与可视化组件；
- 书中所有 Lean 与 Rust 代码都经过编译校验。

## 许可

作为演绎作品，本书同样以 **CC BY-SA 4.0** 发布。你可以自由地分享与改编，但需署名并以相同协议发布。

## 技术

- 站点：[VitePress](https://vitepress.dev/)
- 代码校验：Lean 4（不依赖 Mathlib）、rustc
- “在线运行”使用 [Lean 4 Web](https://live.lean-lang.org/)
