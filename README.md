# 程序员的范畴论（Lean 4 中文版）

Bartosz Milewski《Category Theory for Programmers》的中文改写版：原书的 Haskell / C++ 全部改为 **Lean 4**（辅以 Rust），
并借助 Lean 把原书中的定律写成可以被机器检查的定理；为数学基础薄弱的读者增加了大量补充讲解与交互式图示。

## 本地运行

```bash
npm ci
npm run dev        # http://localhost:5173/ctfp-lean4/
```

## 校验书中代码

需要 [elan](https://github.com/leanprover/elan)（Lean 4 工具链，版本见 `lean-toolchain`）和 stable Rust：

```bash
npm run check                                   # 编译校验全部 Lean / Rust 代码块
node scripts/check-code.mjs docs/part1/01-category.md   # 只校验一章
```

## 部署到 GitHub Pages

仓库已带 `.github/workflows/deploy.yml`：在仓库 Settings → Pages 中把 Source 设为 **GitHub Actions**，
之后每次推送到 `main` 都会自动校验代码、构建并发布。站点默认部署在 `/<仓库名>/` 路径下（由 `BASE` 环境变量控制）。

## 目录结构

```
docs/                   书的正文（Markdown）
docs/.vitepress/        站点配置、主题、交互组件（components/）
docs/public/img/        原书插图
lean/Prelude.lean       全书共用的范畴论基础定义
scripts/check-code.mjs  代码块抽取与编译校验
STYLE.md                写作规范
```

## 许可

CC BY-SA 4.0，与原书相同。原书插图版权归 Bartosz Milewski。
