// 全书章节清单：侧边栏、校验脚本、写作分工都以此为准。
// src 指向原书 LaTeX 源（milewski-ctfp-pdf/src/content/<src>）。

export const parts = [
  {
    text: '开始之前',
    items: [
      { num: '0.1', title: 'Lean 4 速成：写给 Rust 程序员', link: '/guide/lean-for-rustaceans' },
      { num: '0.2', title: '数学工具箱：读这本书需要的全部数学', link: '/guide/math-toolkit' },
      { num: '0.3', title: '序言', link: '/preface', src: '0.0' },
    ],
  },
  {
    text: '第一部分',
    items: [
      { num: '1.1', title: '范畴：复合的本质', link: '/part1/01-category', src: '1.1' },
      { num: '1.2', title: '类型与函数', link: '/part1/02-types-and-functions', src: '1.2' },
      { num: '1.3', title: '大大小小的范畴', link: '/part1/03-categories-great-and-small', src: '1.3' },
      { num: '1.4', title: 'Kleisli 范畴', link: '/part1/04-kleisli-categories', src: '1.4' },
      { num: '1.5', title: '积与余积', link: '/part1/05-products-and-coproducts', src: '1.5' },
      { num: '1.6', title: '简单代数数据类型', link: '/part1/06-simple-algebraic-data-types', src: '1.6' },
      { num: '1.7', title: '函子', link: '/part1/07-functors', src: '1.7' },
      { num: '1.8', title: '函子性', link: '/part1/08-functoriality', src: '1.8' },
      { num: '1.9', title: '函数类型', link: '/part1/09-function-types', src: '1.9' },
      { num: '1.10', title: '自然变换', link: '/part1/10-natural-transformations', src: '1.10' },
    ],
  },
  {
    text: '第二部分',
    items: [
      { num: '2.1', title: '声明式编程', link: '/part2/01-declarative-programming', src: '2.1' },
      { num: '2.2', title: '极限与余极限', link: '/part2/02-limits-and-colimits', src: '2.2' },
      { num: '2.3', title: '自由幺半群', link: '/part2/03-free-monoids', src: '2.3' },
      { num: '2.4', title: '可表函子', link: '/part2/04-representable-functors', src: '2.4' },
      { num: '2.5', title: '米田引理', link: '/part2/05-the-yoneda-lemma', src: '2.5' },
      { num: '2.6', title: '米田嵌入', link: '/part2/06-yoneda-embedding', src: '2.6' },
    ],
  },
  {
    text: '第三部分',
    items: [
      { num: '3.1', title: '一切皆关乎态射', link: '/part3/01-its-all-about-morphisms', src: '3.1' },
      { num: '3.2', title: '伴随', link: '/part3/02-adjunctions', src: '3.2' },
      { num: '3.3', title: '自由/遗忘伴随', link: '/part3/03-free-forgetful-adjunctions', src: '3.3' },
      { num: '3.4', title: '单子：程序员的定义', link: '/part3/04-monads-programmers-definition', src: '3.4' },
      { num: '3.5', title: '单子与副作用', link: '/part3/05-monads-and-effects', src: '3.5' },
      { num: '3.6', title: '范畴论视角下的单子', link: '/part3/06-monads-categorically', src: '3.6' },
      { num: '3.7', title: '余单子', link: '/part3/07-comonads', src: '3.7' },
      { num: '3.8', title: 'F-代数', link: '/part3/08-f-algebras', src: '3.8' },
      { num: '3.9', title: '单子的代数', link: '/part3/09-algebras-for-monads', src: '3.9' },
      { num: '3.10', title: '端与余端', link: '/part3/10-ends-and-coends', src: '3.10' },
      { num: '3.11', title: 'Kan 扩张', link: '/part3/11-kan-extensions', src: '3.11' },
      { num: '3.12', title: '富集范畴', link: '/part3/12-enriched-categories', src: '3.12' },
      { num: '3.13', title: '拓扑斯', link: '/part3/13-topoi', src: '3.13' },
      { num: '3.14', title: 'Lawvere 理论', link: '/part3/14-lawvere-theories', src: '3.14' },
      { num: '3.15', title: '单子、幺半群与范畴', link: '/part3/15-monads-monoids-and-categories', src: '3.15' },
    ],
  },
  {
    text: '附录',
    items: [
      { num: 'A', title: '术语表（中英对照）', link: '/appendix/glossary' },
      { num: 'B', title: '关于本书与版权', link: '/appendix/about' },
    ],
  },
]

export const chapters = parts.flatMap((p) => p.items)
