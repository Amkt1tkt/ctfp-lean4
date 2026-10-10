import { defineConfig } from 'vitepress'
import { parts } from './chapters.mjs'
import { fencePlugin } from './fences.mjs'

const base = process.env.BASE ?? '/ctfp-lean4/'

const sidebar = parts.map((p) => ({
  text: p.text,
  collapsed: false,
  items: p.items.map((c) => ({ text: `${c.num}　${c.title}`, link: c.link })),
}))

export default defineConfig({
  lang: 'zh-CN',
  title: '程序员的范畴论',
  titleTemplate: ':title · 程序员的范畴论（Lean 4 版）',
  description: 'Bartosz Milewski《Category Theory for Programmers》的中文 Lean 4 改写版',
  base,
  cleanUrls: true,
  lastUpdated: true,
  head: [['link', { rel: 'icon', href: `${base}favicon.svg` }]],
  markdown: {
    math: true,
    lineNumbers: false,
    theme: { light: 'github-light', dark: 'github-dark' },
    config(md) {
      md.use(fencePlugin)
    },
  },
  vite: {
    ssr: { noExternal: ['katex'] },
  },
  themeConfig: {
    nav: [
      { text: '开始阅读', link: '/guide/lean-for-rustaceans' },
      { text: '目录', link: '/contents' },
      { text: '术语表', link: '/appendix/glossary' },
    ],
    sidebar,
    outline: { level: [2, 3], label: '本页目录' },
    docFooter: { prev: '上一章', next: '下一章' },
    darkModeSwitchLabel: '外观',
    sidebarMenuLabel: '目录',
    returnToTopLabel: '回到顶部',
    lastUpdated: { text: '最后更新' },
    search: {
      provider: 'local',
      options: {
        translations: {
          button: { buttonText: '搜索', buttonAriaLabel: '搜索' },
          modal: { noResultsText: '没有结果', resetButtonTitle: '清除', footer: { selectText: '选择', navigateText: '切换', closeText: '关闭' } },
        },
      },
    },
    socialLinks: [{ icon: 'github', link: 'https://github.com/Amkt1tkt/ctfp-lean4' }],
    footer: {
      message: '基于 Bartosz Milewski《Category Theory for Programmers》改写，以 CC BY-SA 4.0 授权',
    },
  },
})
