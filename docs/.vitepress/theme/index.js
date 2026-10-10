import DefaultTheme from 'vitepress/theme'
import { onMounted, watch, nextTick } from 'vue'
import { useRoute } from 'vitepress'
import 'katex/dist/katex.min.css'
import './style.css'

// components/ 下（含子目录）的所有 .vue 组件按文件名自动全局注册，
// 章节专属组件放 components/ch/<Ch1_1Xxx>.vue 即可直接在 md 中使用。
const modules = import.meta.glob('./components/**/*.vue', { eager: true })

const LEAN_WEB = 'https://live.lean-lang.org/#code='

function decorateLeanBlocks() {
  const all = Array.from(document.querySelectorAll('.vp-doc .lean-src'))
  all.forEach((el, i) => {
    if (!el.classList.contains('lean-runnable') || el.querySelector('.lean-run')) return
    const btn = document.createElement('a')
    btn.className = 'lean-run'
    btn.target = '_blank'
    btn.rel = 'noopener'
    btn.textContent = '▶ 在线运行'
    btn.title = '在 Lean 4 Web 中打开（自动带上本章此前的所有 Lean 代码）'
    btn.addEventListener('click', () => {
      const code = all
        .slice(0, i + 1)
        .map((e) => e.querySelector('pre')?.textContent ?? '')
        .map((s) => s.replace(/\n+$/, ''))
        .join('\n\n')
      btn.href = LEAN_WEB + encodeURIComponent(code + '\n')
    })
    el.appendChild(btn)
  })
}

export default {
  extends: DefaultTheme,
  enhanceApp({ app }) {
    for (const [file, mod] of Object.entries(modules)) {
      const name = file.split('/').pop().replace(/\.vue$/, '')
      app.component(name, mod.default)
    }
  },
  setup() {
    const route = useRoute()
    onMounted(() => decorateLeanBlocks())
    watch(
      () => route.path,
      () => nextTick(() => setTimeout(decorateLeanBlocks, 50)),
    )
  },
}
