// 自定义代码围栏（fence）约定，markdown 渲染与 scripts/check-code.mjs 共用。
//
//   ```lean            显示 + 编译校验 + “在线运行”按钮（会带上本章此前所有 lean 代码）
//   ```lean hidden     不显示，但参与编译与在线运行（放 import / 前导定义）
//   ```lean no-check   只显示，不校验（故意写错的反例、伪代码）
//   ```rust            显示 + 单独编译校验（每块独立，按 lib crate 编译）
//   ```rust no-check   只显示
//   ```diagram         交换图 DSL，渲染为 <CatDiagram>（语法见 STYLE.md）

const FLAGS = ['hidden', 'no-check']

export function classifyFence(info) {
  const words = (info || '').trim().split(/\s+/).filter(Boolean)
  const lang = (words[0] || '').toLowerCase()
  const flags = new Set(words.filter((w) => FLAGS.includes(w)))
  const rest = words.slice(1).filter((w) => !FLAGS.includes(w))
  return {
    lang,
    hidden: flags.has('hidden'),
    noCheck: flags.has('no-check'),
    restInfo: [words[0] || '', ...rest].join(' '),
  }
}

const escapeHtml = (s) =>
  s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;')

export function fencePlugin(md) {
  // markdown-it 的 HTML 块只认 [A-Za-z][A-Za-z0-9-]* 形式的标签名，`<Ch1_3Xxx />` 会被当成纯文本；
  // 独占行的章节组件标签自动包一层 <div>。
  md.core.ruler.before('block', 'ctfp-chapter-components', (state) => {
    state.src = state.src.replace(/^([ \t]*)(<Ch\d+_\d+[A-Za-z0-9]*\b[\s\S]*?\/>)[ \t]*$/gm, '$1<div>$2</div>')
  })

  const orig = md.renderer.rules.fence
  md.renderer.rules.fence = (tokens, idx, options, env, self) => {
    const token = tokens[idx]
    const f = classifyFence(token.info)
    if (f.lang === 'diagram') {
      return `<CatDiagram spec="${escapeHtml(token.content)}" />\n`
    }
    if (f.lang === 'lean' || f.lang === 'lean4') {
      if (f.hidden) {
        return `<div class="lean-src lean-hidden" v-pre style="display:none"><pre>${escapeHtml(token.content)}</pre></div>\n`
      }
      token.info = f.restInfo
      const html = orig(tokens, idx, options, env, self)
      if (f.noCheck) return `<div class="lean-nocheck">${html}</div>`
      return `<div class="lean-src lean-runnable">${html}</div>`
    }
    if (f.lang === 'rust') token.info = f.restInfo
    return orig(tokens, idx, options, env, self)
  }

  // ![说明](/img/x.jpg "图注") —— 有 title 时在图片下方显示图注。
  const origImage = md.renderer.rules.image
  md.renderer.rules.image = (tokens, idx, options, env, self) => {
    const title = tokens[idx].attrGet('title')
    const html = origImage(tokens, idx, options, env, self)
    return title ? `${html}<span class="img-caption">${md.utils.escapeHtml(title)}</span>` : html
  }
}
