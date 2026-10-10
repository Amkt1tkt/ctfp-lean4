<script setup>
import { ref, computed } from 'vue'

const input = ref('hello monad world')
const grouping = ref('left')
const retLeft = ref(false)
const retRight = ref(false)
const step = ref(99)

const COLORS = ['#3b82f6', '#16a34a', '#ea580c', '#9333ea', '#64748b']

const show = (v) => (Array.isArray(v) ? '[' + v.map((s) => JSON.stringify(s)).join(', ') + ']' : JSON.stringify(v))

const ARROWS = {
  ret: { name: 'ret', sig: 'α → Writer String α', log: '', run: (v) => v, color: 4 },
  f: { name: 'upCase', sig: 'String → Writer String String', log: 'upCase ', run: (s) => s.toUpperCase(), color: 0 },
  g: { name: 'toWords', sig: 'String → Writer String (List String)', log: 'toWords ', run: (s) => s.split(' ').filter((w) => w !== ''), color: 1 },
  h: { name: 'count', sig: 'List String → Writer String Nat', log: 'count ', run: (ws) => ws.length, color: 2 },
}

const chain = computed(() => {
  const ks = ['f', 'g', 'h']
  if (retLeft.value) ks.unshift('ret')
  if (retRight.value) ks.push('ret')
  return ks.map((k) => ARROWS[k])
})

const stages = computed(() => {
  let v = input.value
  const out = [{ value: v, log: '' }]
  let log = ''
  for (const a of chain.value) {
    v = a.run(v)
    log += a.log
    out.push({ value: v, log, arrow: a })
  }
  return out
})

const k = computed(() => Math.min(step.value, chain.value.length))

// 把日志拼接的括号结构画出来
function tree(arrs, dir) {
  if (arrs.length === 1) return { leaf: arrs[0] }
  if (dir === 'left') return { l: tree(arrs.slice(0, -1), dir), r: { leaf: arrs[arrs.length - 1] } }
  return { l: { leaf: arrs[0] }, r: tree(arrs.slice(1), dir) }
}
function render(t, top = true) {
  if (t.leaf) {
    const a = t.leaf
    const txt = a.log === '' ? '""' : JSON.stringify(a.log)
    return `<span style="color:${COLORS[a.color]};font-weight:600">${txt}</span>`
  }
  const s = `${render(t.l, false)} <span class="op">&lt;&gt;</span> ${render(t.r, false)}`
  return top ? s : `<span class="paren">(</span>${s}<span class="paren">)</span>`
}
function renderFish(t, top = true) {
  if (t.leaf) return `<span style="color:${COLORS[t.leaf.color]};font-weight:600">${t.leaf.name}</span>`
  const s = `${renderFish(t.l, false)} <span class="op">&gt;=&gt;</span> ${renderFish(t.r, false)}`
  return top ? s : `<span class="paren">(</span>${s}<span class="paren">)</span>`
}

const fishHtml = computed(() => renderFish(tree(chain.value, grouping.value)))
const logHtml = computed(() => render(tree(chain.value, grouping.value)))
const final = computed(() => stages.value[stages.value.length - 1])
const otherFish = computed(() => renderFish(tree(chain.value, grouping.value === 'left' ? 'right' : 'left')))

function next() {
  step.value = Math.min(k.value + 1, chain.value.length)
}
function prev() {
  step.value = Math.max(k.value - 1, 0)
}
</script>

<template>
  <div class="ctfp-widget kw">
    <div class="ctfp-widget-title">Kleisli 复合实验台：Writer 单子里的“鱼”</div>
    <p class="hint">输入一段文字，看它依次穿过几个记日志的 Kleisli 箭头。切换括号方式、在两头插入 <code>ret</code>，观察最终结果是否改变。</p>

    <div class="row">
      <label>输入 <input v-model="input" class="txt" /></label>
    </div>
    <div class="row">
      <button class="ctfp-btn" :class="{ on: grouping === 'left' }" @click="grouping = 'left'">左结合 (f &gt;=&gt; g) &gt;=&gt; h</button>
      <button class="ctfp-btn" :class="{ on: grouping === 'right' }" @click="grouping = 'right'">右结合 f &gt;=&gt; (g &gt;=&gt; h)</button>
    </div>
    <div class="row">
      <label><input type="checkbox" v-model="retLeft" /> 左边接 <code>ret</code></label>
      <label><input type="checkbox" v-model="retRight" /> 右边接 <code>ret</code></label>
    </div>

    <div class="expr"><span class="lbl">复合：</span><span v-html="fishHtml" /></div>

    <div class="pipe">
      <div class="stage">
        <div class="box start">
          <div class="v">{{ show(stages[0].value) }}</div>
          <div class="l">日志：<i>（尚无）</i></div>
        </div>
      </div>
      <template v-for="(s, i) in stages.slice(1)" :key="i">
        <div class="arrow" :class="{ lit: i < k }" :style="{ '--c': COLORS[s.arrow.color] }">
          <span class="an">{{ s.arrow.name }}</span>
          <span class="as">{{ s.arrow.sig }}</span>
          <span class="al">记录 {{ s.arrow.log === '' ? '""（mempty）' : JSON.stringify(s.arrow.log) }}</span>
        </div>
        <div class="stage" :class="{ hidden: i >= k }">
          <div class="box" :style="{ borderColor: COLORS[s.arrow.color] }">
            <div class="v">{{ show(s.value) }}</div>
            <div class="l">日志：{{ JSON.stringify(s.log) }}</div>
          </div>
        </div>
      </template>
    </div>

    <div class="row">
      <button class="ctfp-btn" @click="prev" :disabled="k === 0">上一步</button>
      <button class="ctfp-btn" @click="next" :disabled="k >= chain.length">下一步</button>
      <button class="ctfp-btn" @click="step = 0">从头开始</button>
      <button class="ctfp-btn" @click="step = 99">全部执行</button>
    </div>

    <div class="result" v-if="k >= chain.length">
      <div><span class="lbl">日志的拼接结构：</span><span v-html="logHtml" /></div>
      <div><span class="lbl">最终结果：</span><code>⟨({{ show(final.value) }}, {{ JSON.stringify(final.log) }})⟩</code></div>
      <div class="note">
        换成 <span v-html="otherFish" />，日志的括号会换一种方式，但由于字符串拼接满足<b>结合律</b>，结果一字不差；
        <code>ret</code> 贡献的是空串 <code>""</code>，它是拼接的<b>单位元</b>，所以加不加 <code>ret</code> 都一样。
        这正是 Writer 单子定律来自幺半群定律的直观原因。
      </div>
    </div>
  </div>
</template>

<style scoped>
.kw, .kw * { font-variant-ligatures: none; font-feature-settings: "liga" 0, "calt" 0; }
.kw .hint { font-size: 13px; color: var(--vp-c-text-2); margin: 0 0 10px; line-height: 1.6; }
.row { display: flex; flex-wrap: wrap; gap: 8px 14px; align-items: center; margin: 8px 0; font-size: 13px; }
.txt { border: 1px solid var(--vp-c-divider); border-radius: 6px; padding: 3px 8px; background: var(--vp-c-bg); color: var(--vp-c-text-1); width: 220px; max-width: 60vw; font-family: var(--vp-font-family-mono); }
.expr, .result { font-family: var(--vp-font-family-mono); font-size: 13px; margin: 10px 0; padding: 8px 10px; background: var(--vp-c-bg); border-radius: 8px; border: 1px dashed var(--vp-c-divider); overflow-x: auto; }
.result > div { margin: 4px 0; }
.lbl { color: var(--vp-c-text-2); font-family: var(--vp-font-family-base); }
.expr :deep(.op), .result :deep(.op) { color: var(--vp-c-text-2); }
.expr :deep(.paren), .result :deep(.paren) { color: var(--vp-c-text-3); font-weight: 700; }
.pipe { display: flex; flex-direction: column; align-items: stretch; gap: 2px; margin: 10px 0; }
.stage { display: flex; justify-content: center; transition: opacity 0.3s; }
.stage.hidden { opacity: 0.15; }
.box { border: 2px solid var(--vp-c-divider); border-radius: 10px; padding: 6px 12px; background: var(--vp-c-bg); min-width: 240px; max-width: 100%; text-align: center; }
.box .v { font-family: var(--vp-font-family-mono); font-size: 14px; color: var(--vp-c-text-1); word-break: break-all; }
.box .l { font-size: 12px; color: var(--vp-c-text-2); font-family: var(--vp-font-family-mono); word-break: break-all; }
.arrow { display: flex; flex-direction: column; align-items: center; font-size: 12px; color: var(--vp-c-text-3); padding: 2px 0 2px; position: relative; }
.arrow::before { content: '↓'; font-size: 18px; line-height: 1; }
.arrow.lit { color: var(--c); }
.arrow .an { font-weight: 700; font-family: var(--vp-font-family-mono); }
.arrow .as, .arrow .al { font-family: var(--vp-font-family-mono); font-size: 11px; }
.note { font-family: var(--vp-font-family-base); color: var(--vp-c-text-2); line-height: 1.7; margin-top: 6px !important; }
button:disabled { opacity: 0.4; cursor: default; }
</style>
