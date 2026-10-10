<script setup>
// 自由幺半群“只记账、不计算”：同一个列表可以被唯一的同态解释到不同的幺半群里；
// 比较两个列表：在 List 中不同，在目标幺半群中可能被“认同”为同一个元素。
import { computed, ref } from 'vue'

const GENS = [1, 2, 3, 5, 6]
const MONOIDS = [
  { id: 'add', name: '(ℕ, +, 0)', unit: 0, op: (a, b) => a + b, sym: '+', gen: (g) => g, show: String },
  { id: 'mul', name: '(ℕ, ×, 1)', unit: 1, op: (a, b) => a * b, sym: '×', gen: (g) => g, show: String },
  { id: 'max', name: '(ℕ, max, 0)', unit: 0, op: (a, b) => Math.max(a, b), sym: 'max', gen: (g) => g, show: String, prefix: true },
  { id: 'xor', name: '(Bool, xor, false)：模 2 加法', unit: false, op: (a, b) => a !== b, sym: 'xor', gen: (g) => g % 2 === 1, show: (b) => (b ? 'true' : 'false') },
  { id: 'str', name: '(String, ++, "")', unit: '', op: (a, b) => a + b, sym: '++', gen: (g) => String(g), show: (s) => JSON.stringify(s) },
]
const mId = ref('mul')
const M = computed(() => MONOIDS.find((m) => m.id === mId.value))

const lists = ref({ A: [2, 3], B: [6] })
const target = ref('A')
const push = (g) => lists.value[target.value].push(g)
const pop = () => lists.value[target.value].pop()
const clear = () => (lists.value[target.value] = [])

const h = (xs) => xs.reduceRight((acc, g) => M.value.op(M.value.gen(g), acc), M.value.unit)
const trace = (xs) => {
  const m = M.value
  if (!xs.length) return `h [] = ${m.show(m.unit)}`
  const parts = xs.map((g) => m.show(m.gen(g)))
  const expr = m.prefix
    ? parts.reduceRight((acc, p) => `max ${p} (${acc})`, m.show(m.unit))
    : parts.map((p) => p).join(` ${m.sym} `) + ` ${m.sym} ${m.show(m.unit)}`
  return `h [${xs.join(', ')}] = ${expr} = ${m.show(h(xs))}`
}
const sameList = computed(() => JSON.stringify(lists.value.A) === JSON.stringify(lists.value.B))
const sameImg = computed(() => h(lists.value.A) === h(lists.value.B))
const genOut = (g) => M.value.show(M.value.gen(g))
</script>

<template>
  <div class="ctfp-widget fme">
    <div class="ctfp-widget-title">自由幺半群只记账、不计算：同一个列表，不同的解释</div>
    <div class="fme-row">
      <span class="lbl">目标幺半群 m：</span>
      <button v-for="m in MONOIDS" :key="m.id" class="ctfp-btn" :class="{ on: mId === m.id }" @click="mId = m.id">{{ m.name }}</button>
    </div>
    <div class="fme-row small">
      <span class="lbl">生成元函数 f : x → U m：</span>
      <span v-for="g in GENS" :key="'f' + g" class="gen-map"><code>{{ g }} ↦ {{ genOut(g) }}</code></span>
    </div>
    <p class="fme-hint">
      选中列表 A 或 B，点下面的生成元往里追加。每个列表都是自由幺半群 <code>List x</code> 的一个元素——它只是把“要乘的东西”记下来。
      唯一的同态 <code>h = lift f</code> 把它解释（折叠）进 m。
    </p>
    <div class="fme-lists">
      <div v-for="k in ['A', 'B']" :key="k" class="fme-list" :class="{ active: target === k }" @click="target = k">
        <div class="fme-list-head">列表 {{ k }}{{ target === k ? '（正在编辑）' : '' }}</div>
        <div class="fme-chips">
          <span class="bracket">[</span>
          <span v-for="(g, i) in lists[k]" :key="i" class="chip">{{ g }}</span>
          <span class="bracket">]</span>
        </div>
        <div class="fme-trace"><code>{{ trace(lists[k]) }}</code></div>
      </div>
    </div>
    <div class="fme-row">
      <span class="lbl">向 {{ target }} 追加：</span>
      <button v-for="g in GENS" :key="'g' + g" class="ctfp-btn" @click="push(g)">{{ g }}</button>
      <button class="ctfp-btn" @click="pop">撤销</button>
      <button class="ctfp-btn" @click="clear">清空</button>
    </div>
    <div class="fme-verdict">
      <div>在自由幺半群 <code>List x</code> 中：A {{ sameList ? '=' : '≠' }} B
        <span class="muted">（列表只有逐项相同才相等——没有多余的等式）</span></div>
      <div>在 m = {{ M.name }} 中：h A {{ sameImg ? '=' : '≠' }} h B
        <span v-if="!sameList && sameImg" class="tag-id">同态把两个不同的列表“认同”成了同一个元素</span></div>
    </div>
  </div>
</template>

<style scoped>
.fme { max-width: 100%; overflow: hidden; }
.fme-row { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin: 8px 0; font-size: 13px; }
.fme-row.small { font-size: 12px; }
.lbl { color: var(--vp-c-text-2); }
.gen-map code { font-size: 11.5px; }
.fme-hint { font-size: 13px; color: var(--vp-c-text-2); line-height: 1.6; margin: 8px 0; }
.fme-lists { display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); gap: 10px; }
@media (max-width: 640px) { .fme-lists { grid-template-columns: 1fr; } }
.fme-list { border: 1px solid var(--vp-c-divider); border-radius: 10px; padding: 8px 10px; cursor: pointer; background: var(--vp-c-bg); min-width: 0; }
.fme-list.active { border: 2px solid var(--vp-c-brand-1); }
.fme-list-head { font-size: 12px; color: var(--vp-c-text-2); margin-bottom: 4px; }
.fme-chips { display: flex; flex-wrap: wrap; gap: 4px; align-items: center; min-height: 28px; }
.chip { font-family: var(--vp-font-family-mono); font-size: 13px; padding: 1px 8px; border-radius: 999px; background: var(--vp-c-brand-soft); color: var(--vp-c-brand-1); }
.bracket { font-family: var(--vp-font-family-mono); color: var(--vp-c-text-3); }
.fme-trace { margin-top: 6px; font-size: 12px; overflow-wrap: anywhere; }
.fme-trace code { white-space: normal; }
.fme-verdict { margin-top: 10px; font-size: 13px; line-height: 1.9; border-top: 1px dashed var(--vp-c-divider); padding-top: 8px; }
.muted { color: var(--vp-c-text-3); font-size: 12px; }
.tag-id { margin-left: 6px; font-size: 12px; padding: 1px 8px; border-radius: 999px; background: var(--vp-c-warning-soft, rgba(234, 179, 8, 0.16)); color: var(--vp-c-warning-1); }
</style>
