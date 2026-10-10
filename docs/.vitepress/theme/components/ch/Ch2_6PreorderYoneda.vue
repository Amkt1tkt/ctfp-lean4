<script setup>
import { ref, computed } from 'vue'

const nodes = [
  { v: 1, x: 150, y: 250 },
  { v: 2, x: 90, y: 180 },
  { v: 3, x: 220, y: 180 },
  { v: 4, x: 40, y: 110 },
  { v: 6, x: 160, y: 110 },
  { v: 12, x: 100, y: 40 },
]
const edges = [[1, 2], [1, 3], [2, 4], [2, 6], [3, 6], [4, 12], [6, 12]]
const pos = Object.fromEntries(nodes.map((n) => [n.v, n]))
const le = (p, q) => q % p === 0 // p ≤ q  ⇔  p ∣ q

const mode = ref('contra') // 'contra': C(-, a)   'co': C(a, -)
const a = ref(2)
const b = ref(6)
const picking = ref('a')

function pick(v) {
  if (picking.value === 'a') { a.value = v; picking.value = 'b' }
  else { b.value = v; picking.value = 'a' }
}

// 逆变：C(x, a) 非空 ⇔ x ≤ a；协变：C(a, x) 非空 ⇔ a ≤ x
const inA = (x) => (mode.value === 'contra' ? le(x, a.value) : le(a.value, x))
const inB = (x) => (mode.value === 'contra' ? le(x, b.value) : le(b.value, x))

const rows = computed(() =>
  nodes.map(({ v }) => {
    const p = inA(v), q = inB(v)
    let kind, bad = false
    if (!p && !q) kind = '∅ → ∅：空函数'
    else if (!p && q) kind = '∅ → {∗}：absurd'
    else if (p && q) kind = '{∗} → {∗}：唯一的函数'
    else { kind = '{∗} → ∅：不存在！'; bad = true }
    return { v, p, q, kind, bad }
  }),
)
const blocked = computed(() => rows.value.filter((r) => r.bad))
const holds = computed(() => blocked.value.length === 0)
const relHolds = computed(() => (mode.value === 'contra' ? le(a.value, b.value) : le(b.value, a.value)))

const homA = computed(() => (mode.value === 'contra' ? `C(x, ${a.value})` : `C(${a.value}, x)`))
const homB = computed(() => (mode.value === 'contra' ? `C(x, ${b.value})` : `C(${b.value}, x)`))
const setName = computed(() => (mode.value === 'contra' ? '↓' : '↑'))
</script>

<template>
  <div class="ctfp-widget py">
    <div class="ctfp-widget-title">预序上的米田嵌入：12 的因数，按“整除”排序（a ≤ b 即 a ∣ b）</div>
    <p class="hint">点击图中的数字依次选定 <b>a</b> 和 <b>b</b>（当前在选：<b>{{ picking }}</b>）。下方表格列出自然变换 <code>{{ mode === 'contra' ? 'C(-, a) ⟹ C(-, b)' : 'C(a, -) ⟹ C(b, -)' }}</code> 在每个对象 x 上的分量能不能存在。</p>
    <div class="row">
      <button class="ctfp-btn" :class="{ on: mode === 'contra' }" @click="mode = 'contra'">余米田：C(-, a)，看“下方集合” ↓a</button>
      <button class="ctfp-btn" :class="{ on: mode === 'co' }" @click="mode = 'co'">米田：C(a, -)，看“上方集合” ↑a</button>
    </div>
    <div class="body">
      <svg viewBox="0 0 270 290" class="hasse" role="img">
        <line v-for="(e, i) in edges" :key="i" :x1="pos[e[0]].x" :y1="pos[e[0]].y" :x2="pos[e[1]].x" :y2="pos[e[1]].y" class="edge" />
        <g v-for="n in nodes" :key="n.v" class="node" @click="pick(n.v)">
          <circle :cx="n.x" :cy="n.y" r="22" :class="{ inB: inB(n.v) }" />
          <circle v-if="inA(n.v)" :cx="n.x" :cy="n.y" r="27" class="ringA" />
          <text :x="n.x" :y="n.y + 5" text-anchor="middle" class="num">{{ n.v }}</text>
          <text v-if="n.v === a" :x="n.x + 26" :y="n.y - 18" class="tag tagA">a</text>
          <text v-if="n.v === b" :x="n.x - 34" :y="n.y - 18" class="tag tagB">b</text>
        </g>
      </svg>
      <div class="side">
        <div class="legend">
          <span><i class="lgA"></i>{{ setName }}{{ a }} = {x | {{ homA }} 非空}</span>
          <span><i class="lgB"></i>{{ setName }}{{ b }} = {x | {{ homB }} 非空}</span>
        </div>
        <table>
          <thead><tr><th>x</th><th>{{ homA }}</th><th>{{ homB }}</th><th>分量</th></tr></thead>
          <tbody>
            <tr v-for="r in rows" :key="r.v" :class="{ bad: r.bad }">
              <td>{{ r.v }}</td>
              <td>{{ r.p ? '{∗}' : '∅' }}</td>
              <td>{{ r.q ? '{∗}' : '∅' }}</td>
              <td>{{ r.kind }}</td>
            </tr>
          </tbody>
        </table>
      </div>
    </div>
    <div class="verdict" :class="holds ? 'ok' : 'no'">
      <template v-if="holds">
        每个分量都存在（而且唯一）⇒ 自然变换存在。此时 {{ setName }}{{ a }} ⊆ {{ setName }}{{ b }}，
        而米田嵌入告诉我们这等价于 <b>{{ mode === 'contra' ? `${a} ∣ ${b}` : `${b} ∣ ${a}` }}</b> {{ relHolds ? '✓' : '' }}。
      </template>
      <template v-else>
        在 x = {{ blocked.map((r) => r.v).join(', ') }} 处卡住了：没有从单元素集到空集的函数 ⇒ 自然变换不存在。
        对应地，{{ setName }}{{ a }} ⊄ {{ setName }}{{ b }}，且 <b>{{ mode === 'contra' ? `${a} ∤ ${b}` : `${b} ∤ ${a}` }}</b>。
      </template>
    </div>
  </div>
</template>

<style scoped>
.py { max-width: 100%; }
.row { display: flex; gap: 6px; flex-wrap: wrap; margin: 6px 0; }
.hint { font-size: 13px; color: var(--vp-c-text-2); margin: 6px 0; }
.body { display: grid; grid-template-columns: minmax(0, 270px) minmax(0, 1fr); gap: 14px; align-items: start; }
@media (max-width: 640px) { .body { grid-template-columns: minmax(0, 1fr); } }
.hasse { width: 100%; max-width: 270px; }
.edge { stroke: var(--vp-c-text-3); stroke-width: 1.5; }
.node { cursor: pointer; }
.node circle { fill: var(--vp-c-bg); stroke: var(--vp-c-text-2); stroke-width: 1.5; transition: all 0.2s; }
.node circle.inB { fill: var(--vp-c-green-soft, rgba(16, 185, 129, 0.25)); stroke: var(--vp-c-green-1, #10b981); }
.node circle.ringA { fill: none; stroke: var(--vp-c-brand-1); stroke-width: 3; stroke-dasharray: 5 3; }
.num { font-size: 15px; font-weight: 600; fill: var(--vp-c-text-1); pointer-events: none; }
.tag { font-size: 14px; font-weight: 700; font-style: italic; }
.tagA { fill: var(--vp-c-brand-1); }
.tagB { fill: var(--vp-c-green-1, #10b981); }
.legend { display: flex; flex-direction: column; gap: 4px; font-size: 13px; margin-bottom: 6px; }
.legend i { display: inline-block; width: 14px; height: 14px; border-radius: 50%; margin-right: 6px; vertical-align: -2px; }
.lgA { border: 3px dashed var(--vp-c-brand-1); box-sizing: border-box; }
.lgB { background: var(--vp-c-green-soft, rgba(16, 185, 129, 0.25)); border: 1.5px solid var(--vp-c-green-1, #10b981); }
table { border-collapse: collapse; font-size: 13px; width: 100%; display: table; margin: 0; }
th, td { border: 1px solid var(--vp-c-divider); padding: 3px 8px; text-align: left; }
th, td:nth-child(-n+3) { white-space: nowrap; }
tr.bad { background: var(--vp-c-danger-soft, rgba(244, 63, 94, 0.14)); font-weight: 600; }
.verdict { margin-top: 10px; padding: 8px 12px; border-radius: 8px; font-size: 14px; }
.verdict.ok { background: var(--vp-c-green-soft, rgba(16, 185, 129, 0.14)); }
.verdict.no { background: var(--vp-c-danger-soft, rgba(244, 63, 94, 0.14)); }
</style>
