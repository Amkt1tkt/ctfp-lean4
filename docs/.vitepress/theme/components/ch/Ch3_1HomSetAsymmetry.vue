<script setup>
// hom-集的不对称性：比较 |C(a, b)| 与 |C(b, a)|。
// 偏序（瘦范畴）中至多一个方向非空；有限集合范畴中 |Set(A, B)| = |B|^|A|，通常两个方向大小不同。
import { computed, ref } from 'vue'

const mode = ref('poset')
const objs = [0, 1, 2, 3]
const label = (k) => (mode.value === 'poset' ? String(k) : `${k} 元集`)
const count = (a, b) => (mode.value === 'poset' ? (a <= b ? 1 : 0) : b ** a)
const sel = ref({ a: 1, b: 3 })
const maxCount = computed(() => Math.max(...objs.flatMap((a) => objs.map((b) => count(a, b)))))
const shade = (v) => {
  if (v === 0) return 'transparent'
  const t = 0.18 + 0.62 * (Math.log(v + 1) / Math.log(maxCount.value + 1))
  return `color-mix(in srgb, var(--vp-c-brand-1) ${Math.round(t * 100)}%, transparent)`
}
const isSel = (a, b) => sel.value.a === a && sel.value.b === b
const isMirror = (a, b) => sel.value.a === b && sel.value.b === a && a !== b
const ab = computed(() => count(sel.value.a, sel.value.b))
const ba = computed(() => count(sel.value.b, sel.value.a))
</script>

<template>
  <div class="ctfp-widget hsa">
    <div class="ctfp-widget-title">hom-集的不对称性：C(a, b) 与 C(b, a) 往往大不一样</div>
    <div class="hsa-controls">
      <button class="ctfp-btn" :class="{ on: mode === 'poset' }" @click="mode = 'poset'">偏序 (ℕ 的一段, ≤)：瘦范畴</button>
      <button class="ctfp-btn" :class="{ on: mode === 'set' }" @click="mode = 'set'">有限集合范畴 Set：“厚”预序</button>
    </div>
    <p class="hsa-hint">点击格子 (a, b) 查看 hom-集 C(a, b) 的大小；它的“镜像” C(b, a) 会用虚线框标出。颜色越深，态射越多。</p>
    <div class="hsa-body">
      <table class="hsa-table">
        <tr>
          <th class="corner">a ＼ b</th>
          <th v-for="b in objs" :key="'h' + b">{{ label(b) }}</th>
        </tr>
        <tr v-for="a in objs" :key="'r' + a">
          <th>{{ label(a) }}</th>
          <td
            v-for="b in objs" :key="a + '-' + b"
            :class="{ sel: isSel(a, b), mirror: isMirror(a, b) }"
            :style="{ background: shade(count(a, b)) }"
            @click="sel = { a, b }"
          >{{ count(a, b) }}</td>
        </tr>
      </table>
      <div class="hsa-info">
        <div class="big">|C({{ label(sel.a) }}, {{ label(sel.b) }})| = {{ ab }}</div>
        <div class="big mirror-txt">|C({{ label(sel.b) }}, {{ label(sel.a) }})| = {{ ba }}</div>
        <p v-if="mode === 'poset'">
          在偏序里，从 a 到 b 的箭头存在当且仅当 a ≤ b，而且至多一支。所以除了对角线（a = b），
          一对对象之间<b>最多只有一个方向</b>有箭头：箭头有着确定的“流向”。
        </p>
        <p v-else>
          在 Set 中，从 A 到 B 的函数共有 |B|<sup>|A|</sup> 个。例如 2<sup>3</sup> = 8 而 3<sup>2</sup> = 9；
          从空集出发总有恰好 1 个函数，而到空集去（除非起点也空）一个都没有。两个方向都可能非空，但大小一般不同——
          可以把一般范畴想成“厚的”预序：箭头仍有大致的流向，只是每个方向上可以挤着很多支。
        </p>
      </div>
    </div>
  </div>
</template>

<style scoped>
.hsa { max-width: 100%; overflow: hidden; }
.hsa-controls { display: flex; flex-wrap: wrap; gap: 8px; }
.hsa-hint { font-size: 13px; color: var(--vp-c-text-2); margin: 10px 0; }
.hsa-body { display: flex; flex-wrap: wrap; gap: 18px; align-items: flex-start; }
.hsa-table { border-collapse: collapse; margin: 0; display: table; }
.hsa-table th, .hsa-table td { padding: 6px 10px; font-size: 13px; text-align: center; border: 1px solid var(--vp-c-divider); }
.hsa-table th { background: var(--vp-c-bg); font-weight: 600; white-space: nowrap; }
.hsa-table th.corner { color: var(--vp-c-text-3); font-weight: 500; }
.hsa-table td { cursor: pointer; font-family: var(--vp-font-family-mono); min-width: 3em; transition: outline 0.1s; }
.hsa-table td.sel { outline: 3px solid var(--vp-c-brand-1); outline-offset: -3px; font-weight: 700; }
.hsa-table td.mirror { outline: 2px dashed var(--vp-c-warning-1); outline-offset: -3px; font-weight: 700; }
.hsa-info { flex: 1; min-width: 220px; font-size: 13px; line-height: 1.7; }
.hsa-info p { margin: 8px 0 0; }
.big { font-size: 15px; font-weight: 600; font-family: var(--vp-font-family-mono); }
.mirror-txt { color: var(--vp-c-warning-1); }
</style>
