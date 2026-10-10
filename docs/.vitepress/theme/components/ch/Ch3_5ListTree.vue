<script setup>
import { ref, computed, watch } from 'vue'

const n = ref(13)
const openZ = ref(new Set([5]))
const openX = ref(new Set(['5-3']))
const onlyHits = ref(false)

const isHit = (x, y, z) => x * x + y * y === z * z
const range = (a, b) => Array.from({ length: Math.max(0, b - a + 1) }, (_, i) => a + i)

const zs = computed(() => range(1, n.value))
const xsOf = (z) => range(1, z)
const ysOf = (x, z) => range(x, z)
const zHasHit = (z) => xsOf(z).some((x) => ysOf(x, z).some((y) => isHit(x, y, z)))
const xHasHit = (x, z) => ysOf(x, z).some((y) => isHit(x, y, z))

const results = computed(() => {
  const out = []
  for (const z of zs.value) for (const x of xsOf(z)) for (const y of ysOf(x, z)) if (isHit(x, y, z)) out.push([x, y, z])
  return out
})
const leaves = computed(() => zs.value.reduce((acc, z) => acc + xsOf(z).reduce((a, x) => a + (z - x + 1), 0), 0))

watch(n, () => {
  openZ.value = new Set([...openZ.value].filter((z) => z <= n.value))
  openX.value = new Set([...openX.value].filter((k) => Number(k.split('-')[0]) <= n.value))
})

function toggleZ(z) {
  const s = new Set(openZ.value)
  s.has(z) ? s.delete(z) : s.add(z)
  openZ.value = s
}
function toggleX(z, x) {
  const k = `${z}-${x}`
  const s = new Set(openX.value)
  s.has(k) ? s.delete(k) : s.add(k)
  openX.value = s
}
function expandHits() {
  const sz = new Set(), sx = new Set()
  for (const [x, , z] of results.value) { sz.add(z); sx.add(`${z}-${x}`) }
  openZ.value = sz
  openX.value = sx
  onlyHits.value = true
}
function collapse() {
  openZ.value = new Set()
  openX.value = new Set()
}
const visibleZ = computed(() => (onlyHits.value ? zs.value.filter(zHasHit) : zs.value))
const visibleX = (z) => (onlyHits.value ? xsOf(z).filter((x) => xHasHit(x, z)) : xsOf(z))
</script>

<template>
  <div class="ctfp-widget lt">
    <div class="ctfp-widget-title">列表单子的非确定性展开树：triples n</div>
    <p class="hint">每个 <code>←</code> 都是一次“分叉”：程序同时走进列表里的每一个元素。点击 z、x 节点展开下一层；最底层的 <code>guard</code> 要么给出 <code>[()]</code>（分支存活），要么给出 <code>[]</code>（分支被剪掉）。</p>
    <div class="row">
      <label>n = <input type="range" min="5" max="25" v-model.number="n" /> <b class="mono">{{ n }}</b></label>
      <label><input type="checkbox" v-model="onlyHits" /> 只显示有结果的分支</label>
      <button class="ctfp-btn" @click="expandHits">展开所有成功路径</button>
      <button class="ctfp-btn" @click="collapse">全部收起</button>
    </div>

    <div class="tree mono">
      <div class="lvl-label">let z ← List.range' 1 {{ n }}</div>
      <div class="zrow">
        <button v-for="z in visibleZ" :key="z" class="node z" :class="{ open: openZ.has(z), hit: zHasHit(z) }" @click="toggleZ(z)">z={{ z }}</button>
      </div>
      <template v-for="z in visibleZ" :key="'z' + z">
        <div v-if="openZ.has(z)" class="branch">
          <div class="lvl-label">z = {{ z }}：let x ← List.range' 1 {{ z }}</div>
          <div class="xrow">
            <button v-for="x in visibleX(z)" :key="x" class="node x" :class="{ open: openX.has(z + '-' + x), hit: xHasHit(x, z) }" @click="toggleX(z, x)">x={{ x }}</button>
          </div>
          <template v-for="x in visibleX(z)" :key="'x' + x">
            <div v-if="openX.has(z + '-' + x)" class="branch inner">
              <div class="lvl-label">x = {{ x }}：let y ← [{{ x }}..{{ z }}]，然后 guard ({{ x }}² + y² = {{ z }}²)</div>
              <div class="yrow">
                <span v-for="y in ysOf(x, z)" :key="y" class="leaf" :class="isHit(x, y, z) ? 'ok' : 'no'" :title="`${x * x} + ${y * y} ${isHit(x, y, z) ? '=' : '≠'} ${z * z}`">
                  y={{ y }} <small>{{ isHit(x, y, z) ? '[()] → [(' + x + ', ' + y + ', ' + z + ')]' : '[]' }}</small>
                </span>
              </div>
            </div>
          </template>
        </div>
      </template>
    </div>

    <div class="sum">
      <div>一共尝试了 <b>{{ leaves }}</b> 个 (x, y, z) 组合，其中 <b>{{ results.length }}</b> 个通过了 guard。</div>
      <div class="mono res">triples {{ n }} = [<span v-for="(t, i) in results" :key="i"><span class="okc">({{ t.join(', ') }})</span><span v-if="i < results.length - 1">, </span></span>]</div>
      <div class="dim">最终结果就是把所有叶子上的小列表（大多是 <code>[]</code>，少数是单元素列表）按从左到右的顺序拼接起来——这正是 bind（flatMap）一层层做的事。</div>
    </div>
  </div>
</template>

<style scoped>
.lt, .lt * { font-variant-ligatures: none; font-feature-settings: "liga" 0, "calt" 0; }
.hint { font-size: 13px; color: var(--vp-c-text-2); margin: 0 0 8px; line-height: 1.6; }
.row { display: flex; flex-wrap: wrap; gap: 8px 14px; align-items: center; margin: 8px 0; font-size: 13px; }
.mono { font-family: var(--vp-font-family-mono); }
.dim { color: var(--vp-c-text-3); }
.tree { background: var(--vp-c-bg); border: 1px solid var(--vp-c-divider); border-radius: 10px; padding: 10px 12px; font-size: 12px; max-height: 460px; overflow: auto; }
.lvl-label { color: var(--vp-c-text-3); margin: 6px 0 4px; font-size: 11px; }
.zrow, .xrow, .yrow { display: flex; flex-wrap: wrap; gap: 4px; }
.branch { margin: 6px 0 6px 10px; padding-left: 10px; border-left: 2px solid var(--vp-c-divider); }
.branch.inner { border-left-color: color-mix(in srgb, var(--vp-c-brand-1) 40%, transparent); }
.node { font-family: var(--vp-font-family-mono); font-size: 12px; padding: 1px 8px; border-radius: 6px; border: 1px solid var(--vp-c-divider); background: var(--vp-c-bg-soft); color: var(--vp-c-text-2); cursor: pointer; }
.node.hit { color: var(--vp-c-text-1); border-color: color-mix(in srgb, #16a34a 60%, transparent); }
.node.open { background: var(--vp-c-brand-1); color: white; border-color: var(--vp-c-brand-1); }
.leaf { padding: 1px 6px; border-radius: 6px; border: 1px solid var(--vp-c-divider); }
.leaf small { font-size: 10px; }
.leaf.no { color: var(--vp-c-text-3); text-decoration: line-through; text-decoration-color: color-mix(in srgb, var(--vp-c-danger-1) 50%, transparent); }
.leaf.no small { text-decoration: none; }
.leaf.ok { color: #15803d; border-color: #16a34a; background: color-mix(in srgb, #16a34a 12%, transparent); font-weight: 600; }
.dark .leaf.ok { color: #4ade80; }
.sum { margin-top: 10px; font-size: 13px; line-height: 1.7; }
.res { word-break: break-all; }
.okc { color: #15803d; }
.dark .okc { color: #4ade80; }
</style>
