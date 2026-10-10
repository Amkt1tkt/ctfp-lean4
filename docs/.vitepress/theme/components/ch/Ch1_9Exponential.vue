<script setup>
import { ref, computed, watch } from 'vue'

const A_NAMES = ['x', 'y', 'z']
const B_NAMES = ['0', '1', '2']

const nA = ref(2)
const nB = ref(2)
const sel = ref(0) // 选中的函数编号
const arg = ref(0) // 选中的参数编号

const As = computed(() => A_NAMES.slice(0, nA.value))
const Bs = computed(() => B_NAMES.slice(0, nB.value))

// 所有函数：每个函数是一个长度为 |A| 的数组，第 i 项是 f(A[i]) 在 B 中的下标
const funcs = computed(() => {
  const out = []
  const total = nB.value ** nA.value
  for (let k = 0; k < total; k++) {
    const t = []
    let r = k
    for (let i = nA.value - 1; i >= 0; i--) {
      t[i] = r % nB.value
      r = Math.floor(r / nB.value)
    }
    out.push(t)
  }
  return nB.value === 0 && nA.value > 0 ? [] : out
})

watch([nA, nB], () => {
  sel.value = 0
  arg.value = 0
})

const count = computed(() => funcs.value.length)
const cur = computed(() => funcs.value[sel.value])

const note = computed(() => {
  if (nA.value === 0 && nB.value === 0) return '0⁰ = 1：从空类型到空类型，恰好有一个函数——空函数。'
  if (nA.value === 0) return `a⁰ = 1：从空类型出发的函数只有一个——那张空表（就是 absurd / Empty.elim）。`
  if (nB.value === 0) return `0^${nA.value} = 0：A 非空时，到空类型的函数一个也没有——你没法为 ${As.value[0]} 填上任何值。`
  if (nB.value === 1) return '1^a = 1：到单元素类型的函数只有一个——把一切都送到唯一的那个值（unit）。'
  if (nA.value === 1) return `a¹ = a：从单元素类型出发的函数，和 B 的元素一一对应（每个函数只是“挑出”一个元素）。`
  return `每个函数是一张有 ${nA.value} 行的表，每行有 ${nB.value} 种填法，所以一共 ${nB.value}^${nA.value} = ${count.value} 个。`
})

const tuple = computed(() => (cur.value ? '(' + cur.value.map((j) => Bs.value[j]).join(', ') + ')' : ''))
const evalRes = computed(() => (cur.value && nA.value > 0 ? Bs.value[cur.value[arg.value]] : null))
const prodStr = computed(() => (nA.value === 0 ? 'Unit' : Array(nA.value).fill('B').join(' × ')))
</script>

<template>
  <div class="ctfp-widget exp-widget">
    <div class="ctfp-widget-title">指数对象 = 函数表：B^A 里到底有什么？</div>
    <div class="ctl">
      <span class="lbl">|A| =</span>
      <button v-for="n in [0, 1, 2, 3]" :key="'a' + n" class="ctfp-btn" :class="{ on: nA === n }" @click="nA = n">{{ n }}</button>
      <span class="lbl sp">|B| =</span>
      <button v-for="n in [0, 1, 2, 3]" :key="'b' + n" class="ctfp-btn" :class="{ on: nB === n }" @click="nB = n">{{ n }}</button>
    </div>
    <div class="sets">
      <span>A = {<span class="mono">{{ As.join(', ') }}</span>}</span>
      <span>B = {<span class="mono">{{ Bs.join(', ') }}</span>}</span>
      <span class="big">|B^A| = {{ nB }}<sup>{{ nA }}</sup> = <b>{{ count }}</b></span>
    </div>
    <p class="note">{{ note }}</p>

    <div class="grid" v-if="count > 0">
      <button
        v-for="(t, k) in funcs"
        :key="k"
        class="tbl"
        :class="{ on: sel === k }"
        @click="sel = k"
        :title="`函数 f${k}`"
      >
        <div class="fname">f<sub>{{ k }}</sub></div>
        <div v-if="nA === 0" class="empty">（空表）</div>
        <div v-for="(j, i) in t" :key="i" class="cell" :class="{ hit: sel === k && arg === i }">
          <span>{{ As[i] }}</span><span class="arr">↦</span><span>{{ Bs[j] }}</span>
        </div>
      </button>
    </div>
    <div v-else class="none">（没有任何函数）</div>

    <div v-if="cur" class="evalbox">
      <div class="ev-title">eval : B^A × A → B</div>
      <template v-if="nA > 0">
        <div class="ctl">
          <span class="lbl">参数 a =</span>
          <button v-for="(a, i) in As" :key="a" class="ctfp-btn" :class="{ on: arg === i }" @click="arg = i">{{ a }}</button>
        </div>
        <div class="mono res">
          eval (f<sub>{{ sel }}</sub>, {{ As[arg] }}) = f<sub>{{ sel }}</sub> {{ As[arg] }} = <b>{{ evalRes }}</b>
        </div>
      </template>
      <div v-else class="mono res">A 是空的，没有参数可以喂给 eval。</div>
      <div class="mono tup">
        f<sub>{{ sel }}</sub> 作为元组：{{ nA === 0 ? '()' : tuple }} &nbsp;∈&nbsp; {{ prodStr }}
      </div>
    </div>
    <p class="hint">点一张表选中一个函数（B^A 的一个元素），再选一个参数，看 eval 怎样“查表”。每张表也可以读成一个 |A| 元组——这就是 B^A ≅ B × … × B。</p>
  </div>
</template>

<style scoped>
.exp-widget { max-width: 100%; }
.ctl { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin-bottom: 6px; }
.lbl { font-size: 13px; color: var(--vp-c-text-2); font-family: var(--vp-font-family-mono); }
.lbl.sp { margin-left: 14px; }
.sets { display: flex; flex-wrap: wrap; gap: 18px; font-size: 14px; margin: 6px 0; align-items: baseline; }
.big { font-size: 16px; }
.mono { font-family: var(--vp-font-family-mono); }
.note { font-size: 13px; color: var(--vp-c-text-2); margin: 4px 0 10px; min-height: 1.5em; }
.grid { display: flex; flex-wrap: wrap; gap: 8px; max-height: 300px; overflow-y: auto; padding: 2px; }
.tbl {
  border: 1px solid var(--vp-c-divider); border-radius: 8px; background: var(--vp-c-bg);
  padding: 4px 8px; min-width: 64px; cursor: pointer; font-family: var(--vp-font-family-mono); font-size: 12px;
  color: var(--vp-c-text-1); transition: all 0.2s; text-align: left;
}
.tbl:hover { border-color: var(--vp-c-brand-2); }
.tbl.on { border-color: var(--vp-c-brand-1); box-shadow: 0 0 0 2px var(--vp-c-brand-soft); }
.fname { font-size: 11px; color: var(--vp-c-text-3); margin-bottom: 2px; }
.cell { display: flex; gap: 4px; padding: 0 3px; border-radius: 4px; }
.cell.hit { background: var(--vp-c-brand-soft); color: var(--vp-c-brand-1); font-weight: 600; }
.arr { color: var(--vp-c-text-3); }
.empty { color: var(--vp-c-text-3); font-size: 11px; }
.none { color: var(--vp-c-text-3); font-size: 13px; padding: 10px 0; }
.evalbox { margin-top: 12px; padding: 10px 12px; border: 1px dashed var(--vp-c-divider); border-radius: 8px; }
.ev-title { font-size: 13px; font-weight: 600; margin-bottom: 6px; font-family: var(--vp-font-family-mono); }
.res { font-size: 14px; margin: 4px 0; }
.tup { font-size: 13px; color: var(--vp-c-text-2); }
.hint { font-size: 12px; color: var(--vp-c-text-3); margin: 8px 0 0; }
</style>
