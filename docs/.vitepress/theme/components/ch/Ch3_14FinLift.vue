<script setup>
// 𝐅 中的一个态射 f : m → n 同时有两种提升：
//   对元组：aⁿ → aᵐ（按 f 挑选分量，逆变）
//   对运算：𝐋(m,1) → 𝐋(n,1)（按 f 给变量改名，协变）
// 并验证两种走法求值相同（余端的认同关系）。
import { computed, ref, watch } from 'vue'

const m = ref(3)
const n = ref(4)
const f = ref([0, 2, 2])
const sel = ref(null)
const tuple = ref(['p', 'q', 'r', 's', 't'])

watch([m, n], () => {
  f.value = Array.from({ length: m.value }, (_, i) => Math.min(f.value[i] ?? i, n.value - 1))
  sel.value = null
})

const W = 300, H = 210
const spread = (k, count) => (count === 1 ? 105 : 40 + (k * 130) / (count - 1))
const srcY = (i) => spread(i, m.value)
const tgtY = (j) => spread(j, n.value)
const SX = 70, TX = 230

function clickSrc(i) { sel.value = sel.value === i ? null : i }
function clickTgt(j) {
  if (sel.value === null) return
  f.value[sel.value] = j
  sel.value = sel.value + 1 < m.value ? sel.value + 1 : null
}

const presetPick = () => { m.value = 1; f.value = [Math.min(2, n.value - 1)] }
const presetDup = () => { n.value = 1; f.value = Array(m.value).fill(0) }
const presetRandom = () => { f.value = f.value.map(() => Math.floor(Math.random() * n.value)) }
const presetId = () => { n.value = m.value; f.value = Array.from({ length: m.value }, (_, i) => i) }

const injective = computed(() => new Set(f.value).size === f.value.length)
const surjective = computed(() => new Set(f.value).size === n.value)
const total = computed(() => n.value ** m.value)
const index = computed(() => f.value.reduce((acc, j) => acc * n.value + j, 0) + 1)

const lifted = computed(() => f.value.map((j) => tuple.value[j]))
const sub = (k) => String(k).split('').map((d) => '₀₁₂₃₄₅₆₇₈₉'[d]).join('')
const termM = computed(() => Array.from({ length: m.value }, (_, i) => 'x' + sub(i)).join(' · '))
const termN = computed(() => f.value.map((j) => 'x' + sub(j)).join(' · '))
const tupleN = computed(() => tuple.value.slice(0, n.value))
const evalRenamed = computed(() => f.value.map((j) => tupleN.value[j]).join(''))
const evalLifted = computed(() => lifted.value.join(''))
</script>

<template>
  <div class="ctfp-widget fl">
    <div class="ctfp-widget-title">一个 f : m → n，两种提升</div>
    <p class="fl-hint">
      先点左边的一个点（m 中的元素），再点右边的一个点（n 中的元素），就设定了 f 在它上面的取值。
      观察下面两栏：对元组是“挑选分量”，方向是 aⁿ → aᵐ；对运算是“给变量改名”，方向是 𝐋(m,1) → 𝐋(n,1)。
    </p>
    <div class="fl-row">
      <label>m = <select v-model.number="m"><option v-for="k in [1, 2, 3, 4]" :key="k" :value="k">{{ k }}</option></select></label>
      <label>n = <select v-model.number="n"><option v-for="k in [1, 2, 3, 4, 5]" :key="k" :value="k">{{ k }}</option></select></label>
      <button class="ctfp-btn" @click="presetPick">选第 k 个（1 → n）</button>
      <button class="ctfp-btn" @click="presetDup">复制（m → 1）</button>
      <button class="ctfp-btn" @click="presetId">恒等</button>
      <button class="ctfp-btn" @click="presetRandom">随机</button>
    </div>

    <div class="fl-main">
      <svg :viewBox="`0 0 ${W} ${H}`" :width="W" class="fl-svg">
        <defs>
          <marker id="fl-ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" orient="auto-start-reverse">
            <path d="M0,0 L10,5 L0,10 L3,5 z" fill="var(--vp-c-brand-1)" />
          </marker>
        </defs>
        <text :x="SX" y="16" text-anchor="middle" class="fl-head">m = {{ m }}</text>
        <text :x="TX" y="16" text-anchor="middle" class="fl-head">n = {{ n }}</text>
        <rect :x="SX - 20" y="24" width="40" :height="H - 40" rx="18" class="fl-set" />
        <rect :x="TX - 20" y="24" width="40" :height="H - 40" rx="18" class="fl-set" />
        <line v-for="(j, i) in f" :key="'a' + i" :x1="SX + 10" :y1="srcY(i)" :x2="TX - 12" :y2="tgtY(j)"
              class="fl-arrow" :class="{ hot: sel === i }" marker-end="url(#fl-ah)" />
        <g v-for="i in m" :key="'s' + i" class="fl-pt" @click="clickSrc(i - 1)">
          <circle :cx="SX" :cy="srcY(i - 1)" r="9" :class="{ on: sel === i - 1 }" />
          <text :x="SX - 22" :y="srcY(i - 1) + 4" text-anchor="end" class="fl-idx">{{ i - 1 }}</text>
        </g>
        <g v-for="j in n" :key="'t' + j" class="fl-pt" :class="{ armed: sel !== null }" @click="clickTgt(j - 1)">
          <circle :cx="TX" :cy="tgtY(j - 1)" r="9" />
          <text :x="TX + 22" :y="tgtY(j - 1) + 4" class="fl-idx">{{ j - 1 }} : {{ tuple[j - 1] }}</text>
        </g>
      </svg>
      <div class="fl-facts">
        <div>取值表：<code>[{{ f.join(', ') }}]</code></div>
        <div>从 {{ m }} 到 {{ n }} 一共有 n<sup>m</sup> = <b>{{ total }}</b> 个态射，这是第 {{ index }} 个。</div>
        <div>单射：<b>{{ injective ? '是' : '否' }}</b>；满射：<b>{{ surjective ? '是' : '否' }}</b></div>
        <div class="fl-tuple">
          aⁿ 中的元组（可改）：
          <input v-for="j in n" :key="'in' + j" v-model="tuple[j - 1]" maxlength="3" class="fl-in" />
        </div>
      </div>
    </div>

    <div class="fl-cols">
      <div class="fl-col">
        <div class="fl-col-head">逆变：aⁿ → aᵐ（liftPow f）</div>
        <div class="fl-tup">({{ tupleN.join(', ') }})</div>
        <div class="fl-arrowtxt">↓ 第 i 个输出取第 f(i) 个分量</div>
        <div class="fl-tup out">({{ lifted.join(', ') }})</div>
      </div>
      <div class="fl-col">
        <div class="fl-col-head">协变：𝐋(m,1) → 𝐋(n,1)（rename f）</div>
        <div class="fl-tup">{{ termM }}</div>
        <div class="fl-arrowtxt">↓ 把变量 xᵢ 改名为 x<sub>f(i)</sub></div>
        <div class="fl-tup out">{{ termN }}</div>
      </div>
    </div>
    <div class="fl-check">
      在字符串拼接模型中求值：改名后的项作用在 n 元组上 = <code>"{{ evalRenamed }}"</code>；
      原来的项作用在挑选后的 m 元组上 = <code>"{{ evalLifted }}"</code>。
      <b>{{ evalRenamed === evalLifted ? '两者相同' : '不同？' }}</b>——这就是余端里 ⟨f, id⟩ 与 ⟨id, f⟩ 两条路被认同的原因（定理 <code>eval_rename</code>）。
    </div>
  </div>
</template>

<style scoped>
.fl-hint { font-size: 13px; color: var(--vp-c-text-2); margin: 0 0 10px; line-height: 1.7; }
.fl-row { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; font-size: 13px; }
.fl-row select { border: 1px solid var(--vp-c-divider); border-radius: 6px; background: var(--vp-c-bg); color: var(--vp-c-text-1); padding: 1px 4px; }
.fl-main { display: flex; flex-wrap: wrap; gap: 16px; align-items: center; margin: 10px 0; }
.fl-svg { max-width: 100%; height: auto; flex: 0 1 300px; }
.fl-head { font-size: 13px; fill: var(--vp-c-text-2); }
.fl-set { fill: none; stroke: var(--vp-c-text-3); stroke-width: 1.3; }
.fl-arrow { stroke: var(--vp-c-brand-1); stroke-width: 1.6; }
.fl-arrow.hot { stroke-width: 3; }
.fl-pt { cursor: pointer; }
.fl-pt circle { fill: var(--vp-c-bg); stroke: var(--vp-c-text-1); stroke-width: 1.5; transition: all 0.2s; }
.fl-pt circle.on { fill: var(--vp-c-brand-1); stroke: var(--vp-c-brand-1); }
.fl-pt.armed circle { stroke: var(--vp-c-brand-1); stroke-dasharray: 3 2; }
.fl-pt:hover circle { stroke-width: 2.6; }
.fl-idx { font-size: 12px; fill: var(--vp-c-text-2); font-family: var(--vp-font-family-mono); }
.fl-facts { flex: 1 1 220px; font-size: 13px; line-height: 2; }
.fl-tuple { display: flex; flex-wrap: wrap; gap: 4px; align-items: center; }
.fl-in { width: 40px; font-family: var(--vp-font-family-mono); font-size: 13px; padding: 1px 4px; border: 1px solid var(--vp-c-divider); border-radius: 6px; background: var(--vp-c-bg); color: var(--vp-c-text-1); }
.fl-cols { display: flex; flex-wrap: wrap; gap: 12px; }
.fl-col { flex: 1 1 230px; min-width: 0; border: 1px solid var(--vp-c-divider); border-radius: 10px; padding: 8px 12px; background: var(--vp-c-bg); text-align: center; }
.fl-col-head { font-size: 13px; color: var(--vp-c-text-2); margin-bottom: 6px; }
.fl-tup { font-family: var(--vp-font-family-mono); font-size: 15px; overflow-wrap: anywhere; }
.fl-tup.out { color: var(--vp-c-brand-1); font-weight: 600; }
.fl-arrowtxt { font-size: 12px; color: var(--vp-c-text-3); margin: 4px 0; }
.fl-check { margin-top: 10px; font-size: 13px; line-height: 1.75; padding: 8px 12px; border-radius: 8px; border: 1px solid var(--vp-c-divider); background: var(--vp-c-bg); }
</style>
