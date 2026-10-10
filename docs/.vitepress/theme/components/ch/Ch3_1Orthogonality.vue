<script setup>
// 函子改内容、自然变换换容器：两种操作“正交”，先后次序无关（自然性方块交换）。
// 反例：排序不是自然变换，换一下次序结果就不同。
import { computed, ref } from 'vue'

const input = ref([3, 1, 4, 2])
const FS = [
  { id: 'inc', label: 'f = (· + 1)', fn: (x) => x + 1, lean: '(· + 1)' },
  { id: 'dbl', label: 'f = (· * 2)', fn: (x) => x * 2, lean: '(· * 2)' },
  { id: 'neg', label: 'f = (10 - ·)', fn: (x) => 10 - x, lean: '(10 - ·)' },
]
const ALPHAS = [
  { id: 'rev', label: 'α = reverse', kind: 'list', fn: (xs) => [...xs].reverse(), natural: true },
  { id: 'take', label: 'α = take 2', kind: 'list', fn: (xs) => xs.slice(0, 2), natural: true },
  { id: 'head', label: 'α = head?（List ⟹ Option）', kind: 'option', fn: (xs) => (xs.length ? [xs[0]] : []), natural: true },
  { id: 'sort', label: '反例：sort（不是自然变换）', kind: 'list', fn: (xs) => [...xs].sort((a, b) => a - b), natural: false },
]
const fId = ref('neg')
const aId = ref('rev')
const f = computed(() => FS.find((x) => x.id === fId.value))
const a = computed(() => ALPHAS.find((x) => x.id === aId.value))
const step = ref(2)

const top1 = computed(() => input.value.map(f.value.fn))
const top2 = computed(() => a.value.fn(top1.value))
const bot1 = computed(() => a.value.fn(input.value))
const bot2 = computed(() => bot1.value.map(f.value.fn))
const same = computed(() => JSON.stringify(top2.value) === JSON.stringify(bot2.value))

function reroll() {
  const k = 3 + Math.floor(Math.random() * 3)
  input.value = Array.from({ length: k }, () => Math.floor(Math.random() * 9))
}
const show = (lvl) => step.value >= lvl
const fmt = (xs, kind) => (kind === 'option' ? (xs.length ? `some ${xs[0]}` : 'none') : `[${xs.join(', ')}]`)
</script>

<template>
  <div class="ctfp-widget orth">
    <div class="ctfp-widget-title">函子改内容，自然变换换容器：先后次序无关</div>
    <div class="orth-row">
      <span class="lbl">函子作用（改每个元素）：</span>
      <button v-for="x in FS" :key="x.id" class="ctfp-btn" :class="{ on: fId === x.id }" @click="fId = x.id">{{ x.label }}</button>
    </div>
    <div class="orth-row">
      <span class="lbl">分量（换容器）：</span>
      <button v-for="x in ALPHAS" :key="x.id" class="ctfp-btn" :class="{ on: aId === x.id }" @click="aId = x.id">{{ x.label }}</button>
    </div>
    <div class="orth-row">
      <button class="ctfp-btn" @click="reroll">换一个输入列表</button>
      <button class="ctfp-btn" @click="step = 0">从头演示</button>
      <button class="ctfp-btn" :disabled="step >= 2" @click="step++">下一步</button>
    </div>

    <div class="orth-board">
      <div class="orth-path">
        <div class="tag">路径一：先 map f，再 α</div>
        <div class="flow">
          <div class="box list">{{ fmt(input, 'list') }}</div>
          <div class="arr">map f →</div>
          <div class="box list" :class="{ ghost: !show(1) }">{{ show(1) ? fmt(top1, 'list') : '?' }}</div>
          <div class="arr">α →</div>
          <div class="box" :class="[a.kind, { ghost: !show(2) }]">{{ show(2) ? fmt(top2, a.kind) : '?' }}</div>
        </div>
      </div>
      <div class="orth-path">
        <div class="tag">路径二：先 α，再 map f</div>
        <div class="flow">
          <div class="box list">{{ fmt(input, 'list') }}</div>
          <div class="arr">α →</div>
          <div class="box" :class="[a.kind, { ghost: !show(1) }]">{{ show(1) ? fmt(bot1, a.kind) : '?' }}</div>
          <div class="arr">map f →</div>
          <div class="box" :class="[a.kind, { ghost: !show(2) }]">{{ show(2) ? fmt(bot2, a.kind) : '?' }}</div>
        </div>
      </div>
      <div v-if="show(2)" class="verdict" :class="same ? 'ok' : 'bad'">
        <template v-if="same">两条路径结果相同：方块交换。{{ a.natural ? '' : '（这次碰巧相同，换个 f 或输入试试。）' }}</template>
        <template v-else>两条路径结果不同！sort 要“看”元素的值来决定位置，它干涉了内容，所以不是自然变换。</template>
      </div>
    </div>
    <p class="orth-hint">
      自然变换只搬动“格子”，从不查看格子里装的是什么；函子只改格子里的东西，从不挪动格子。两者互不干扰，
      所以谁先谁后都一样。把 f 选成 <code>(10 - ·)</code>（它会颠倒大小顺序），再选 sort，就能看到不自然的变换露馅。
    </p>
  </div>
</template>

<style scoped>
.orth { max-width: 100%; overflow: hidden; }
.orth-row { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin-bottom: 8px; font-size: 13px; }
.lbl { color: var(--vp-c-text-2); min-width: 9em; }
.ctfp-btn:disabled { opacity: 0.4; cursor: not-allowed; }
.orth-board { margin-top: 8px; display: flex; flex-direction: column; gap: 10px; }
.orth-path { border: 1px solid var(--vp-c-divider); border-radius: 10px; padding: 8px 10px; background: var(--vp-c-bg); }
.tag { font-size: 12px; color: var(--vp-c-text-2); margin-bottom: 6px; }
.flow { display: flex; flex-wrap: wrap; align-items: center; gap: 6px; }
.box {
  font-family: var(--vp-font-family-mono); font-size: 13px; padding: 4px 10px; border-radius: 8px;
  border: 2px solid var(--vp-c-brand-1); min-width: 3.5em; text-align: center; transition: all 0.25s;
}
.box.option { border-color: var(--vp-c-warning-1); border-style: dashed; }
.box.ghost { opacity: 0.35; }
.arr { font-size: 12px; color: var(--vp-c-text-2); white-space: nowrap; }
.verdict { font-size: 13px; padding: 6px 10px; border-radius: 8px; }
.verdict.ok { background: var(--vp-c-success-soft, rgba(16, 185, 129, 0.14)); color: var(--vp-c-success-1, #18794e); }
.verdict.bad { background: var(--vp-c-danger-soft, rgba(244, 63, 94, 0.14)); color: var(--vp-c-danger-1); }
.orth-hint { font-size: 13px; color: var(--vp-c-text-2); line-height: 1.6; margin: 10px 0 0; }
</style>
