<script setup>
import { ref, computed, onBeforeUnmount } from 'vue'

const LIMIT = 60
const initial = Array.from({ length: LIMIT - 1 }, (_, i) => i + 2)

// 每个“拍”是 era 的半步：phase 0 = 种子摆好，phase 1 = 头部已取出、倍数被标记
const seed = ref(initial.slice())
const out = ref([])
const phase = ref(0)
let timer = null

const head = computed(() => seed.value[0])
const marked = computed(() =>
  phase.value === 1 ? new Set(seed.value.slice(1).filter((n) => n % head.value === 0)) : new Set(),
)
const finished = computed(() => seed.value.length === 0)

function tick() {
  if (finished.value) return stop()
  if (phase.value === 0) {
    phase.value = 1
  } else {
    const p = head.value
    out.value = [...out.value, p]
    seed.value = seed.value.slice(1).filter((n) => n % p !== 0)
    phase.value = 0
  }
}
function stop() {
  if (timer) clearInterval(timer)
  timer = null
}
function play() {
  if (timer) return stop()
  if (finished.value) reset()
  timer = setInterval(tick, 800)
}
function reset() {
  stop()
  seed.value = initial.slice()
  out.value = []
  phase.value = 0
}
onBeforeUnmount(stop)
</script>

<template>
  <div class="ctfp-widget sieve">
    <div class="ctfp-widget-title">安娜态射动画：埃拉托色尼筛</div>
    <p class="hint">
      余代数 <code>era</code> 把种子（一个“剩余的数”的列表）拆成两部分：一个吐出的元素（列表的头 p）和一个新种子
      （尾部删去 p 的倍数）。<code>ana era</code> 只是一遍遍地重复这个动作。这里为了能画出来，只看 2 到 {{ LIMIT }}；
      真正的种子是无限的。
    </p>
    <div class="label">当前种子：</div>
    <div class="chips">
      <span
        v-for="(n, i) in seed"
        :key="n"
        class="chip"
        :class="{ head: i === 0 && phase === 1, gone: marked.has(n) }"
      >{{ n }}</span>
      <span v-if="finished" class="muted">（在这个窗口里已经筛完了）</span>
    </div>
    <div class="status">
      <template v-if="!finished && phase === 1">
        <code>era</code> 吐出 <b>{{ head }}</b>，并把 {{ marked.size }} 个 {{ head }} 的倍数从尾部删去，得到新种子。
      </template>
      <template v-else-if="!finished">下一步：<code>era</code> 看一眼种子的头部。</template>
    </div>
    <div class="label">已生成的流（<code>ana era</code> 的输出）：</div>
    <div class="chips out">
      <span v-for="p in out" :key="p" class="chip prime">{{ p }}</span>
      <span class="muted">…</span>
    </div>
    <div class="row">
      <button class="ctfp-btn" :disabled="finished" @click="tick">下一步</button>
      <button class="ctfp-btn" @click="play">自动播放 / 暂停</button>
      <button class="ctfp-btn" @click="reset">重置</button>
    </div>
  </div>
</template>

<style scoped>
.sieve { max-width: 100%; }
.hint { font-size: 0.9em; color: var(--vp-c-text-2); margin: 0.3em 0 0.6em; }
.label { font-size: 0.88em; color: var(--vp-c-text-2); margin-top: 8px; }
.chips { display: flex; flex-wrap: wrap; gap: 4px; margin: 4px 0; min-height: 30px; }
.chip {
  display: inline-block; min-width: 2.1em; text-align: center; padding: 2px 4px; border-radius: 5px;
  border: 1px solid var(--vp-c-divider); background: var(--vp-c-bg-soft); font-family: var(--vp-font-family-mono);
  font-size: 0.85em; transition: all 0.3s;
}
.chip.head { background: var(--vp-c-warning-soft); border-color: var(--vp-c-warning-1); font-weight: 700; }
.chip.gone { opacity: 0.35; text-decoration: line-through; border-style: dashed; }
.chip.prime { background: var(--vp-c-brand-soft); border-color: var(--vp-c-brand-1); }
.status { min-height: 1.8em; font-size: 0.92em; margin: 6px 0; }
.muted { color: var(--vp-c-text-3); font-size: 0.88em; align-self: center; }
.row { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 8px; }
</style>
