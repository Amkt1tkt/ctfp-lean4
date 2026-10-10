<script setup>
// 流余单子：duplicate 产生“所有焦点”，extend f = map f ∘ duplicate。
import { ref, computed, onBeforeUnmount } from 'vue'

const N = 10 // 显示的列数（流本身是无限的）

const inputs = {
  nats: { name: '自然数 0,1,2,…', f: (k) => k },
  square: { name: '方波', f: (k) => (Math.floor(k / 3) % 2 ? 6 : 0) },
  noise: { name: '噪声', f: (k) => [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4][k % 20] },
  step: { name: '阶跃', f: (k) => (k < 4 ? 0 : 8) },
}
const inputKey = ref('noise')
const s = (k) => inputs[inputKey.value].f(k)

const fmt = (x) => (Number.isInteger(x) ? String(x) : x.toFixed(2).replace(/0+$/, '').replace(/\.$/, ''))

const arrows = {
  extract: { name: 'extract', lean: 'extract', win: 1, f: (row) => row(0), desc: '只看焦点：extend extract = id' },
  sum3: { name: 'sumS 3', lean: 'sumS 3', win: 3, f: (row) => row(0) + row(1) + row(2), desc: '焦点及其后两个元素之和' },
  avg3: { name: 'average 3', lean: 'average 3', win: 3, f: (row) => (row(0) + row(1) + row(2)) / 3, desc: '滑动平均（原书的例子）' },
  diff: { name: '差分', lean: 'fun w => w.get 1 - w.get 0', win: 2, f: (row) => row(1) - row(0), desc: '下一个减当前：离散“导数”' },
  max3: { name: 'max 3', lean: 'fun w => max3 (w.get 0) (w.get 1) (w.get 2)', win: 3, f: (row) => Math.max(row(0), row(1), row(2)), desc: '局部最大值滤波' },
}
const arrowKey = ref('avg3')
const arrow = computed(() => arrows[arrowKey.value])

const showDup = ref(true)
const focus = ref(null) // 被选中的结果下标
const revealed = ref(N) // extend 播放时已经算出的结果个数
let timer = 0

const rowAt = (k) => (j) => s(k + j)
const results = computed(() => Array.from({ length: N }, (_, k) => arrow.value.f(rowAt(k))))

function play() {
  clearInterval(timer)
  revealed.value = 0
  focus.value = 0
  timer = setInterval(() => {
    revealed.value++
    if (revealed.value >= N) {
      clearInterval(timer)
      focus.value = null
    } else focus.value = revealed.value
  }, 550)
}
onBeforeUnmount(() => clearInterval(timer))

function pick(k) {
  clearInterval(timer)
  revealed.value = N
  focus.value = focus.value === k ? null : k
}

const inWindow = (k, j) => focus.value === k && j < arrow.value.win
const srcHighlighted = (i) => focus.value !== null && i >= focus.value && i < focus.value + arrow.value.win
</script>

<template>
  <div class="ctfp-widget se">
    <div class="ctfp-widget-title">流余单子：duplicate 产生所有焦点，extend 在每个焦点上运行同一个滤波器</div>
    <div class="se-bar">
      <span class="se-label">输入流 s：</span>
      <button v-for="(v, k) in inputs" :key="k" class="ctfp-btn" :class="{ on: inputKey === k }" @click="inputKey = k">{{ v.name }}</button>
    </div>
    <div class="se-bar">
      <span class="se-label">co-Kleisli 箭头 f：</span>
      <button v-for="(v, k) in arrows" :key="k" class="ctfp-btn" :class="{ on: arrowKey === k }" @click="arrowKey = k; focus = null">{{ v.name }}</button>
    </div>
    <div class="se-desc">
      <code>f = {{ arrow.lean }}</code>：{{ arrow.desc }}
    </div>

    <div class="se-scroll">
      <table class="se-table">
        <tbody>
          <tr class="se-src">
            <th>s</th>
            <td v-for="i in N" :key="i" :class="{ hl: srcHighlighted(i - 1) }">{{ fmt(s(i - 1)) }}</td>
            <td class="se-dots">…</td>
            <td class="se-gap"></td>
            <td class="se-res-head"></td>
          </tr>
          <tr v-if="showDup" class="se-caption-row">
            <th></th>
            <td :colspan="N + 1" class="se-caption">duplicate s：第 k 行是 drop k s，焦点（第一格）依次右移</td>
            <td class="se-gap"></td>
            <td class="se-res-head">f 作用在该行</td>
          </tr>
          <template v-if="showDup">
            <tr v-for="k in N" :key="'r' + k" :class="['se-row', { on: focus === k - 1 }]" @click="pick(k - 1)">
              <th>drop {{ k - 1 }}</th>
              <td v-for="i in N" :key="i" :class="{ pad: i < k, focus: i === k, win: i >= k && inWindow(k - 1, i - k) }">
                <template v-if="i >= k">{{ fmt(s(i - 1)) }}</template>
              </td>
              <td class="se-dots">…</td>
              <td class="se-gap">→</td>
              <td class="se-res" :class="{ shown: k - 1 < revealed, on: focus === k - 1 }">
                {{ k - 1 < revealed ? fmt(results[k - 1]) : '?' }}
              </td>
            </tr>
          </template>
          <tr class="se-out">
            <th>extend f s</th>
            <td
              v-for="i in N"
              :key="i"
              :class="{ shown: i - 1 < revealed, on: focus === i - 1 }"
              @click="pick(i - 1)"
            >{{ i - 1 < revealed ? fmt(results[i - 1]) : '?' }}</td>
            <td class="se-dots">…</td>
            <td class="se-gap"></td>
            <td class="se-res-head"></td>
          </tr>
        </tbody>
      </table>
    </div>

    <div class="se-bar se-controls">
      <button class="ctfp-btn" @click="play">▶ 逐个焦点播放 extend</button>
      <button class="ctfp-btn" :class="{ on: showDup }" @click="showDup = !showDup">{{ showDup ? '隐藏' : '显示' }} duplicate</button>
    </div>
    <div class="se-tip">
      点击任意一行或底部任意一格：高亮这个焦点下 f 读取的“窗口”。底部那一行就是把 f 依次用在 duplicate 的每一行上，
      即 <code>extend f = (f &lt;$&gt; ·) ∘ duplicate</code>。
    </div>
  </div>
</template>

<style scoped>
.se-bar {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
  align-items: center;
  margin-bottom: 8px;
}
.se-label {
  font-size: 13px;
  color: var(--vp-c-text-2);
}
.se-desc {
  font-size: 13px;
  color: var(--vp-c-text-2);
  margin-bottom: 10px;
}
.se-scroll {
  overflow-x: auto;
  max-width: 100%;
}
.se-table {
  border-collapse: separate;
  border-spacing: 3px;
  margin: 0;
  display: table;
  font-family: var(--vp-font-family-mono);
  font-size: 13px;
}
.se-table th,
.se-table td {
  border: none;
  padding: 0;
  text-align: center;
  background: none;
}
.se-table tr {
  background: none !important;
  border: none;
}
.se-table th {
  font-weight: 500;
  font-size: 12px;
  color: var(--vp-c-text-2);
  text-align: right;
  padding-right: 8px;
  white-space: nowrap;
}
.se-table td {
  width: 34px;
  min-width: 34px;
  height: 28px;
  border-radius: 5px;
}
.se-src td:not(.se-dots):not(.se-gap):not(.se-res-head) {
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
}
.se-src td.hl {
  border-color: var(--vp-c-warning-1);
  background: color-mix(in srgb, var(--vp-c-warning-1) 18%, var(--vp-c-bg));
}
.se-caption {
  font-family: var(--vp-font-family-base);
  font-size: 12px;
  color: var(--vp-c-text-3);
  text-align: left !important;
  padding-top: 6px !important;
}
.se-res-head {
  font-family: var(--vp-font-family-base);
  font-size: 11px;
  color: var(--vp-c-text-3);
  width: 64px !important;
  white-space: nowrap;
}
.se-row {
  cursor: pointer;
}
.se-row td:not(.pad):not(.se-dots):not(.se-gap):not(.se-res) {
  background: var(--vp-c-bg);
  color: var(--vp-c-text-2);
}
.se-row td.focus {
  color: var(--vp-c-text-1) !important;
  font-weight: 700;
  box-shadow: inset 0 0 0 1.5px var(--vp-c-brand-1);
}
.se-row td.win {
  background: color-mix(in srgb, var(--vp-c-warning-1) 22%, var(--vp-c-bg)) !important;
  color: var(--vp-c-text-1) !important;
}
.se-row.on th {
  color: var(--vp-c-brand-1);
}
.se-dots {
  color: var(--vp-c-text-3);
  width: 18px !important;
  min-width: 18px !important;
}
.se-gap {
  color: var(--vp-c-text-3);
  width: 20px !important;
  min-width: 20px !important;
}
.se-res,
.se-out td:not(.se-dots):not(.se-gap):not(.se-res-head) {
  color: var(--vp-c-text-3);
  border: 1px dashed var(--vp-c-divider);
  transition: all 0.25s;
}
.se-res {
  width: 64px !important;
}
.se-res.shown,
.se-out td.shown {
  color: var(--vp-c-brand-1);
  border: 1px solid var(--vp-c-brand-1);
  background: var(--vp-c-bg);
  font-weight: 600;
}
.se-res.on,
.se-out td.on {
  background: color-mix(in srgb, var(--vp-c-brand-1) 18%, var(--vp-c-bg));
}
.se-out td {
  cursor: pointer;
}
.se-out th {
  color: var(--vp-c-brand-1);
  padding-top: 8px;
}
.se-controls {
  margin-top: 10px;
}
.se-tip {
  font-size: 12px;
  color: var(--vp-c-text-3);
}
</style>
