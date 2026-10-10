<script setup>
// 伴随的 hom-集同构：L = (· × Bool) ⊣ R = (Bool → ·)，取 c = Bool。
// 左边列出 L d → c 的全部态射，右边列出 d → R c 的全部态射；柯里化给出一一对应。
import { computed, ref } from 'vue'

const dChoice = ref('two') // 'one' | 'two'
const dElems = computed(() => (dChoice.value === 'one' ? ['⋆'] : ['x', 'y']))
const n = computed(() => dElems.value.length)
const total = computed(() => 1 << (2 * n.value))

// 一个态射用 2n 个比特表示：bits[i*2 + b] = f(d_i, b)，b = 0(false) / 1(true)
const toBits = (code) => Array.from({ length: 2 * n.value }, (_, k) => (code >> k) & 1)
const fromBits = (bits) => bits.reduce((acc, v, k) => acc | (v << k), 0)

// Bool → Bool 的四个函数，按“名字”排序
const BB = [
  { name: 'const false', out: [0, 0] },
  { name: 'id', out: [0, 1] },
  { name: 'not', out: [1, 0] },
  { name: 'const true', out: [1, 1] },
]
const bbIndex = (o0, o1) => BB.findIndex((g) => g.out[0] === o0 && g.out[1] === o1)

// 左侧按“列优先”比特串排序：先看所有 (d, false)，再看所有 (d, true)
const leftOrder = computed(() => {
  const codes = Array.from({ length: total.value }, (_, c) => c)
  const key = (c) => {
    const b = toBits(c)
    const col = []
    for (let v = 0; v < 2; v++) for (let i = 0; i < n.value; i++) col.push(b[i * 2 + v])
    return col.join('')
  }
  return codes.sort((a, b) => (key(a) < key(b) ? -1 : 1))
})
// 右侧按每个 d_i 被送到的 Bool → Bool 函数的名字顺序排序
const rightOrder = computed(() => {
  const codes = Array.from({ length: total.value }, (_, c) => c)
  const key = (c) => {
    const b = toBits(c)
    return dElems.value.map((_, i) => bbIndex(b[i * 2], b[i * 2 + 1])).join('')
  }
  return codes.sort((a, b) => (key(a) < key(b) ? -1 : 1))
})

const selected = ref(null)
const showNumbers = ref(false)
const lastAction = ref('')
const pairNo = (code) => leftOrder.value.indexOf(code) + 1

function pick(code) {
  selected.value = code
  lastAction.value = ''
}
function setD(v) {
  dChoice.value = v
  selected.value = null
  lastAction.value = ''
}
function flip(i, b) {
  if (selected.value === null) selected.value = 0
  const bits = toBits(selected.value)
  bits[i * 2 + b] ^= 1
  selected.value = fromBits(bits)
  lastAction.value = ''
}
// 自然性：在 c 上后复合 not（左边 not ∘ f，右边 Functor.map not ∘ g）
function postNot() {
  if (selected.value === null) return
  selected.value = fromBits(toBits(selected.value).map((v) => v ^ 1))
  lastAction.value = 'c'
}
// 自然性：在 d 上前复合 swap（左边 f ∘ L swap，右边 g ∘ swap）
function preSwap() {
  if (selected.value === null || n.value < 2) return
  const b = toBits(selected.value)
  selected.value = fromBits([b[2], b[3], b[0], b[1]])
  lastAction.value = 'd'
}

const selBits = computed(() => (selected.value === null ? null : toBits(selected.value)))
const B = (v) => (v ? 'true' : 'false')
</script>

<template>
  <div class="ctfp-widget hsb">
    <div class="ctfp-widget-title">伴随的 hom-集同构：(· × Bool) ⊣ (Bool → ·)，取 c = Bool</div>
    <div class="hsb-controls">
      <span>d 取：</span>
      <button class="ctfp-btn" :class="{ on: dChoice === 'one' }" @click="setD('one')">Unit（1 个元素 ⋆）</button>
      <button class="ctfp-btn" :class="{ on: dChoice === 'two' }" @click="setD('two')">{x, y}（2 个元素）</button>
      <label class="hsb-check"><input type="checkbox" v-model="showNumbers" /> 显示配对编号</label>
    </div>
    <p class="hsb-hint">
      点选任意一张卡片，另一侧与它对应的卡片会同时高亮。每张左侧卡片是一张小表：行是 d 的元素，列是第二个分量
      <code>false</code>/<code>true</code>，格子里是 f 的输出（0 = false，1 = true）。右侧卡片把同一张表<b>按行读</b>——
      这就是柯里化。两边都恰好有 {{ total }} 个态射。
    </p>

    <div class="hsb-grid">
      <div class="hsb-col">
        <div class="hsb-head">左：C(L d, c) = (d × Bool → Bool)</div>
        <div class="hsb-cards">
          <button
            v-for="code in leftOrder" :key="'l' + code"
            class="hsb-card" :class="{ sel: selected === code }"
            @click="pick(code)"
          >
            <span v-if="showNumbers" class="hsb-no">#{{ pairNo(code) }}</span>
            <table class="mini">
              <tr><th></th><th>F</th><th>T</th></tr>
              <tr v-for="(e, i) in dElems" :key="e">
                <th>{{ e }}</th>
                <td :class="{ one: toBits(code)[i * 2] }">{{ toBits(code)[i * 2] }}</td>
                <td :class="{ one: toBits(code)[i * 2 + 1] }">{{ toBits(code)[i * 2 + 1] }}</td>
              </tr>
            </table>
          </button>
        </div>
      </div>
      <div class="hsb-col">
        <div class="hsb-head">右：D(d, R c) = (d → (Bool → Bool))</div>
        <div class="hsb-cards right-cards">
          <button
            v-for="code in rightOrder" :key="'r' + code"
            class="hsb-card right" :class="{ sel: selected === code }"
            @click="pick(code)"
          >
            <span v-if="showNumbers" class="hsb-no">#{{ pairNo(code) }}</span>
            <div v-for="(e, i) in dElems" :key="e" class="hsb-row">
              {{ e }} ↦ <code>{{ BB[bbIndex(toBits(code)[i * 2], toBits(code)[i * 2 + 1])].name }}</code>
            </div>
          </button>
        </div>
      </div>
    </div>

    <div class="hsb-detail">
      <template v-if="selBits">
        <div class="hsb-pair">
          <div>
            <div class="hsb-sub">f : d × Bool → Bool（点格子可以改输出）</div>
            <table class="big">
              <tr><th>输入</th><th>输出</th></tr>
              <template v-for="(e, i) in dElems" :key="e">
                <tr v-for="b in [0, 1]" :key="e + b">
                  <td><code>({{ e }}, {{ B(b) }})</code></td>
                  <td><button class="cell" :class="{ one: selBits[i * 2 + b] }" @click="flip(i, b)">{{ B(selBits[i * 2 + b]) }}</button></td>
                </tr>
              </template>
            </table>
          </div>
          <div class="hsb-arrows">
            <div>leftAdjunct = curry →</div>
            <div>← rightAdjunct = uncurry</div>
          </div>
          <div>
            <div class="hsb-sub">g = curry f : d → (Bool → Bool)</div>
            <table class="big">
              <tr><th>输入</th><th>输出（一个函数）</th></tr>
              <tr v-for="(e, i) in dElems" :key="e">
                <td><code>{{ e }}</code></td>
                <td>
                  <code>{{ BB[bbIndex(selBits[i * 2], selBits[i * 2 + 1])].name }}</code>
                  <span class="muted">（false ↦ {{ B(selBits[i * 2]) }}，true ↦ {{ B(selBits[i * 2 + 1]) }}）</span>
                </td>
              </tr>
            </table>
          </div>
        </div>
        <div class="hsb-nat">
          <span>检验自然性：</span>
          <button class="ctfp-btn" @click="postNot">在 c 上后复合 not</button>
          <button class="ctfp-btn" :disabled="n < 2" @click="preSwap">在 d 上前复合 swap（交换 x, y）</button>
        </div>
        <p v-if="lastAction === 'c'" class="hsb-msg">
          左边变成了 <code>not ∘ f</code>，右边变成了 <code>Functor.map not ∘ g</code>（每一行的函数都被后复合了 not），
          而两者<b>仍然配成一对</b>：<code>curry (not ∘ f) = Functor.map not ∘ curry f</code>。这就是“在 c 上自然”。
        </p>
        <p v-else-if="lastAction === 'd'" class="hsb-msg">
          左边变成了 <code>f ∘ L swap</code>（表的两行互换），右边变成了 <code>g ∘ swap</code>，两者<b>仍然配成一对</b>：
          <code>curry (f ∘ Prod.map swap id) = curry f ∘ swap</code>。这就是“在 d 上自然”。
        </p>
      </template>
      <p v-else class="muted">先点选上面任意一张卡片。</p>
    </div>
  </div>
</template>

<style scoped>
.hsb-controls { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; font-size: 14px; }
.hsb-check { font-size: 13px; margin-left: 8px; color: var(--vp-c-text-2); }
.hsb-hint { font-size: 13px; color: var(--vp-c-text-2); margin: 10px 0; line-height: 1.6; }
.hsb { max-width: 100%; overflow: hidden; }
.hsb-grid { display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 1.25fr); gap: 14px; }
.hsb-col { min-width: 0; }
@media (max-width: 640px) { .hsb-grid { grid-template-columns: minmax(0, 1fr); } }
.hsb-head { font-size: 13px; font-weight: 600; margin-bottom: 6px; color: var(--vp-c-text-1); }
.hsb-cards { display: grid; grid-template-columns: repeat(auto-fill, minmax(64px, 1fr)); gap: 6px; }
.hsb-cards.right-cards { grid-template-columns: repeat(auto-fill, minmax(118px, 1fr)); }
.hsb-card {
  position: relative; border: 1px solid var(--vp-c-divider); border-radius: 8px; background: var(--vp-c-bg);
  padding: 6px 4px; cursor: pointer; font-size: 11px; color: var(--vp-c-text-1); transition: all 0.15s;
  display: flex; flex-direction: column; align-items: center; justify-content: center; min-height: 54px;
}
.hsb-card:hover { border-color: var(--vp-c-brand-1); }
.hsb-card.sel { border: 2px solid var(--vp-c-brand-1); background: var(--vp-c-brand-soft); transform: scale(1.04); }
.hsb-card.right { align-items: flex-start; padding-left: 7px; }
.hsb-row { line-height: 1.5; font-size: 10.5px; }
.hsb-row code { font-size: 10px; padding: 0 2px; white-space: nowrap; }
.hsb-no { position: absolute; top: 1px; right: 4px; font-size: 9.5px; color: var(--vp-c-text-3); }
table.mini { border-collapse: collapse; margin: 0; display: table; }
table.mini th, table.mini td { border: none; padding: 0 4px; font-size: 10.5px; line-height: 1.4; background: transparent; }
table.mini th { color: var(--vp-c-text-3); font-weight: 500; }
table.mini td.one, .cell.one { color: var(--vp-c-brand-1); font-weight: 700; }
table.mini tr { background: transparent; border: none; }
.hsb-detail { margin-top: 14px; padding-top: 12px; border-top: 1px dashed var(--vp-c-divider); }
.hsb-pair { display: flex; flex-wrap: wrap; gap: 16px; align-items: center; }
.hsb-pair > div { min-width: 0; max-width: 100%; }
.hsb-sub { font-size: 13px; color: var(--vp-c-text-2); margin-bottom: 4px; }
table.big { margin: 0; font-size: 13px; }
table.big td, table.big th { padding: 3px 10px; }
.hsb-arrows { font-size: 13px; color: var(--vp-c-brand-1); font-weight: 600; text-align: center; line-height: 2; }
.cell { border: 1px solid var(--vp-c-divider); border-radius: 6px; padding: 0 8px; background: var(--vp-c-bg); cursor: pointer; font-family: var(--vp-font-family-mono); font-size: 12px; }
.cell:hover { border-color: var(--vp-c-brand-1); }
.hsb-nat { margin-top: 12px; display: flex; flex-wrap: wrap; gap: 8px; align-items: center; font-size: 13px; }
.hsb-nat .ctfp-btn:disabled { opacity: 0.4; cursor: not-allowed; }
.hsb-msg { font-size: 13px; line-height: 1.7; margin: 10px 0 0; color: var(--vp-c-text-1); }
.muted { color: var(--vp-c-text-3); font-size: 12px; }
</style>
