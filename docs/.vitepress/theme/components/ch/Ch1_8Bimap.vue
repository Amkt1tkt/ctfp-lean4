<script setup>
import { ref, computed, onBeforeUnmount } from 'vue'

const gs = [
  { name: 'n ↦ n * 10', out: 'Nat', fn: (n) => n * 10, show: (v) => String(v) },
  { name: 'n ↦ n + 1', out: 'Nat', fn: (n) => n + 1, show: (v) => String(v) },
  { name: 'n ↦ 是偶数?', out: 'Bool', fn: (n) => n % 2 === 0, show: (v) => (v ? 'true' : 'false') },
]
const hs = [
  { name: 's ↦ s.length', out: 'Nat', fn: (s) => s.length, show: (v) => String(v) },
  { name: 's ↦ s.toUpper', out: 'String', fn: (s) => s.toUpperCase(), show: (v) => `"${v}"` },
  { name: 's ↦ s ++ "!"', out: 'String', fn: (s) => s + '!', show: (v) => `"${v}"` },
]
const showNat = (v) => String(v)
const showStr = (v) => `"${v}"`

const kind = ref('prod') // prod | sum
const side = ref('inl') // sum 的哪一边
const gi = ref(0)
const hi = ref(0)
const step = ref(0) // 0..2
const playing = ref(false)
let timer = 0

const start = { l: 3, r: 'cat' }

// 一个值：{ l, r, ls, rs } 及类型 { lt, rt }；对 sum 只有一边存在
function mk(l, r, ls, rs, lt, rt) {
  return { l, r, ls, rs, lt, rt }
}
const initial = computed(() => mk(start.l, start.r, showNat, showStr, 'Nat', 'String'))

function applyFirst(v) {
  const g = gs[gi.value]
  return { ...v, l: g.fn(v.l), ls: g.show, lt: g.out, changed: 'l' }
}
function applySecond(v) {
  const h = hs[hi.value]
  return { ...v, r: h.fn(v.r), rs: h.show, rt: h.out, changed: 'r' }
}
function applyBoth(v) {
  return { ...applySecond(applyFirst(v)), changed: 'lr' }
}

const lanes = computed(() => {
  const v0 = initial.value
  const a1 = applyFirst(v0)
  const a2 = applySecond(a1)
  const b1 = applySecond(v0)
  const b2 = applyFirst(b1)
  const c1 = applyBoth(v0)
  return [
    { title: 'first g，然后 second h', ops: ['first g', 'second h'], vals: [v0, a1, a2] },
    { title: 'second h，然后 first g', ops: ['second h', 'first g'], vals: [v0, b1, b2] },
    { title: 'bimap g h（一步）', ops: ['bimap g h'], vals: [v0, c1] },
  ]
})

function typeOf(v) {
  return kind.value === 'prod' ? `${v.lt} × ${v.rt}` : `${v.lt} ⊕ ${v.rt}`
}
function render(v, prev) {
  if (kind.value === 'prod') {
    return {
      parts: [
        { t: v.ls(v.l), hot: prev && v.changed?.includes('l') },
        { t: v.rs(v.r), hot: prev && v.changed?.includes('r') },
      ],
      prod: true,
    }
  }
  if (side.value === 'inl') {
    const touched = prev && v.changed?.includes('l')
    const idle = prev && !v.changed?.includes('l')
    return { parts: [{ t: `inl ${v.ls(v.l)}`, hot: touched, idle }], prod: false }
  }
  const touched = prev && v.changed?.includes('r')
  const idle = prev && !v.changed?.includes('r')
  return { parts: [{ t: `inr ${v.rs(v.r)}`, hot: touched, idle }], prod: false }
}

function finalText(v) {
  return render(v, false).parts.map((p) => p.t).join(', ')
}
const allSame = computed(() => {
  const finals = lanes.value.map((l) => finalText(l.vals[l.vals.length - 1]))
  return finals.every((f) => f === finals[0]) ? finals[0] : null
})

function visible(lane, i) {
  if (i === 0) return true
  if (lane.vals.length === 2) return step.value >= 1
  return step.value >= i
}

function stop() {
  clearTimeout(timer)
  playing.value = false
}
function run() {
  stop()
  step.value = 0
  playing.value = true
  const adv = () => {
    step.value++
    if (step.value < 2) timer = setTimeout(adv, 1000)
    else playing.value = false
  }
  timer = setTimeout(adv, 500)
}
function changed() {
  stop()
  step.value = 0
}
onBeforeUnmount(stop)
</script>

<template>
  <div class="ctfp-widget bm-widget">
    <div class="ctfp-widget-title">双函子：first、second 与 bimap</div>
    <div class="row">
      <span class="lbl">双函子：</span>
      <button class="ctfp-btn" :class="{ on: kind === 'prod' }" @click="kind = 'prod'; changed()">积 Prod</button>
      <button class="ctfp-btn" :class="{ on: kind === 'sum' }" @click="kind = 'sum'; changed()">余积 Sum</button>
      <template v-if="kind === 'sum'">
        <span class="lbl">值在：</span>
        <button class="ctfp-btn" :class="{ on: side === 'inl' }" @click="side = 'inl'; changed()">inl 3</button>
        <button class="ctfp-btn" :class="{ on: side === 'inr' }" @click="side = 'inr'; changed()">inr "cat"</button>
      </template>
    </div>
    <div class="row">
      <span class="lbl">g : Nat → ?</span>
      <button v-for="(g, i) in gs" :key="g.name" class="ctfp-btn" :class="{ on: gi === i }" @click="gi = i; changed()">{{ g.name }}</button>
    </div>
    <div class="row">
      <span class="lbl">h : String → ?</span>
      <button v-for="(h, i) in hs" :key="h.name" class="ctfp-btn" :class="{ on: hi === i }" @click="hi = i; changed()">{{ h.name }}</button>
    </div>
    <div class="row"><button class="ctfp-btn run" @click="run">▶ 三条路线同时运行</button></div>

    <div class="lanes">
      <div v-for="(lane, li) in lanes" :key="li" class="lane">
        <div class="lane-title">{{ lane.title }}</div>
        <template v-for="(v, i) in lane.vals" :key="i">
          <div v-if="i > 0" class="op" :class="{ show: visible(lane, i) }">↓ <code>{{ lane.ops[i - 1] }}</code></div>
          <div class="val" :class="{ show: visible(lane, i) }">
            <div class="v"><span class="paren">{{ render(v, i > 0).prod ? '(' : '' }}</span>
            <template v-for="(p, pi) in render(v, i > 0).parts" :key="pi">
              <span v-if="pi > 0" class="paren">, </span>
              <span class="part" :class="{ hot: p.hot && visible(lane, i), idle: p.idle }">{{ p.t }}</span>
            </template>
            <span class="paren">{{ render(v, i > 0).prod ? ')' : '' }}</span></div>
            <div class="ty">: {{ typeOf(v) }}</div>
          </div>
        </template>
      </div>
    </div>
    <p class="verdict" :class="{ show: step >= 2 }">
      <template v-if="allSame">三条路线的结果都是 <code>{{ allSame }}</code>——这就是定理 <code>first_second_comm</code> 与 <code>bimap_eq_first_second</code>。</template>
    </p>
    <p class="hint">
      高亮的分量表示这一步改动了它。
      <template v-if="kind === 'sum'">对余积而言，一个值只在一边，所以总有一个函数“扑空”（灰色表示这一步什么也没做）。</template>
      <template v-else>对积而言，两个分量互不干扰，所以先改哪个都一样。</template>
    </p>
  </div>
</template>

<style scoped>
.bm-widget { max-width: 100%; }
.row { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; margin-bottom: 6px; }
.lbl { font-size: 13px; color: var(--vp-c-text-2); min-width: 92px; font-family: var(--vp-font-family-mono); }
.run { border-color: var(--vp-c-brand-1); color: var(--vp-c-brand-1); }
.lanes { display: grid; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr)); gap: 12px; margin-top: 10px; }
.lane { border: 1px solid var(--vp-c-divider); border-radius: 10px; padding: 10px; background: var(--vp-c-bg); text-align: center; }
.lane-title { font-size: 13px; font-weight: 600; margin-bottom: 8px; color: var(--vp-c-text-2); }
.val { font-family: var(--vp-font-family-mono); font-size: 15px; padding: 6px 4px; border-radius: 8px; opacity: 0.12; transition: opacity 0.4s; }
.val.show { opacity: 1; }
.op { font-size: 12px; color: var(--vp-c-text-3); opacity: 0.12; transition: opacity 0.4s; }
.op.show { opacity: 1; }
.part { padding: 1px 4px; border-radius: 5px; transition: all 0.3s; }
.part.hot { background: var(--vp-c-brand-soft); color: var(--vp-c-brand-1); font-weight: 600; }
.part.idle { color: var(--vp-c-text-3); text-decoration: underline dotted; }
.paren { color: var(--vp-c-text-2); white-space: pre; }
.v { display: flex; justify-content: center; align-items: baseline; flex-wrap: wrap; }
.ty { font-size: 11px; color: var(--vp-c-text-3); margin-top: 2px; }
.verdict { min-height: 1.6em; font-size: 14px; opacity: 0; transition: opacity 0.4s; }
.verdict.show { opacity: 1; }
.hint { font-size: 12px; color: var(--vp-c-text-3); margin: 4px 0 0; }
</style>
