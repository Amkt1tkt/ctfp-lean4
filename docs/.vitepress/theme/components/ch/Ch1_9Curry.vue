<script setup>
import { ref, computed } from 'vue'

const Z = ['苹果', '香蕉', '樱桃']
const A = ['小杯', '中杯', '大杯']
const table = ref([
  [5, 7, 9],
  [4, 6, 8],
  [8, 11, 14],
])
const curried = ref(false)
const pick = ref({ z: 0, a: 1 })

function randomize() {
  table.value = Z.map(() => A.map(() => 3 + Math.floor(Math.random() * 13)))
}
function choose(z, a) {
  pick.value = { z, a }
}

const p = computed(() => pick.value)
const v = computed(() => table.value[p.value.z][p.value.a])
const rowStr = (z) => '[' + A.map((a, i) => `${a} ↦ ${table.value[z][i]}`).join(', ') + ']'
</script>

<template>
  <div class="ctfp-widget cur-widget">
    <div class="ctfp-widget-title">柯里化：一张二维表 ⇄ 一列一维表</div>
    <div class="ctl">
      <button class="ctfp-btn" :class="{ on: !curried }" @click="curried = false">二维表：g : 水果 × 杯型 → 价格</button>
      <button class="ctfp-btn" :class="{ on: curried }" @click="curried = true">柯里化：h : 水果 → (杯型 → 价格)</button>
      <button class="ctfp-btn" @click="randomize">随机改价</button>
    </div>

    <div class="board" :class="{ curried }">
      <div class="hdr-row" :class="{ fade: curried }">
        <div class="corner">g</div>
        <div v-for="a in A" :key="a" class="colh">{{ a }}</div>
      </div>
      <div v-for="(z, zi) in Z" :key="z" class="row" :class="{ sel: curried && p.z === zi }">
        <div class="rowh">{{ z }}<span class="maps">&nbsp;↦</span></div>
        <div class="fn">
          <div class="fn-label">h {{ z }} : 杯型 → 价格</div>
          <div class="cells">
            <button
              v-for="(a, ai) in A"
              :key="a"
              class="cell"
              :class="{ hit: p.z === zi && p.a === ai }"
              @click="choose(zi, ai)"
            >
              <span class="inner-a">{{ a }} ↦</span>
              <span class="num">{{ table[zi][ai] }}</span>
            </button>
          </div>
        </div>
      </div>
    </div>

    <div class="readout mono">
      <div v-if="!curried">g ({{ Z[p.z] }}, {{ A[p.a] }}) = <b>{{ v }}</b></div>
      <template v-else>
        <div>h {{ Z[p.z] }} = {{ rowStr(p.z) }}</div>
        <div>h {{ Z[p.z] }} {{ A[p.a] }} = <b>{{ v }}</b></div>
      </template>
      <div class="dim">
        {{ curried ? '反柯里化回去' : '柯里化之后' }}：
        <template v-if="curried">uncurry h ({{ Z[p.z] }}, {{ A[p.a] }}) = eval (h {{ Z[p.z] }}, {{ A[p.a] }}) = {{ v }}</template>
        <template v-else>curry g {{ Z[p.z] }} {{ A[p.a] }} = {{ v }}</template>
      </div>
    </div>
    <p class="hint">
      点任意一格看它在两种视角下的读法。切换视角时，表里的数字一个都没变——变的只是“怎么分组”：
      二维表按 (行, 列) 一次查到底；柯里化后先用行 z 查出一整行（一个函数 h z），再用列 a 在这一行里查。
      这就是 <code>(价格^杯型)^水果 ≅ 价格^(水果 × 杯型)</code>。
    </p>
  </div>
</template>

<style scoped>
.cur-widget { max-width: 100%; }
.ctl { display: flex; flex-wrap: wrap; gap: 6px; margin-bottom: 10px; }
.mono { font-family: var(--vp-font-family-mono); }
.board { display: flex; flex-direction: column; gap: 0; transition: gap 0.45s; overflow-x: auto; }
.board.curried { gap: 10px; }
.hdr-row, .row { display: flex; align-items: stretch; }
.hdr-row { transition: opacity 0.4s, max-height 0.45s; max-height: 40px; overflow: hidden; }
.hdr-row.fade { opacity: 0; max-height: 0; }
.corner, .rowh { width: 74px; flex: none; font-size: 13px; display: flex; align-items: center; justify-content: center; color: var(--vp-c-text-2); }
.corner { font-family: var(--vp-font-family-mono); font-style: italic; }
.colh { flex: 1; min-width: 64px; text-align: center; font-size: 13px; color: var(--vp-c-text-2); padding: 6px 0; border-bottom: 1px solid var(--vp-c-divider); }
.rowh { font-weight: 600; color: var(--vp-c-text-1); border-right: 1px solid var(--vp-c-divider); transition: border-color 0.4s; }
.curried .rowh { border-right-color: transparent; }
.maps { color: var(--vp-c-brand-1); opacity: 0; transition: opacity 0.4s; }
.curried .maps { opacity: 1; }
.fn { flex: 1; border: 1px solid transparent; border-radius: 0; transition: all 0.45s; padding: 0; }
.curried .fn { border-color: var(--vp-c-divider); border-radius: 10px; padding: 4px 8px 6px; background: var(--vp-c-bg); }
.curried .row.sel .fn { border-color: var(--vp-c-brand-1); box-shadow: 0 0 0 2px var(--vp-c-brand-soft); }
.fn-label { font-size: 11px; color: var(--vp-c-text-3); font-family: var(--vp-font-family-mono); max-height: 0; opacity: 0; overflow: hidden; transition: all 0.45s; }
.curried .fn-label { max-height: 20px; opacity: 1; margin-bottom: 3px; }
.cells { display: flex; gap: 0; transition: gap 0.45s; }
.curried .cells { gap: 6px; }
.cell {
  flex: 1; min-width: 64px; border: none; border-bottom: 1px solid var(--vp-c-divider); background: transparent;
  padding: 8px 4px; font-size: 15px; cursor: pointer; color: var(--vp-c-text-1); transition: all 0.3s; border-radius: 0;
  display: flex; justify-content: center; gap: 4px; align-items: baseline;
}
.curried .cell { border: 1px solid var(--vp-c-divider); border-radius: 6px; padding: 4px; }
.cell:hover { background: var(--vp-c-bg-soft); }
.cell.hit { background: var(--vp-c-brand-soft); color: var(--vp-c-brand-1); font-weight: 600; }
.inner-a { font-size: 11px; color: var(--vp-c-text-3); max-width: 0; overflow: hidden; white-space: nowrap; transition: max-width 0.45s; }
.curried .inner-a { max-width: 60px; }
.num { font-family: var(--vp-font-family-mono); }
.readout { margin-top: 12px; font-size: 14px; line-height: 1.8; }
.readout .dim { color: var(--vp-c-text-2); font-size: 13px; }
.hint { font-size: 12px; color: var(--vp-c-text-3); margin: 8px 0 0; }
</style>
