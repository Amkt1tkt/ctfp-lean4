<script setup>
import { ref, computed } from 'vue'

const N = 8
const elems = Array.from({ length: N }, (_, i) => i)
const members = ref(new Set([0, 2, 4, 6]))
const focus = ref(null)

const presets = [
  { label: '偶数', pred: (x) => x % 2 === 0 },
  { label: '质数', pred: (x) => [2, 3, 5, 7].includes(x) },
  { label: '≥ 5', pred: (x) => x >= 5 },
  { label: '空集', pred: () => false },
  { label: '全集', pred: () => true },
]

function applyPreset(p) {
  members.value = new Set(elems.filter(p.pred))
  focus.value = null
}
function toggle(x) {
  const s = new Set(members.value)
  if (s.has(x)) s.delete(x)
  else s.add(x)
  members.value = s
  focus.value = x
}
const chi = (x) => members.value.has(x)
const sub = computed(() => elems.filter(chi))
const bits = computed(() => elems.map((x) => (chi(x) ? '1' : '0')).join(''))
const index = computed(() => parseInt([...bits.value].reverse().join(''), 2))
const leanList = computed(() => sub.value.join(', '))

// 拉回图的几何
const W = 560
const H = 330
const bx = (x) => 40 + x * 34
const yA = 70
const yB = 250
const oneX = 470
const oneY = yA
const omX = 470
const trueY = yB - 22
const falseY = yB + 32

function isFocus(x) {
  return focus.value === x
}
const focusIn = computed(() => focus.value !== null && chi(focus.value))
</script>

<template>
  <div class="ctfp-widget subset">
    <div class="ctfp-widget-title">特征函数与子集：χ : b → Ω 与拉回</div>
    <div class="hint">点击元素把它加入或移出子集 a ⊆ b = {0,…,7}；点过的元素会在拉回图中高亮它的两条路线。</div>

    <div class="row">
      <div class="presets">
        <span class="lbl">预设：</span>
        <button v-for="p in presets" :key="p.label" class="ctfp-btn small" @click="applyPreset(p)">{{ p.label }}</button>
      </div>
    </div>

    <div class="chips">
      <button
        v-for="x in elems"
        :key="x"
        class="chip"
        :class="{ in: chi(x), focus: isFocus(x) }"
        @click="toggle(x)"
      >{{ x }}</button>
    </div>

    <div class="tablewrap">
      <table class="chi">
        <tbody>
          <tr>
            <th class="rh">x</th>
            <td v-for="x in elems" :key="x" :class="{ focus: isFocus(x) }" @click="focus = x">{{ x }}</td>
          </tr>
          <tr>
            <th class="rh">χ(x)</th>
            <td v-for="x in elems" :key="x" :class="[chi(x) ? 't' : 'f', { focus: isFocus(x) }]" @click="focus = x">{{ chi(x) ? 'true' : 'false' }}</td>
          </tr>
        </tbody>
      </table>
    </div>

    <div class="panels">
      <div class="svg-panel">
        <svg :viewBox="`0 0 ${W} ${H}`" class="pb">
          <defs>
            <marker id="ch313-ah" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
              <path d="M0,0 L10,5 L0,10 L3,5 z" fill="context-stroke" />
            </marker>
          </defs>

          <!-- 区域 -->
          <rect x="18" :y="yA - 30" width="282" height="60" rx="14" class="blob a" />
          <text x="24" :y="yA - 38" class="region">a = {x | χ x = true}</text>
          <rect x="18" :y="yB - 30" width="282" height="60" rx="14" class="blob b" />
          <text x="24" :y="yB + 50" class="region">b</text>
          <circle :cx="oneX" :cy="oneY" r="24" class="blob one" />
          <text :x="oneX + 30" :y="oneY - 22" class="region">1</text>
          <rect :x="omX - 40" :y="trueY - 24" width="80" height="98" rx="14" class="blob om" />
          <text :x="omX + 46" :y="trueY - 10" class="region">Ω</text>

          <!-- f : a → b（垂直平行的箭头：单射） -->
          <line
            v-for="x in sub" :key="'f' + x"
            :x1="bx(x)" :y1="yA + 10" :x2="bx(x)" :y2="yB - 12"
            class="arr f" :class="{ hi: isFocus(x), dim: focus !== null && !isFocus(x) }"
            marker-end="url(#ch313-ah)"
          />
          <!-- unit : a → 1 -->
          <line
            v-for="x in sub" :key="'u' + x"
            :x1="bx(x) + 8" :y1="yA" :x2="oneX - 26" :y2="oneY"
            class="arr u" :class="{ hi: isFocus(x), dim: focus !== null && !isFocus(x) }"
            marker-end="url(#ch313-ah)"
          />
          <!-- χ : b → Ω -->
          <line
            v-for="x in elems" :key="'c' + x"
            :x1="bx(x) + 8" :y1="yB" :x2="omX - 30" :y2="chi(x) ? trueY : falseY"
            class="arr c" :class="[chi(x) ? 'ct' : 'cf', { hi: isFocus(x), dim: focus !== null && !isFocus(x) }]"
            marker-end="url(#ch313-ah)"
          />
          <!-- true : 1 → Ω -->
          <line :x1="oneX" :y1="oneY + 26" :x2="omX" :y2="trueY - 14" class="arr tr" :class="{ hi: focusIn }" marker-end="url(#ch313-ah)" />

          <!-- 箭头名 -->
          <text x="8" :y="(yA + yB) / 2" class="aname">f</text>
          <text :x="(300 + oneX) / 2 + 20" :y="yA - 8" class="aname">unit</text>
          <text :x="oneX + 8" :y="(oneY + trueY) / 2" class="aname">true</text>
          <text :x="(300 + omX) / 2 - 10" :y="yB - 24" class="aname">χ</text>

          <!-- 元素 -->
          <g v-for="x in sub" :key="'ea' + x">
            <circle :cx="bx(x)" :cy="yA" r="9" class="dot in" :class="{ focus: isFocus(x) }" />
            <text :x="bx(x)" :y="yA + 4" class="dlabel">{{ x }}</text>
          </g>
          <text v-if="!sub.length" x="159" :y="yA + 5" class="empty">（空）</text>
          <g v-for="x in elems" :key="'eb' + x" style="cursor: pointer" @click="toggle(x)">
            <circle :cx="bx(x)" :cy="yB" r="9" class="dot" :class="{ in: chi(x), focus: isFocus(x) }" />
            <text :x="bx(x)" :y="yB + 4" class="dlabel">{{ x }}</text>
          </g>
          <circle :cx="oneX" :cy="oneY" r="6" class="dot star" />
          <text :x="oneX" :y="oneY + 18" class="small">()</text>
          <circle :cx="omX" :cy="trueY" r="8" class="dot tv" />
          <text :x="omX" :y="trueY + 24" class="small">true</text>
          <circle :cx="omX" :cy="falseY" r="8" class="dot fv" />
          <text :x="omX" :y="falseY + 24" class="small">false</text>
        </svg>
      </div>
    </div>

    <div class="explain">
      <template v-if="focus === null">
        方块交换：对 a 中每个元素，<b>true ∘ unit</b> 与 <b>χ ∘ f</b> 都把它送到 true。而 b 中 χ 取 false 的元素，在 a 里没有原像。
      </template>
      <template v-else-if="focusIn">
        元素 <b>{{ focus }}</b> ∈ a：沿 unit 到 ()，再沿 true 到 <span class="t">true</span>；沿 f 到 b 中的 {{ focus }}，再沿 χ 也到 <span class="t">true</span>。两条路线一致。
      </template>
      <template v-else>
        元素 <b>{{ focus }}</b> ∉ a：χ {{ focus }} = <span class="f">false</span>。拉回只收集那些 χ 送到 true 的元素，所以 {{ focus }} 不在 a 中。
      </template>
    </div>

    <div class="footer">
      <div>χ 的表格横过来读：<code>{{ bits }}</code>（第 {{ index }} 号）——8 元素集合有 2<sup>8</sup> = 256 个子集，恰好对应 256 个函数 b → Bool：Sub(b) ≅ C(b, Ω)。</div>
      <div class="lean"><code>{x : Fin 8 // x.val ∈ [{{ leanList }}]}</code>　共 {{ sub.length }} 个元素；<code>Subtype.val</code> 就是 f。</div>
    </div>
  </div>
</template>

<style scoped>
.subset { max-width: 100%; }
.hint { font-size: 13px; color: var(--vp-c-text-2); margin-bottom: 8px; }
.presets { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; }
.lbl { font-size: 13px; color: var(--vp-c-text-2); }
.ctfp-btn.small { padding: 2px 10px; }
.chips { display: flex; flex-wrap: wrap; gap: 8px; margin: 10px 0; justify-content: center; }
.chip {
  width: 38px; height: 38px; border-radius: 50%;
  border: 2px solid var(--vp-c-divider);
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  font-weight: 700; cursor: pointer; transition: all 0.15s;
}
.chip.in { background: var(--vp-c-brand-1); border-color: var(--vp-c-brand-1); color: var(--vp-c-white, #fff); }
.chip.focus { box-shadow: 0 0 0 3px color-mix(in srgb, var(--vp-c-warning-1) 60%, transparent); }
.panels { max-width: 600px; margin: 0 auto; }
.tablewrap { overflow-x: auto; margin-bottom: 10px; }
.tablewrap table.chi { border-collapse: collapse; font-size: 13px; margin: 0 auto; display: table; }
.chi th, .chi td { padding: 2px 8px; border: 1px solid var(--vp-c-divider); text-align: center; }
.chi td { font-family: var(--vp-font-family-mono); cursor: pointer; min-width: 44px; }
.chi th.rh { font-style: italic; background: var(--vp-c-bg); }
.chi td.focus { background: color-mix(in srgb, var(--vp-c-warning-1) 18%, transparent); }
td.t, .t { color: var(--vp-c-success-1, #18794e); font-weight: 600; }
td.f, .f { color: var(--vp-c-danger-1); font-weight: 600; }
.pb { width: 100%; height: auto; display: block; background: var(--vp-c-bg); border: 1px solid var(--vp-c-divider); border-radius: 10px; }
.blob { stroke-width: 1.2; }
.blob.a { fill: color-mix(in srgb, var(--vp-c-danger-1) 12%, transparent); stroke: var(--vp-c-danger-1); }
.blob.b { fill: color-mix(in srgb, var(--vp-c-brand-1) 12%, transparent); stroke: var(--vp-c-brand-1); }
.blob.one { fill: color-mix(in srgb, var(--vp-c-warning-1) 18%, transparent); stroke: var(--vp-c-warning-1); }
.blob.om { fill: color-mix(in srgb, var(--vp-c-text-3) 12%, transparent); stroke: var(--vp-c-text-3); }
.region { font-size: 13px; font-weight: 700; fill: var(--vp-c-text-1); font-style: italic; }
.aname { font-size: 14px; font-style: italic; fill: var(--vp-c-text-2); font-weight: 600; }
.arr { stroke-width: 1.3; stroke: var(--vp-c-text-3); transition: opacity 0.2s, stroke-width 0.2s; }
.arr.f { stroke: var(--vp-c-danger-1); }
.arr.u { stroke: var(--vp-c-warning-1); }
.arr.c.ct { stroke: var(--vp-c-success-1, #18794e); }
.arr.c.cf { stroke: var(--vp-c-text-3); stroke-dasharray: 4 4; }
.arr.tr { stroke: var(--vp-c-success-1, #18794e); stroke-width: 2; }
.arr.hi { stroke-width: 3; opacity: 1; }
.arr.dim { opacity: 0.18; }
.dot { fill: var(--vp-c-bg); stroke: var(--vp-c-text-2); stroke-width: 1.5; }
.dot.in { fill: var(--vp-c-brand-1); stroke: var(--vp-c-brand-1); }
.dot.focus { stroke: var(--vp-c-warning-1); stroke-width: 3; }
.dot.star { fill: var(--vp-c-warning-1); stroke: none; }
.dot.tv { fill: var(--vp-c-success-1, #18794e); stroke: none; }
.dot.fv { fill: var(--vp-c-danger-1); stroke: none; }
.dlabel { font-size: 10px; text-anchor: middle; fill: var(--vp-c-text-1); pointer-events: none; font-weight: 700; }
.dot.in + .dlabel { fill: #fff; }
.small { font-size: 11px; text-anchor: middle; fill: var(--vp-c-text-2); }
.empty { font-size: 12px; text-anchor: middle; fill: var(--vp-c-text-3); }
.explain { font-size: 13px; margin-top: 10px; padding: 8px 12px; border-radius: 8px; background: var(--vp-c-bg); border: 1px solid var(--vp-c-divider); }
.footer { font-size: 12px; color: var(--vp-c-text-2); margin-top: 8px; line-height: 1.8; }
.footer code { font-size: 12px; }
.lean { word-break: break-all; }
</style>
