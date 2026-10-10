<script setup>
import { ref, computed, watch } from 'vue'

// a = Bool。目标类型 x ∈ {Bool, Unit, Color}
const TYPES = [
  { name: 'Bool', vals: ['true', 'false'] },
  { name: 'Unit', vals: ['()'] },
  { name: 'Color', vals: ['.r', '.g', '.b'] },
]

function fnName(x, vt, vf) {
  if (x === 'Bool') {
    if (vt === 'true' && vf === 'false') return 'id'
    if (vt === 'false' && vf === 'true') return 'not'
    return `fun _ => ${vt}`
  }
  if (vt === vf) return `fun _ => ${vt}`
  return `(if · then ${vt} else ${vf})`
}

// 全部 h : Bool → x
const rows = computed(() => {
  const out = []
  for (const t of TYPES) {
    for (const vt of t.vals) {
      for (const vf of t.vals) {
        const isId = t.name === 'Bool' && vt === 'true' && vf === 'false'
        out.push({ key: `${t.name}:${vt}:${vf}`, type: t.name, vals: t.vals, vt, vf, name: fnName(t.name, vt, vf), isId })
      }
    }
  }
  // id 行放最前
  out.sort((p, q) => (q.isId ? 1 : 0) - (p.isId ? 1 : 0))
  return out
})

const F = ref('List')
const FS = ['List', 'Option', 'Pair']

// 种子 q : F Bool
const seedList = ref(['true', 'false', 'true'])
const seedOpt = ref('true') // 'none' | 'true' | 'false'
const seedPair = ref(['false', 'true'])

const seed = computed(() => {
  if (F.value === 'List') return { k: 'List', v: seedList.value.slice() }
  if (F.value === 'Option') return { k: 'Option', v: seedOpt.value === 'none' ? null : seedOpt.value }
  return { k: 'Pair', v: seedPair.value.slice() }
})

const apply = (row, b) => (b === 'true' ? row.vt : row.vf)

function fmap(row, q) {
  if (q.k === 'List') return { k: 'List', v: q.v.map((b) => apply(row, b)) }
  if (q.k === 'Option') return { k: 'Option', v: q.v === null ? null : apply(row, q.v) }
  return { k: 'Pair', v: q.v.map((b) => apply(row, b)) }
}

function show(val) {
  if (val.k === 'List') return `[${val.v.join(', ')}]`
  if (val.k === 'Option') return val.v === null ? 'none' : `some ${val.v}`
  return `(${val.v[0]}, ${val.v[1]})`
}
const eqv = (p, q) => show(p) === show(q)

function alternatives(row, correct) {
  const xs = row.vals
  const c = []
  if (correct.k === 'List') {
    const v = correct.v
    c.push({ k: 'List', v: v.slice().reverse() })
    c.push({ k: 'List', v: v.slice(1) })
    if (v.length) c.push({ k: 'List', v: v.concat([v[0]]) })
    c.push({ k: 'List', v: [] })
    c.push({ k: 'List', v: [xs[0]] })
  } else if (correct.k === 'Option') {
    c.push({ k: 'Option', v: null })
    for (const x of xs) c.push({ k: 'Option', v: x })
  } else {
    for (const x of xs) for (const y of xs) c.push({ k: 'Pair', v: [x, y] })
  }
  const seen = new Set([show(correct)])
  return c.filter((z) => {
    const s = show(z)
    if (seen.has(s)) return false
    seen.add(s)
    return true
  })
}

const revealed = ref(1)
const tampered = ref({}) // key -> index into alternatives
watch([F, seedList, seedOpt, seedPair], () => {
  tampered.value = {}
}, { deep: true })
watch(F, () => { revealed.value = 1 })

const table = computed(() =>
  rows.value.map((r, i) => {
    const correct = fmap(r, seed.value)
    const alts = alternatives(r, correct)
    const ti = tampered.value[r.key]
    const shown = ti !== undefined && alts.length ? alts[ti % alts.length] : correct
    return { ...r, i, correct, shown, alts, bad: !eqv(shown, correct) }
  }),
)

const broken = computed(() => table.value.filter((r) => r.bad && r.i < revealed.value))

function step() {
  if (revealed.value < rows.value.length) revealed.value++
}
function all() {
  revealed.value = rows.value.length
}
function restart() {
  revealed.value = 1
  tampered.value = {}
}
function tamper(r) {
  if (r.isId || r.i >= revealed.value) return
  if (!r.alts.length) return
  const cur = tampered.value[r.key]
  const next = cur === undefined ? 0 : cur + 1
  const t = { ...tampered.value }
  if (next >= r.alts.length) delete t[r.key]
  else t[r.key] = next
  tampered.value = t
}

function pushList(b) {
  if (seedList.value.length < 5) seedList.value = [...seedList.value, b]
}
function popList() {
  seedList.value = seedList.value.slice(0, -1)
}
function togglePair(i) {
  const p = seedPair.value.slice()
  p[i] = p[i] === 'true' ? 'false' : 'true'
  seedPair.value = p
}

const countFBool = computed(() => (F.value === 'List' ? '无穷多' : F.value === 'Option' ? '3' : '4'))
const lastRow = computed(() => (revealed.value > 1 ? table.value[revealed.value - 1] : null))
</script>

<template>
  <div class="ctfp-widget yt">
    <div class="ctfp-widget-title">米田表格：一个元素长出整个自然变换（a = Bool）</div>
    <p class="hint">
      ① 选一个函子 F，并在 <code>F Bool</code> 中选一个元素 q（这就是 <code>α_Bool(id)</code>）。
      ② 点“下一格”，看自然性如何把 q “运送”到每一个分量 <code>α_x(h)</code>。
      ③ 想捣乱？点击任意已填好的值去篡改它，看看会发生什么。
    </p>

    <div class="row">
      <span class="lbl">函子 F：</span>
      <button v-for="f in FS" :key="f" class="ctfp-btn" :class="{ on: F === f }" @click="F = f">{{ f }}</button>
    </div>

    <div class="row">
      <span class="lbl">种子 q：</span>
      <template v-if="F === 'List'">
        <code class="seed">[{{ seedList.join(', ') }}]</code>
        <button class="ctfp-btn" @click="pushList('true')">追加 true</button>
        <button class="ctfp-btn" @click="pushList('false')">追加 false</button>
        <button class="ctfp-btn" @click="popList">删除末尾</button>
      </template>
      <template v-else-if="F === 'Option'">
        <button v-for="o in ['none', 'true', 'false']" :key="o" class="ctfp-btn" :class="{ on: seedOpt === o }" @click="seedOpt = o">
          {{ o === 'none' ? 'none' : 'some ' + o }}
        </button>
      </template>
      <template v-else>
        <code class="seed">({{ seedPair[0] }}, {{ seedPair[1] }})</code>
        <button class="ctfp-btn" @click="togglePair(0)">翻转 fst</button>
        <button class="ctfp-btn" @click="togglePair(1)">翻转 snd</button>
      </template>
    </div>
    <p class="hint small">
      <code>F Bool</code> 中有 {{ countFBool }} 个元素，于是从 <code>Reader Bool</code> 到 <code>{{ F }}</code> 的自然变换也恰好有 {{ countFBool }} 个——每个种子对应一个。
    </p>

    <div class="row">
      <button class="ctfp-btn" @click="step" :disabled="revealed >= rows.length">下一格 ▶</button>
      <button class="ctfp-btn" @click="all">全部展开</button>
      <button class="ctfp-btn" @click="restart">重来</button>
      <span class="progress">{{ revealed }} / {{ rows.length }}</span>
    </div>

    <div class="tablewrap">
      <table>
        <thead>
          <tr><th>x</th><th>h : Bool → x</th><th>α<sub>x</sub>(h)</th><th>来历</th></tr>
        </thead>
        <tbody>
          <tr
            v-for="r in table"
            :key="r.key"
            :class="{ seedrow: r.isId, hidden: r.i >= revealed, bad: r.bad && r.i < revealed, fresh: lastRow && lastRow.key === r.key }"
          >
            <td><code>{{ r.type }}</code></td>
            <td><code>{{ r.name }}</code></td>
            <td>
              <code v-if="r.i < revealed" class="val" :class="{ clickable: !r.isId && r.alts.length }" @click="tamper(r)">{{ show(r.shown) }}</code>
              <span v-else class="q">?</span>
            </td>
            <td class="why">
              <template v-if="r.i >= revealed">—</template>
              <template v-else-if="r.isId">种子：你选的 q</template>
              <template v-else-if="r.bad">✗ 应为 <code>{{ show(r.correct) }}</code></template>
              <template v-else><code>{{ F === 'List' ? 'List.map' : F === 'Option' ? 'Option.map' : 'Functor.map' }} h q</code></template>
            </td>
          </tr>
        </tbody>
      </table>
    </div>

    <div v-if="broken.length" class="alert">
      <b>自然性被破坏了。</b>取态射 <code>f := {{ broken[0].name }} : Bool → {{ broken[0].type }}</code>，看从 <code>id</code> 出发的自然性方块：
      <br />
      <code>F f (α_Bool id) = F f q = {{ show(broken[0].correct) }}</code>，而 <code>α_{{ broken[0].type }} (f ∘ id) = α_{{ broken[0].type }} f = {{ show(broken[0].shown) }}</code>。
      <br />
      两条路径不相等——这样的一族函数就不再是自然变换了。除了种子，你没有任何自由。
    </div>
    <div v-else-if="revealed >= rows.length" class="ok">
      全部 {{ rows.length }} 个分量都由那一个种子决定。这就是米田引理：<code>Nat(Reader Bool, {{ F }}) ≅ {{ F }} Bool</code>。
    </div>
  </div>
</template>

<style scoped>
.yt { max-width: 100%; }
.row { display: flex; gap: 6px; align-items: center; flex-wrap: wrap; margin: 6px 0; }
.lbl { font-size: 13px; color: var(--vp-c-text-2); min-width: 4.5em; }
.hint { font-size: 13px; color: var(--vp-c-text-2); margin: 6px 0; }
.hint.small { font-size: 12px; }
.seed { font-size: 14px; padding: 2px 8px; }
.progress { font-size: 12px; color: var(--vp-c-text-3); margin-left: 6px; }
.tablewrap { max-width: 100%; overflow-x: auto; margin-top: 8px; }
table { border-collapse: collapse; font-size: 13px; width: 100%; display: table; margin: 0; }
th, td { border: 1px solid var(--vp-c-divider); padding: 2px 8px; text-align: left; }
th { white-space: nowrap; }
td code { white-space: nowrap; font-size: 12px; }
td.why { white-space: nowrap; }
tr.hidden td { color: var(--vp-c-text-3); }
tr.seedrow { background: var(--vp-c-brand-soft); }
tr.fresh td { animation: flash 0.8s ease; }
tr.bad { background: var(--vp-c-danger-soft, rgba(244, 63, 94, 0.14)); }
@keyframes flash { from { background: var(--vp-c-yellow-soft, rgba(234, 179, 8, 0.3)); } to { background: transparent; } }
.val.clickable { cursor: pointer; border-bottom: 1px dashed var(--vp-c-brand-1); }
.q { color: var(--vp-c-text-3); }
.why { font-size: 12px; color: var(--vp-c-text-2); }
.alert { margin-top: 10px; padding: 8px 12px; border-radius: 8px; background: var(--vp-c-danger-soft, rgba(244, 63, 94, 0.14)); font-size: 13px; line-height: 1.8; }
.ok { margin-top: 10px; padding: 8px 12px; border-radius: 8px; background: var(--vp-c-green-soft, rgba(16, 185, 129, 0.14)); font-size: 13px; }
button:disabled { opacity: 0.5; cursor: default; }
</style>
