<script setup>
import { ref, onMounted, onBeforeUnmount, watch } from 'vue'

const query = ref('')
const shown = ref(0)
const total = ref(0)
const root = ref(null)
let rows = []

function collect() {
  const doc = root.value?.closest('.vp-doc')
  if (!doc) return
  rows = Array.from(doc.querySelectorAll('table tbody tr')).map((tr) => ({
    tr,
    table: tr.closest('table'),
    text: tr.textContent.toLowerCase(),
  }))
  total.value = rows.length
}

function apply() {
  const q = query.value.trim().toLowerCase()
  const words = q.split(/\s+/).filter(Boolean)
  let n = 0
  const visibleTables = new Map()
  for (const r of rows) {
    const hit = words.every((w) => r.text.includes(w))
    r.tr.style.display = hit ? '' : 'none'
    if (hit) n++
    visibleTables.set(r.table, (visibleTables.get(r.table) || 0) + (hit ? 1 : 0))
  }
  for (const [table, count] of visibleTables) {
    table.style.display = count ? '' : 'none'
    let h = table.previousElementSibling
    while (h && !/^H[23]$/.test(h.tagName)) h = h.previousElementSibling
    if (h && !q) h.style.opacity = ''
    else if (h) h.style.opacity = count ? '' : '0.35'
  }
  shown.value = n
}

watch(query, apply)
onMounted(() => {
  collect()
  apply()
})
onBeforeUnmount(() => {
  query.value = ''
  apply()
})
</script>

<template>
  <div ref="root" class="ctfp-widget gf">
    <div class="ctfp-widget-title">在本页的表格中筛选</div>
    <div class="bar">
      <input v-model="query" type="search" placeholder="输入中文、英文或符号，例如：伴随、functor、⊗" aria-label="筛选术语" />
      <button v-if="query" class="ctfp-btn" @click="query = ''">清除</button>
    </div>
    <div class="info">{{ query ? `匹配 ${shown} / ${total} 条` : `共 ${total} 条；多个关键词用空格分隔，同时匹配` }}</div>
  </div>
</template>

<style scoped>
.bar {
  display: flex;
  gap: 8px;
  align-items: center;
}
input {
  flex: 1;
  min-width: 0;
  font-size: 14px;
  padding: 7px 12px;
  border-radius: 8px;
  border: 1px solid var(--vp-c-divider);
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  outline: none;
  transition: border-color 0.2s;
}
input:focus {
  border-color: var(--vp-c-brand-1);
}
.info {
  margin-top: 6px;
  font-size: 12px;
  color: var(--vp-c-text-3);
}
</style>
