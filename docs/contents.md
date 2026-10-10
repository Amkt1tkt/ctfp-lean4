<script setup>
import { parts } from './.vitepress/chapters.mjs'
import { withBase } from 'vitepress'
</script>

# 目录

如果你对 Lean 4 还不熟，先读 **0.1 Lean 4 速成**；如果你担心自己的数学基础，**0.2 数学工具箱**会把全书用到的数学从头讲一遍。
之后按顺序阅读即可：第一部分建立基本词汇，第二部分讲泛构造与米田引理，第三部分是伴随、单子以及更高的抽象。

<div v-for="p in parts" :key="p.text" class="toc-part">
  <h2>{{ p.text }}</h2>
  <ul>
    <li v-for="c in p.items" :key="c.link">
      <span class="toc-num">{{ c.num }}</span>
      <a :href="withBase(c.link)">{{ c.title }}</a>
    </li>
  </ul>
</div>

<style scoped>
.toc-part ul { list-style: none; padding-left: 0; }
.toc-num { display: inline-block; width: 3em; color: var(--vp-c-text-3); font-variant-numeric: tabular-nums; }
</style>
