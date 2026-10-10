# 3.11 Kan 扩张

到目前为止，我们大多只和一个范畴、或者一对范畴打交道。有时候，这显得有点束手束脚。

比如，在范畴 $\mathcal{C}$ 中定义极限时，我们引入了一个索引范畴 $\mathcal{I}$，作为构成锥底的那个“图样”的模板。照理说，我们也该再引入一个范畴——一个平凡的范畴——作为锥顶点的模板。可我们当时没这么做，而是用了从 $\mathcal{I}$ 到 $\mathcal{C}$ 的常函子 $\Delta_c$。

是时候修正这种别扭了。我们用**三个**范畴来定义极限。先从索引范畴 $\mathcal{I}$ 到 $\mathcal{C}$ 的函子 $D$ 开始。这个函子负责挑出锥的底——它就是图函子（diagram functor）。

![三个范畴（原书手绘）](/img/3.11/kan2.jpg "三个范畴：索引范畴 I、单点范畴 1、目标范畴 C，以及它们之间的函子 K、D、F。")

新加入的是范畴 $\mathbf{1}$：它只有一个对象（以及一个恒等态射）。从 $\mathcal{I}$ 到这个范畴的函子 $K$ 只有一个可能：把所有对象映到 $\mathbf{1}$ 中唯一的那个对象，把所有态射映到恒等态射。而任何从 $\mathbf{1}$ 到 $\mathcal{C}$ 的函子 $F$，都挑出了锥的一个候选顶点。

![F 挑出一个顶点（原书手绘）](/img/3.11/kan15.jpg "函子 F 把 1 中唯一的对象映成 C 中的一个顶点（apex）；ε 的各分量是从顶点出发的锥的侧边。")

```lean hidden
namespace Ch311

universe u v

structure Iso (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

infix:25 " ≅ " => Iso
```

一个锥，就是一个从 $F \circ K$ 到 $D$ 的自然变换 $\varepsilon$。注意，$F \circ K$ 做的事情和原来的 $\Delta_c$ 一模一样：先把 $\mathcal{I}$ 的一切压扁到 $\mathbf{1}$，再由 $F$ 送到顶点。下图展示了这个变换：

![锥作为自然变换（原书手绘）](/img/3.11/kan3-e1492120491591.jpg "锥就是自然变换 ε : F ∘ K ⇒ D。")

```diagram
I: (0, 0) "\mathcal{I}"
one: (1.6, 0) "\mathbf{1}"
C: (3.2, 0) "\mathcal{C}"
K: I -> one "K"
F: one -> C "F"
D: I -> C "" bend=-85
Dlab: (1.6, 0.97) "D"
eps: (1.6, 0.32) "\varepsilon \Downarrow"
caption: 锥 = 自然变换 ε : F ∘ K ⇒ D。上面一条路是 F ∘ K，下面一条是 D，双箭头 ε 从上指向下。
```

现在可以定义一个泛性质，来挑出这种 $F$ 中“最好”的那一个。这个 $F$ 会把 $\mathbf{1}$ 映到 $\mathcal{C}$ 中 $D$ 的极限，而从 $F \circ K$ 到 $D$ 的自然变换 $\varepsilon$ 会提供相应的投影。这个泛函子叫作 $D$ **沿** $K$ 的**右 Kan 扩张**（right Kan extension），记作 $\mathrm{Ran}_K D$。

我们来表述这个泛性质。假设有另一个锥——也就是另一个函子 $F'$，连同一个从 $F' \circ K$ 到 $D$ 的自然变换 $\varepsilon'$：

![另一个锥（原书手绘）](/img/3.11/kan31-e1492120512209.jpg "另一个候选：F′ 连同 ε′ : F′ ∘ K ⇒ D。")

如果 Kan 扩张 $F = \mathrm{Ran}_K D$ 存在，那么必定有唯一的自然变换 $\sigma$ 从 $F'$ 指向它，使得 $\varepsilon'$ 经由 $\varepsilon$ 分解，即：

$$\varepsilon' = \varepsilon \cdot (\sigma \circ K)$$

这里 $\sigma \circ K$ 是两个自然变换的**水平复合**（其中一个是 $K$ 上的恒等自然变换），然后再与 $\varepsilon$ 做**垂直复合**。

![分解（原书手绘）](/img/3.11/kan5.jpg "σ : F′ ⇒ F 先“横着”贴上 K，再与 ε 竖着叠起来，就得到 ε′。")

::: info 数学小课堂：水平复合与垂直复合（回顾）
自然变换有两种复合方式（见 [1.10 自然变换](/part1/10-natural-transformations)）：

- **垂直复合** $\beta \cdot \alpha$：$\alpha : F \Rightarrow G$、$\beta : G \Rightarrow H$，得到 $F \Rightarrow H$，分量是 $(\beta \cdot \alpha)_x = \beta_x \circ \alpha_x$。在 Lean 里就是逐点复合 `fun x => β x ∘ α x`。
- **水平复合**的一个特例 $\sigma \circ K$（也叫“胡须”，whiskering）：$\sigma : F' \Rightarrow F$ 是 $\mathcal{A} \to \mathcal{C}$ 之间的变换，$K : \mathcal{I} \to \mathcal{A}$ 是函子，那么 $\sigma \circ K : F' \circ K \Rightarrow F \circ K$ 的分量就是 $(\sigma \circ K)_i = \sigma_{K i}$——只在 $K$ 的像上取 $\sigma$ 的分量。
:::

逐个分量来看，作用在 $\mathcal{I}$ 中的对象 $i$ 上，我们得到：

$$\varepsilon'_i = \varepsilon_i \circ \sigma_{K i}$$

```diagram
FpKi: (0, 0) "F'(K\,i)"
FKi: (2.2, 0) "F(K\,i)"
Di: (1.1, 1.4) "D\,i"
s: FpKi -> FKi "\sigma_{K i}"
e: FKi -> Di "\varepsilon_i"
ep: FpKi -> Di "\varepsilon'_i" side=right
path "直接走 ε′ᵢ": ep
path "先 σ 再 εᵢ": s e color=green
caption: 分解条件的分量形式：在 C 中，这是一个交换三角形。
```

在我们的情形中，$\sigma$ 只有一个分量，对应 $\mathbf{1}$ 中唯一的对象。所以它确实就是从 $F'$ 定义的锥的顶点、到 $\mathrm{Ran}_K D$ 定义的泛锥的顶点的那个唯一态射。上面的交换条件，正是极限定义所要求的那些。

但重要的是，我们完全可以把平凡范畴 $\mathbf{1}$ 换成任意范畴 $\mathcal{A}$，右 Kan 扩张的定义依然成立。

## 右 Kan 扩张

**先看它在程序里长什么样。** 在 $\mathcal{A} = \mathcal{C} = \mathbf{Set}$（在 Lean 中就是 `Type`）的情形，右 Kan 扩张有一个非常具体的样子（本章后面会推导出来）：

```lean no-check
Ran k d a = ∀ i, (a → k i) → d i     -- 伪代码
```

“给我一个把 `a` 变成 `k i` 的方法，不管 `i` 是什么，我都能给你一个 `d i`。”记住这个形状，然后我们来看抽象的定义。

**再看定义。** 函子 $D : \mathcal{I} \to \mathcal{C}$ 沿函子 $K : \mathcal{I} \to \mathcal{A}$ 的右 Kan 扩张，是一个函子 $F : \mathcal{A} \to \mathcal{C}$（记作 $\mathrm{Ran}_K D$），连同一个自然变换

$$\varepsilon : F \circ K \to D$$

使得对任何其他函子 $F' : \mathcal{A} \to \mathcal{C}$ 和自然变换

$$\varepsilon' : F' \circ K \to D$$

都存在唯一的自然变换

$$\sigma : F' \to F$$

把 $\varepsilon'$ 分解为：

$$\varepsilon' = \varepsilon \cdot (\sigma \circ K)$$

这一大口话确实不好消化，不过可以画成下面这张漂亮的图：

![右 Kan 扩张（原书手绘）](/img/3.11/kan7.jpg "右 Kan 扩张：F = Ran_K D 是所有“F′ ∘ K ⇒ D”中最好的那个，任何 F′ 都经由唯一的 σ 分解到它。")

```diagram
A: (0, 0) "\mathcal{A}"
I: (0, 1.7) "\mathcal{I}"
C: (2.3, 1.7) "\mathcal{C}"
K: I -> A "K"
D: I -> C "D" side=right
F: A -> C "F" side=right
Fp: A -> C "F'" bend=60
sig: (1.3, 0.63) "\sigma \Downarrow"
eps: (0.75, 1.35) "\varepsilon \Downarrow"
caption: 外侧的弧是 F′，对角线是 F = Ran_K D。σ : F′ ⇒ F，ε : F ∘ K ⇒ D。
```

一个有趣的看法是：在某种意义上，Kan 扩张就像是“函子乘法”的逆运算。有些作者甚至直接把 $\mathrm{Ran}_K D$ 记作 $D/K$。确实，用这种记号，$\varepsilon$ 的定义——它也被叫作右 Kan 扩张的**余单位**（counit）——看起来就像简单的约分：

$$\varepsilon : D/K \circ K \to D$$

Kan 扩张还有另一种解释。设想函子 $K$ 把范畴 $\mathcal{I}$ **嵌入**到 $\mathcal{A}$ 里。最简单的情形下，$\mathcal{I}$ 就是 $\mathcal{A}$ 的一个子范畴。我们有一个把 $\mathcal{I}$ 映到 $\mathcal{C}$ 的函子 $D$。能不能把 $D$ **延拓**成一个定义在整个 $\mathcal{A}$ 上的函子 $F$？理想情况下，这样的延拓会使复合 $F \circ K$ 同构于 $D$。换句话说，$F$ 会把 $D$ 的定义域扩展到 $\mathcal{A}$。但完整的同构通常是奢求，我们只要一半就行：一个单向的自然变换 $\varepsilon$，从 $F \circ K$ 指向 $D$。（左 Kan 扩张选的是另一个方向。）

![把 D 延拓到整个 A（原书手绘）](/img/3.11/kan6.jpg "K 把 I 嵌进 A，D 把 I 映进 C；我们想找一个定义在整个 A 上的 F（虚线），让它在 I 的像上“尽量像” D。")

当然，如果函子 $K$ 在对象上不是单射、或者在 hom-集上不是忠实的（比如上面极限的例子：所有对象都被压到了一个点），这种“嵌入”的图景就不成立了。这时，Kan 扩张会尽力外推那些丢失的信息。

::: info 数学小课堂：子范畴、单射与“忠实”
- **子范畴**：从一个范畴里挑出一部分对象和一部分态射，只要挑出来的东西对恒等和复合封闭，它本身就是一个范畴。
- 函子在对象上是**单射**，意思是不同的对象被送到不同的对象（不会“撞车”）。
- 函子是**忠实的**（faithful），意思是在每个 hom-集上都是单射：两个不同的态射 $f \neq g : a \to b$ 不会被送成同一个态射。

满足这两条，$K$ 就像是一个“嵌入”：$\mathcal{I}$ 原封不动地出现在 $\mathcal{A}$ 里。若 $K$ 还是**满的**（full，每个 $K a \to K b$ 都来自某个 $a \to b$），那么 Kan 扩张在 $\mathcal{I}$ 的像上会与 $D$ 完全吻合——下面偏序的例子里你会亲眼看到这一点。
:::

## Kan 扩张作为伴随

现在假设对任意 $D$（以及一个固定的 $K$），右 Kan 扩张都存在。这时 $\mathrm{Ran}_K -$（用短横代替 $D$）就是一个从函子范畴 $[\mathcal{I}, \mathcal{C}]$ 到函子范畴 $[\mathcal{A}, \mathcal{C}]$ 的函子。事实证明，这个函子是**预复合函子** $- \circ K$ 的**右伴随**。后者把 $[\mathcal{A}, \mathcal{C}]$ 中的函子映到 $[\mathcal{I}, \mathcal{C}]$ 中的函子。伴随关系是：

$$[\mathcal{I}, \mathcal{C}](F' \circ K, D) \cong [\mathcal{A}, \mathcal{C}](F', \mathrm{Ran}_K D)$$

这不过是换个说法重述了这件事：每一个我们称为 $\varepsilon'$ 的自然变换，都唯一对应着一个我们称为 $\sigma$ 的自然变换。

![Kan 扩张作为伴随（原书手绘）](/img/3.11/kan92.jpg "左边是函子范畴 [I, C]，右边是 [A, C]。从 F′ ∘ K 到 D 的箭头，与从 F′ 到 Ran_K D 的箭头一一对应。")

（我们会在本章的 Lean 部分把这个伴随——在 `Type` 上——**真的证明出来**。）

进一步，如果把范畴 $\mathcal{I}$ 选成与 $\mathcal{C}$ 相同，我们可以把恒等函子 $I_{\mathcal{C}}$ 代入 $D$。得到如下恒等式：

$$[\mathcal{C}, \mathcal{C}](F' \circ K, I_{\mathcal{C}}) \cong [\mathcal{A}, \mathcal{C}](F', \mathrm{Ran}_K I_{\mathcal{C}})$$

现在可以把 $F'$ 选成 $\mathrm{Ran}_K I_{\mathcal{C}}$ 本身。这时右边包含恒等自然变换，与之对应，左边给出如下自然变换：

$$\varepsilon : \mathrm{Ran}_K I_{\mathcal{C}} \circ K \to I_{\mathcal{C}}$$

这看起来非常像一个伴随的余单位：

$$\mathrm{Ran}_K I_{\mathcal{C}} \dashv K$$

的确，恒等函子沿函子 $K$ 的右 Kan 扩张，可以用来计算 $K$ 的**左伴随**。为此还需要一个条件：右 Kan 扩张必须被函子 $K$ **保持**。“保持扩张”的意思是：如果我们计算“预复合了 $K$ 的那个函子”的 Kan 扩张，结果应该和“先算原来的 Kan 扩张、再预复合 $K$”相同。在我们的情形，这个条件化简为：

$$K \circ \mathrm{Ran}_K I_{\mathcal{C}} \cong \mathrm{Ran}_K K$$

注意，用“除以 $K$”的记号，这个伴随可以写成：

$$I/K \dashv K$$

这印证了我们的直觉：伴随描述的是某种意义上的“逆”。保持条件变成：

$$K \circ I/K \cong K/K$$

函子沿其自身的右 Kan 扩张 $K/K$，叫作**余密度单子**（codensity monad）。我们会在 Lean 里给它写出 `Monad` 实例。

这个伴随公式之所以重要，是因为——我们很快就会看到——可以用端（余端）来计算 Kan 扩张，从而为我们提供了寻找右（以及左）伴随的实用手段。

## 左 Kan 扩张

**先看它在程序里长什么样。** 在 `Type` 上，左 Kan 扩张是一个存在类型：

```lean no-check
Lan k d a = Σ i, (k i → a) × d i     -- 伪代码
```

“我手里有某个（你不知道是什么的）`i`：一个装着 `i` 的 `d i`，外加一个能把 `k i` 变成 `a` 的函数。”

**再看定义。** 有一个对偶的构造给出左 Kan 扩张。为了建立直觉，我们从余极限的定义出发，把它改写成用单点范畴 $\mathbf{1}$ 的形式。我们用函子 $D : \mathcal{I} \to \mathcal{C}$ 构成余锥的底，用函子 $F : \mathbf{1} \to \mathcal{C}$ 挑出它的顶点：

![余锥（原书手绘）](/img/3.11/kan81.jpg "余锥：D 给出底，F 挑出顶点。")

余锥的侧边——那些内射——是从 $D$ 到 $F \circ K$ 的自然变换 $\eta$ 的各个分量：

![余锥作为自然变换（原书手绘）](/img/3.11/kan10a.jpg "余锥就是自然变换 η : D ⇒ F ∘ K（注意方向和锥相反）。")

余极限是泛余锥。所以对任何其他函子 $F'$ 和自然变换

$$\eta' : D \to F' \circ K$$

![另一个余锥（原书手绘）](/img/3.11/kan10b.jpg "另一个候选：F′ 连同 η′ : D ⇒ F′ ∘ K。")

都存在唯一的自然变换 $\sigma$，从 $F$ 指向 $F'$：

![σ 从 F 指向 F′（原书手绘）](/img/3.11/kan14.jpg "这一次 σ 的方向是从泛对象 F 指向候选者 F′。")

使得：

$$\eta' = (\sigma \circ K) \cdot \eta$$

下图描绘了这一点：

![左分解（原书手绘）](/img/3.11/kan112.jpg "η′ 等于先走 η、再走 σ ∘ K。")

```diagram
Di: (1.1, 0) "D\,i"
FKi: (0, 1.4) "F(K\,i)"
FpKi: (2.2, 1.4) "F'(K\,i)"
e: Di -> FKi "\eta_i" side=right
s: FKi -> FpKi "\sigma_{K i}" side=right
ep: Di -> FpKi "\eta'_i"
path "直接走 η′ᵢ": ep
path "先 ηᵢ 再 σ": e s color=green
caption: 左 Kan 扩张分解条件的分量形式：η′ᵢ = σ_{K i} ∘ ηᵢ。
```

把单点范畴 $\mathbf{1}$ 换成 $\mathcal{A}$，这个定义就自然推广成了**左 Kan 扩张**（left Kan extension）的定义，记作 $\mathrm{Lan}_K D$：

![左 Kan 扩张（原书手绘）](/img/3.11/kan12.jpg "左 Kan 扩张：F = Lan_K D，任何候选 F′ 都通过唯一的 σ : F ⇒ F′ 从它分解出来。")

自然变换

$$\eta : D \to \mathrm{Lan}_K D \circ K$$

叫作左 Kan 扩张的**单位**（unit）。

和以前一样，我们可以把自然变换之间的一一对应

$$\eta' = (\sigma \circ K) \cdot \eta$$

改写成伴随：

$$[\mathcal{A}, \mathcal{C}](\mathrm{Lan}_K D, F') \cong [\mathcal{I}, \mathcal{C}](D, F' \circ K)$$

换句话说，左 Kan 扩张是预复合 $K$ 的**左伴随**，右 Kan 扩张是它的**右伴随**。

就像恒等函子的右 Kan 扩张可以用来计算 $K$ 的左伴随一样，恒等函子的左 Kan 扩张原来就是 $K$ 的右伴随（$\eta$ 是这个伴随的单位）：

$$K \dashv \mathrm{Lan}_K I_{\mathcal{C}}$$

把两个结果合起来，我们得到：

$$\mathrm{Ran}_K I_{\mathcal{C}} \dashv K \dashv \mathrm{Lan}_K I_{\mathcal{C}}$$

## 补充：Kan 扩张作为“最好的近似”

上面的定义很抽象。为了真正“看见” Kan 扩张，我们找一个最简单、却又不平凡的例子：**偏序**。

::: info 数学小课堂：偏序作为范畴
回忆 [1.3 大大小小的范畴](/part1/03-categories-great-and-small)：任何偏序（比如数的 $\le$）都是一个范畴——对象是元素，从 $x$ 到 $y$ 有（唯一一个）态射当且仅当 $x \le y$。在这样的“瘦范畴”里：

- **函子**就是**单调函数**：$x \le y$ 推出 $F x \le F y$（把箭头送到箭头）。
- **自然变换** $F \Rightarrow G$ 存在，当且仅当处处有 $F x \le G x$（每个分量都是一个 $\le$ 箭头，自然性方块自动交换，因为任意两个箭头只要端点相同就相等）。
- **极限**是下确界（最大下界，$\min$/$\inf$），**余极限**是上确界（最小上界，$\max$/$\sup$）。
:::

取 $\mathcal{A}$ 为一串排好队的对象 $a_0 \le a_1 \le \cdots \le a_7$，$\mathcal{I}$ 为其中的几个，$K$ 为包含映射；取 $\mathcal{C}$ 为 $\{\bot < 0 < 1 < \cdots < 8 < \top\}$。$D$ 是 $\mathcal{I}$ 上的一个单调函数。把定义翻译成偏序的语言：

- 右候选 $F'$：一个单调函数，满足在 $\mathcal{I}$ 上 $F'(i) \le D(i)$（这就是 $\varepsilon' : F' \circ K \Rightarrow D$）。
- $\mathrm{Ran}_K D$ 是**最大的**右候选：任何右候选都满足处处 $F' \le \mathrm{Ran}_K D$（这就是 $\sigma : F' \Rightarrow \mathrm{Ran}_K D$）。
- 用后面的端公式算出来：$\mathrm{Ran}_K D(a) = \min\{ D(i) \mid a \le K i \}$——往“右上方”看，取所有从 $a$ 能到达的 $K i$ 上 $D$ 的最小值。
- 对偶地，$\mathrm{Lan}_K D(a) = \max\{ D(i) \mid K i \le a \}$ 是**最小的**左候选。

下面的小工具让你随意选择 $\mathcal{I}$、设置 $D$，并亲手构造候选 $F'$，检验泛性质：

<div class="ch-widget-slot">
<Ch3_11KanPoset />
</div>

你会注意到几件事：

1. 两种扩张在 $\mathcal{I}$ 上都和 $D$ 重合（因为这里的 $K$ 是满忠实的嵌入）。
2. 在 $\mathcal{I}$ 之外，$\mathrm{Ran}$ 是“乐观的最大延拓”（取后面能到的最小值），$\mathrm{Lan}$ 是“保守的最小延拓”（取前面已有的最大值），并且处处 $\mathrm{Lan} \le \mathrm{Ran}$。
3. 把 $\mathcal{I}$ 清空：$\mathrm{Ran}$ 变成常值 $\top$（空集的下确界），$\mathrm{Lan}$ 变成常值 $\bot$——没有任何信息时，“最好的近似”只能是两个极端。
4. 只保留一个对象在 $\mathcal{I}$ 中，并把 $\mathcal{A}$ 看成只有它自己：这就退化回了本章开头的“极限 = 沿 $K : \mathcal{I} \to \mathbf{1}$ 的右 Kan 扩张”。

## Kan 扩张作为端

Kan 扩张真正的威力，来自于它们可以用端（以及余端）来**计算**。为简单起见，我们只考虑目标范畴 $\mathcal{C}$ 是 $\mathbf{Set}$ 的情形，不过这些公式可以推广到任意范畴。

让我们重新审视“Kan 扩张可以把函子的作用延拓到原定义域之外”这个想法。假设 $K$ 把 $\mathcal{I}$ 嵌入 $\mathcal{A}$，函子 $D$ 把 $\mathcal{I}$ 映到 $\mathbf{Set}$。对 $K$ 像中的任何对象 $a$，也就是 $a = K i$，我们可以干脆说：延拓后的函子把 $a$ 映到 $D i$。问题在于，$\mathcal{A}$ 中那些在 $K$ 的像**之外**的对象该怎么办？思路是这样的：每一个这样的对象，都可能通过大量态射连到 $K$ 像中的每一个对象。函子必须保持这些态射。从对象 $a$ 到 $K$ 的像的全部态射，由 hom-函子刻画：

$$\mathcal{A}(a, K -)$$

![从 a 出发的所有箭头（原书手绘）](/img/3.11/kan13.jpg "对象 a′ 在 K 的像之外，但它有许多箭头指向像中的对象 a = K i；延拓后的 F 必须照顾到这些箭头。")

注意，这个 hom-函子是两个函子的复合：

$$\mathcal{A}(a, K -) = \mathcal{A}(a, -) \circ K$$

右 Kan 扩张是函子复合的右伴随：

$$[\mathcal{I}, \mathbf{Set}](F' \circ K, D) \cong [\mathcal{A}, \mathbf{Set}](F', \mathrm{Ran}_K D)$$

我们看看把 $F'$ 换成 hom-函子会发生什么：

$$[\mathcal{I}, \mathbf{Set}](\mathcal{A}(a, -) \circ K, D) \cong [\mathcal{A}, \mathbf{Set}](\mathcal{A}(a, -), \mathrm{Ran}_K D)$$

然后把复合展开：

$$[\mathcal{I}, \mathbf{Set}](\mathcal{A}(a, K -), D) \cong [\mathcal{A}, \mathbf{Set}](\mathcal{A}(a, -), \mathrm{Ran}_K D)$$

右边可以用米田引理化简：

$$[\mathcal{I}, \mathbf{Set}](\mathcal{A}(a, K -), D) \cong \mathrm{Ran}_K D\ a$$

现在把自然变换的集合改写成端（上一章刚学过：$\mathrm{Nat}(F, G) = \int_c \mathcal{C}(F c, G c)$），就得到右 Kan 扩张的这个非常方便的公式：

$$\mathrm{Ran}_K D\ a \cong \int_i \mathbf{Set}(\mathcal{A}(a, K i), D i)$$

左 Kan 扩张有一个类似的、用余端表示的公式：

$$\mathrm{Lan}_K D\ a = \int^i \mathcal{A}(K i, a) \times D i$$

为了说明确实如此，我们来证明它就是函子复合的左伴随：

$$[\mathcal{A}, \mathbf{Set}](\mathrm{Lan}_K D, F') \cong [\mathcal{I}, \mathbf{Set}](D, F' \circ K)$$

把公式代入左边：

$$[\mathcal{A}, \mathbf{Set}]\Big(\int^i \mathcal{A}(K i, -) \times D i,\ F'\Big)$$

这是一个自然变换的集合，所以可以改写成端：

$$\int_a \mathbf{Set}\Big(\int^i \mathcal{A}(K i, a) \times D i,\ F' a\Big)$$

利用 hom-函子的连续性，可以把余端换成端：

$$\int_a \int_i \mathbf{Set}\big(\mathcal{A}(K i, a) \times D i,\ F' a\big)$$

可以用积与指数的伴随（柯里化）：

$$\int_a \int_i \mathbf{Set}\big(\mathcal{A}(K i, a),\ (F' a)^{D i}\big)$$

指数对象同构于相应的 hom-集：

$$\int_a \int_i \mathbf{Set}\big(\mathcal{A}(K i, a),\ \mathbf{Set}(D i, F' a)\big)$$

有一个叫作 **Fubini 定理**的定理，允许我们交换两个端：

$$\int_i \int_a \mathbf{Set}\big(\mathcal{A}(K i, a),\ \mathbf{Set}(D i, F' a)\big)$$

内层的端表示两个函子之间的自然变换的集合，所以可以用米田引理：

$$\int_i \mathbf{Set}\big(D i,\ F' (K i)\big)$$

这确实就是构成我们要证明的伴随右边的那个自然变换集合：

$$[\mathcal{I}, \mathbf{Set}](D, F' \circ K)$$

这类用端、余端和米田引理进行的计算，是端的“微积分”的典型套路。

::: info 数学小课堂：Fubini 定理
在普通微积分里，Fubini 定理说的是（在适当条件下）二重积分可以交换积分次序：$\int_x \int_y f(x, y) = \int_y \int_x f(x, y)$。端的 Fubini 定理是同一个意思：$\int_a \int_i$ 与 $\int_i \int_a$ 给出同构的结果——两者都等于对一对变量 $\langle a, i \rangle$ 一起取的端。用编程的话说：`∀ a, ∀ i, P a i` 和 `∀ i, ∀ a, P a i` 是一回事，只是参数顺序不同。
:::

## Lean 中的 Kan 扩张

Kan 扩张的端/余端公式，可以很容易地翻译成代码。先从右扩张开始：

$$\mathrm{Ran}_K D\ a \cong \int_i \mathbf{Set}(\mathcal{A}(a, K i), D i)$$

把端换成全称量词（依值函数类型），把 hom-集换成函数类型：

```lean
/-- 右 Kan 扩张：Ran k d a = ∀ i, (a → k i) → d i -/
def Ran (k d : Type → Type) (a : Type) : Type 1 :=
  (i : Type) → (a → k i) → d i
```

::: tip Lean 深入：为什么是 `Type 1`？
和上一章的端一样，`Ran k d a` 对**所有**类型 `i : Type` 量化，所以它比任何单个类型都“大”，住在 `Type 1`。于是 `Ran k d` 的类型是 `Type → Type 1`：输入一个普通类型，输出一个“大”类型。

好在 Lean 的 `Functor` 类型类本来就允许这种情况：它的签名是 `class Functor (f : Type u → Type v)`，输入和输出可以住在不同的宇宙。所以我们照样可以为 `Ran k d` 写 `Functor` 实例。代价是：`Ran k d a` 不能再作为 `k` 或 `d` 的参数（它们只接受 `Type`）——比如 `Ran k d (Ran k d a)` 是写不出来的。Haskell 的类型系统是“非直谓的”（impredicative），没有这个限制，但代价是在 Haskell 里你无法把类型系统当作一致的逻辑来证明定理。
:::

`Ran k d` 是一个函子：给一个 `g : a → b`，要把 `Ran k d a` 变成 `Ran k d b`。新的值收到一个 `h : b → k i`，只要先用 `g` 把它“预处理”成 `h ∘ g : a → k i`，交给旧值即可。函子定律在定义上就成立：

```lean
instance : Functor (Ran k d) where
  map g r := fun i h => r i (h ∘ g)

instance : LawfulFunctor (Ran k d) where
  map_const := rfl
  id_map _ := rfl          -- r i (h ∘ id) 就是 r i h
  comp_map _ _ _ := rfl    -- 函数复合的结合律
```

::: tip Lean 深入：`LawfulFunctor` 的三个字段
`LawfulFunctor` 要求三条：`map_const`（`mapConst` 与 `map ∘ const` 一致——我们没自定义 `mapConst`，用的是默认实现，所以是 `rfl`）、`id_map`（`map id x = x`）、`comp_map`（`map (h ∘ g) x = map h (map g x)`）。对 `Ran` 来说，`map` 只是在“输入端”做预复合，所以三条都是 `rfl`。
:::

看着这个定义，可以发现 `Ran` 必须“持有”一个类型为 `a` 的值（好让函数作用在它上面），以及两个函子 `k` 和 `d` 之间的一个自然变换。比如，设 `k` 是树函子，`d` 是列表函子，你拿到了一个 `Ran Tree List String`。如果你给它传一个函数

```lean no-check
f : String → Tree Nat
```

你就会得到一个 `Nat` 的列表，以此类推。右 Kan 扩张会用你的函数生成一棵树，再把它重新打包成一个列表。比如，你可以给它传一个解析器，从字符串生成一棵语法树，然后你会得到对应于这棵树深度优先遍历的列表：

```lean
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

/-- 深度优先遍历：树 ⟹ 列表 的自然变换 -/
def Tree.toList : Tree α → List α
  | .leaf a => [a]
  | .node l r => l.toList ++ r.toList

/-- 一个 Ran Tree List String：它“持有”字符串 "hello world" 和自然变换 Tree.toList。 -/
def demoRan : Ran Tree List String :=
  fun _ h => (h "hello world").toList

/-- 一个玩具“解析器”：把每个单词的长度放进树叶。 -/
def parse (s : String) : Tree Nat :=
  match (s.splitOn " ").map String.length with
  | [] => .leaf 0
  | n :: ns => ns.foldl (fun t m => .node t (.leaf m)) (.leaf n)

#guard demoRan Nat parse == [5, 5]
```

::: tip Rust 视角：秩-2 多态
`Ran` 的值是一个“对**所有** `i` 都能用”的函数。在 Rust 里，闭包不能是泛型的（`|h: impl Fn(&A) -> Vec<I>|` 这种对 `I` 多态的闭包写不出来），要表达“调用方选 `I`”，得用一个**带泛型方法的 trait**——这在类型论里叫秩-2 多态：

```rust
/// Ran Vec Option A ≈ ∀ I. (A → Vec<I>) → Option<I>
pub trait RanVecOpt<A> {
    fn run<I>(&self, h: impl Fn(&A) -> Vec<I>) -> Option<I>;
}

/// 持有一个 A，并“取第一个元素”（一个 Vec ⟹ Option 的自然变换）
pub struct FirstOf<A>(pub A);

impl<A> RanVecOpt<A> for FirstOf<A> {
    fn run<I>(&self, h: impl Fn(&A) -> Vec<I>) -> Option<I> {
        h(&self.0).into_iter().next()
    }
}
```

调用方每次调用 `run` 都可以选一个不同的 `I`——这正是 `∀ i` 的含义。
:::

### 用右 Kan 扩张计算左伴随

把函子 `d` 换成恒等函子，右 Kan 扩张就可以用来计算给定函子的左伴随。这样一来，函子 `k` 的左伴随就由如下类型的多态函数组成：

```lean no-check
∀ i, (a → k i) → i      -- 伪代码：Ran k Id a
```

假设 `k` 是从幺半群范畴出发的遗忘函子。那么全称量词就跑遍所有幺半群。当然，在 Haskell 里我们没法表达幺半群定律，不过下面这个类型是对所得自由函子的一个不错的近似（遗忘函子 `k` 在对象上是恒等的）。在 Lean 里，我们用一个“带幺半群结构的类型”作为量化范围——`[MyMonoid i]` 是一个**实例隐式参数**：

```lean
class MyMonoid (m : Type) where
  one : m
  mul : m → m → m

instance : MyMonoid (List α) := ⟨[], (· ++ ·)⟩

/-- Lst a = ∀ 幺半群 i, (a → i) → i -/
def Lst (a : Type) : Type 1 := (i : Type) → [MyMonoid i] → (a → i) → i
```

不出所料，它生成的是自由幺半群，也就是列表：

```lean
def foldMap [MyMonoid i] (f : a → i) : List a → i
  | [] => MyMonoid.one
  | x :: xs => MyMonoid.mul (f x) (foldMap f xs)

def toLst (as : List a) : Lst a := fun _ _ f => foldMap f as

def fromLst (l : Lst a) : List a := l (List a) (fun x => [x])

/-- 列表 → Lst → 列表，原样回来。 -/
theorem fromLst_toLst (as : List a) : fromLst (toLst as) = as := by
  induction as with
  | nil => rfl
  | cons x xs ih =>
    show [x] ++ foldMap (fun x => [x]) xs = x :: xs
    rw [show foldMap (fun x => [x]) xs = xs from ih]
    rfl
```

::: warning 易错点：另一个方向需要“定律”
反方向 `toLst (fromLst l) = l` 在 Lean 里**证明不了**——而且一般来说根本就是错的。原因有两个：一是 `MyMonoid` 没有要求幺半群定律（单位律、结合律），二是 Lean 没有参数性。原书说这只是“一个不错的近似”，Lean 让我们精确地看到了“近似”在哪里。本章挑战题里你会亲手构造一个反例。
:::

### 左 Kan 扩张

左 Kan 扩张是一个余端：

$$\mathrm{Lan}_K D\ a = \int^i \mathcal{A}(K i, a) \times D i$$

所以它翻译成存在量词。符号化地写：

```lean no-check
Lan k d a = exists i. (k i → a, d i)     -- 伪代码
```

在 Haskell 里，这可以用 GADT 或者全称量化的数据构造器来编码：`data Lan k d a = forall i. Lan (k i -> a) (d i)`。在 Lean 里，最直接的编码是一个带“类型字段”的结构体——也就是依值对：

```lean
/-- 左 Kan 扩张（朴素版本，对应 Haskell 的写法）：某个 i，一个 k i → a，一个 d i。 -/
structure Lan (k d : Type → Type) (a : Type) : Type 1 where
  {i : Type}
  run : k i → a
  di : d i

instance : Functor (Lan k d) where
  map g l := ⟨g ∘ l.run, l.di⟩

instance : LawfulFunctor (Lan k d) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

::: tip Lean 深入：结构体里的类型字段
`{i : Type}` 是一个**类型字段**：每个 `Lan k d a` 的值都“随身携带”一个类型 `i`。花括号表示它是隐式的——写 `⟨run, di⟩` 时，Lean 会从 `run` 和 `di` 的类型推断出 `i`。因为有一个字段是 `Type`，整个结构体就住在 `Type 1`。
:::

对这个数据结构的解释是：它包含一个函数，接受一个装着某种不明 `i` 的容器，产生一个 `a`；它还包含一个装着这些 `i` 的容器。因为你不知道 `i` 是什么，你对这个数据结构唯一能做的事，就是取出装 `i` 的那个容器，用一个自然变换把它重新打包成函子 `k` 所定义的容器，然后调用函数得到 `a`。比如，若 `d` 是树、`k` 是列表，你就可以把树序列化，用得到的列表调用那个函数，得到一个 `a`：

```lean
def treeToList : Lan List Tree String → String := fun l => l.run l.di.toList

#guard treeToList ⟨fun (xs : List Nat) => toString xs.sum, .node (.leaf 1) (.leaf 2)⟩ == "3"
```

### 用左 Kan 扩张计算右伴随：指数对象

左 Kan 扩张可以用来计算一个函子的右伴随。我们知道积函子的右伴随是指数对象，那就试着用 Kan 扩张来实现它。Haskell 里写作 `type Exp a b = Lan ((,) a) Identity b`，其中 `(,) a` 是“把 `i` 变成 `(a, i)`”的函子。Lean 的核心库没有给 `Prod a` 提供 `Functor` 实例，我们自己补一个：

```lean
instance : Functor (Prod a) where
  map f p := (p.1, f p.2)

/-- 用左 Kan 扩张实现指数对象：Lan (a × -) Id b -/
def Exp (a b : Type) : Type 1 := Lan (Prod a) Id b
```

它确实同构于函数类型，由下面这对函数作证：

```lean
def toExp (f : a → b) : Exp a b := ⟨f ∘ Prod.fst, (() : Unit)⟩

def fromExp (e : Exp a b) : a → b := fun x => e.run (x, e.di)

theorem fromExp_toExp (f : a → b) : fromExp (toExp f) = f := rfl
```

注意，正如前面一般情形下描述的，我们执行了如下步骤：

1. 取出装 `x` 的容器（这里只是一个平凡的恒等容器 `Id`），以及函数 `run`。
2. 用恒等函子与积函子之间的自然变换（`x ↦ (a, x)`）把容器重新打包。
3. 调用函数 `run`。

### Lean 胜出：带商的左 Kan 扩张

细心的你会发现，上面只证明了一个方向。另一个方向 `toExp (fromExp e) = e` 对朴素的 `Lan` 是**错**的：`toExp (fromExp e)` 携带的隐藏类型是 `Unit`，而 `e` 携带的可能是任意类型，两个值字面上就不一样。Haskell 靠参数性“假装”它们一样（你观察不出区别）。

而真正的左 Kan 扩张是一个**余端**——要按余楔条件取商！上一章我们已经学会用 `Quot` 构造余端，这里照方抓药。对 `f : i → j`，余楔条件把 `⟨h, map f di⟩`（隐藏类型 `j`）和 `⟨h ∘ map f, di⟩`（隐藏类型 `i`）粘在一起——“先在容器里把 `i` 换成 `j`”与“先把函数的输入从 `k j` 换成 `k i`”无法区分：

```lean
inductive LanRel (k d : Type → Type) [Functor k] [Functor d] (a : Type) :
    Lan k d a → Lan k d a → Prop where
  | glue {i j : Type} (f : i → j) (h : k j → a) (di : d i) :
      LanRel k d a ⟨h, Functor.map f di⟩ ⟨h ∘ Functor.map f, di⟩

/-- 真正的左 Kan 扩张 ∫^i A(K i, a) × D i -/
def LanQ (k d : Type → Type) [Functor k] [Functor d] (a : Type) : Type 1 := Quot (LanRel k d a)

def LanQ.mk [Functor k] [Functor d] {i : Type} (h : k i → a) (di : d i) : LanQ k d a :=
  Quot.mk _ ⟨h, di⟩
```

它仍然是一个守法的函子。`map` 用 `Quot.lift` 定义（要证明它尊重粘合关系），定律用 `Quot.ind` 归结到代表元上：

```lean
instance [Functor k] [Functor d] : Functor (LanQ k d) where
  map g := Quot.lift (fun l => LanQ.mk (g ∘ l.run) l.di) (by
    intro x y r
    cases r with
    | glue f h di => exact Quot.sound (LanRel.glue f (g ∘ h) di))

instance [Functor k] [Functor d] : LawfulFunctor (LanQ k d) where
  map_const := rfl
  id_map q := by
    induction q using Quot.ind with
    | mk l => rfl
  comp_map g h q := by
    induction q using Quot.ind with
    | mk l => rfl
```

现在，指数对象的两个方向都成立了：

```lean
def ExpQ (a b : Type) : Type 1 := LanQ (Prod a) Id b

def toExpQ (f : a → b) : ExpQ a b := LanQ.mk (f ∘ Prod.fst) (() : Unit)

def fromExpQ : ExpQ a b → (a → b) :=
  Quot.lift (fun e x => e.run (x, e.di)) (by
    intro x y r
    cases r with
    | glue f h di => rfl)

theorem fromExpQ_toExpQ (f : a → b) : fromExpQ (toExpQ f) = f := rfl

/-- 朴素版本里不成立的方向，在商里成立了。 -/
theorem toExpQ_fromExpQ (e : ExpQ a b) : toExpQ (fromExpQ e) = e := by
  induction e using Quot.ind with
  | mk l =>
    obtain ⟨g, x⟩ := l
    -- 用 f := fun _ : Unit => x 粘合：⟨g, x⟩ ∼ ⟨fun p => g (p.1, x), ()⟩
    exact (Quot.sound (LanRel.glue (k := Prod a) (d := Id) (fun (_ : Unit) => x) g (() : Unit))).symm
```

于是 `ExpQ a b ≅ (a → b)`：积函子 `a × -` 的右伴随确实就是指数对象，而且这一次是被 Lean 检查过的。

### 补充：在 Lean 中证明 Ran 是右伴随

上面的 `Ran` 和 `Lan` 一样是“朴素版本”：它对 `i` 的量化没有附带自然性条件（Haskell 由参数性白送）。按照端的定义，真正的右 Kan 扩张是带楔条件的——对函数类型的端来说，楔条件就是自然性。我们把它写进结构体：

```lean
/-- 真正的右 Kan 扩张 ∫_i Set(A(a, K i), D i)：带自然性条件。 -/
@[ext]
structure RanN (k d : Type → Type) [Functor k] [Functor d] (a : Type) : Type 1 where
  run : (i : Type) → (a → k i) → d i
  nat : ∀ {i j : Type} (f : i → j) (h : a → k i),
    run j (Functor.map f ∘ h) = Functor.map f (run i h)

instance [Functor k] [Functor d] : Functor (RanN k d) where
  map g r := ⟨fun i h => r.run i (h ∘ g), fun f h => r.nat f (h ∘ g)⟩

instance [Functor k] [Functor d] : LawfulFunctor (RanN k d) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

现在可以陈述并证明伴随 $[\mathcal{I}, \mathbf{Set}](F' \circ K, D) \cong [\mathcal{A}, \mathbf{Set}](F', \mathrm{Ran}_K D)$（在 $\mathcal{I} = \mathcal{A} = \mathbf{Set}$ 的情形）。先定义两种自然变换：`NT F G` 是一般的自然变换（允许 `F`、`G` 输出到不同宇宙，因为 `RanN k d` 输出到 `Type 1`）；`NTK F' k d` 是 $F' \circ K \Rightarrow D$：

```lean
structure NT (F : Type → Type u) (G : Type → Type v) [Functor F] [Functor G] where
  app : (a : Type) → F a → G a
  nat : ∀ {a b : Type} (f : a → b) (x : F a), app b (Functor.map f x) = Functor.map f (app a x)

/-- ε′ : F′ ∘ K ⟹ D -/
structure NTK (F' : Type → Type u) (k d : Type → Type) [Functor F'] [Functor k] [Functor d] where
  app : (i : Type) → F' (k i) → d i
  nat : ∀ {i j : Type} (f : i → j) (x : F' (k i)),
    app j (Functor.map (Functor.map f) x) = Functor.map f (app i x)

theorem NT.ext' {F : Type → Type u} {G : Type → Type v} [Functor F] [Functor G]
    {σ τ : NT F G} (h : σ.app = τ.app) : σ = τ := by
  cases σ; cases τ; cases h; rfl

theorem NTK.ext' {F' : Type → Type u} [Functor F'] [Functor k] [Functor d] {σ τ : NTK F' k d}
    (h : σ.app = τ.app) : σ = τ := by
  cases σ; cases τ; cases h; rfl

/-- 余单位 ε : Ran_K D ∘ K ⟹ D：用 id 去“戳”一下。 -/
def ranCounit [Functor k] [Functor d] : NTK (RanN k d) k d where
  app i r := r.run i id
  nat f r := by
    show r.run _ (id ∘ (Functor.map f)) = _
    exact r.nat f id
```

伴随本身：从 `ε′` 造 `σ`（`σ a x` 收到 `h : a → k i`，就把 `x : F' a` 用 `map h` 推到 `F' (k i)`，再交给 `ε′`）；从 `σ` 造 `ε′`（用 `id` 戳一下，即与余单位复合）。两个方向互逆，用到的恰好是各自的自然性：

```lean
def ranAdj (F' k d : Type → Type) [Functor F'] [Functor k] [Functor d]
    [LawfulFunctor F'] [LawfulFunctor k] [LawfulFunctor d] :
    NTK F' k d ≅ NT F' (RanN k d) where
  toFun ε := {
    app := fun a x => {
      run := fun i h => ε.app i (Functor.map h x)
      nat := fun f h => by
        show ε.app _ (Functor.map (Functor.map f ∘ h) x) = _
        rw [comp_map]
        exact ε.nat f (Functor.map h x) }
    nat := fun g x => by
      apply RanN.ext
      funext i h
      show ε.app i (Functor.map h (Functor.map g x)) = ε.app i (Functor.map (h ∘ g) x)
      rw [comp_map] }
  invFun σ := {
    app := fun i x => (σ.app (k i) x).run i id
    nat := fun {i j} f x => by
      show (σ.app (k j) (Functor.map (Functor.map f) x)).run j id = _
      rw [σ.nat]
      show (σ.app (k i) x).run j (id ∘ Functor.map f) = _
      exact (σ.app (k i) x).nat f id }
  left_inv ε := by
    apply NTK.ext'
    funext i x
    show ε.app i (Functor.map id x) = ε.app i x
    rw [id_map]
  right_inv σ := by
    apply NT.ext'
    funext a x
    apply RanN.ext
    funext i h
    show (σ.app (k i) (Functor.map h x)).run i id = (σ.app a x).run i h
    rw [σ.nat]   -- σ 的自然性把 map h 移进 Ran 里
    rfl
```

这就是本章那张“伴随”插图的 Lean 版本：左边每一个 $\varepsilon'$，右边恰好对应一个 $\sigma$。

### 余密度单子

前面提到，函子沿其自身的右 Kan 扩张 $K/K = \mathrm{Ran}_K K$ 叫作余密度单子。在 Lean 里它就是 `Ran k k`，而且——不管 `k` 是什么，哪怕它根本不是函子——它都是一个守法的单子：

```lean
abbrev Codensity (k : Type → Type) := Ran k k

instance : Monad (Codensity k) where
  pure a := fun _ h => h a
  bind m f := fun i h => m i (fun a => f a i h)

instance : LawfulMonad (Codensity k) := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun _ _ _ => rfl)
```

::: tip 补充：余密度单子有什么用
`Codensity k a` 的值是“给我一个后续（continuation）`a → k i`，我就给你一个 `k i`”——它是续延传递风格（CPS）。`bind` 只是把后续往里塞，从不真正去 `k` 里做事，所以**无论你怎么嵌套 `bind`，它们都被重新结合成右结合的**。对于左结合 `bind` 代价很高的单子（比如自由单子、或用列表拼接实现的 Writer），先把计算放进 `Codensity` 里跑、最后再一次性“降”回原单子，可以把平方复杂度降成线性。这就是 Haskell 里著名的“codensity 优化”。

注意 `LawfulMonad` 的三条定律在这里都是 `rfl`：CPS 把单子定律变成了函数复合的定律。`LawfulMonad.mk'` 是核心库提供的便捷构造器：只需证明 `id_map`、`pure_bind`、`bind_assoc`，其余定律从默认实现中自动得到。
:::

## 自由函子

Kan 扩张的一个有趣应用，是构造**自由函子**（free functor）。它解决的是这样一个实际问题：假设你有一个类型构造器——也就是一个对象的映射。能不能在它的基础上定义一个函子？换句话说，能不能定义一个态射的映射，把这个类型构造器扩展成一个完整的自函子？

关键的观察是：类型构造器可以被描述成一个定义域为**离散范畴**的函子。离散范畴除了恒等态射以外没有别的态射。给定范畴 $\mathcal{C}$，我们总能通过丢掉所有非恒等态射，构造出一个离散范畴 $|\mathcal{C}|$。从 $|\mathcal{C}|$ 到 $\mathcal{C}$ 的函子 $F$ 就只是一个简单的对象映射，也就是我们在编程中所说的类型构造器。还有一个典范函子 $J$，把 $|\mathcal{C}|$ 注入 $\mathcal{C}$：它在对象上（以及恒等态射上）是恒等的。$F$ 沿 $J$ 的左 Kan 扩张（如果存在的话），就是一个从 $\mathcal{C}$ 到 $\mathcal{C}$ 的函子：

$$\mathrm{Lan}_J F\ a = \int^i \mathcal{C}(J i, a) \times F i$$

它叫作基于 $F$ 的自由函子。

在 Lean 里，我们这样写（同样用带类型字段的结构体表示存在量词）：

```lean
/-- 自由函子：Lan_J f a = Σ i, (i → a) × f i -/
structure FreeF (f : Type → Type) (a : Type) : Type 1 where
  {i : Type}
  h : i → a
  fi : f i
```

的确，对**任何**类型构造器 `f`，`FreeF f` 都是一个函子：

```lean
instance : Functor (FreeF f) where
  map g x := ⟨g ∘ x.h, x.fi⟩

instance : LawfulFunctor (FreeF f) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

如你所见，自由函子“伪造”了函数的提升：它把函数和参数都记录下来。它通过记录复合，来累积被提升的函数。函子定律自动满足。这个构造被用在了论文 [Freer Monads, More Extensible Effects](http://okmij.org/ftp/Haskell/extensible/more.pdf) 中。

来看一个 `f` 本身**不是**函子的例子：谓词 `Pred a := a → Bool`。它对 `a` 是逆变的，你没法给它写 `Functor` 实例；可 `FreeF Pred` 却是一个守法的函子。另外，如果 `f` 本来就是函子，我们可以随时把 `FreeF f` 中积攒的函数一次性“执行”掉（这正是上一章的忍者米田引理：`FreeF f` 就是 Coyoneda）：

```lean
def Pred (a : Type) : Type := a → Bool

def isEven : Pred Nat := fun n => n % 2 == 0

-- Pred 不是函子，但 FreeF Pred 是：我们可以对它 map，函数被记录下来
def evenAsString : FreeF Pred String := Functor.map toString (⟨id, isEven⟩ : FreeF Pred Nat)

#guard evenAsString.h (7 : Nat) == "7"

def FreeF.lift (x : f a) : FreeF f a := ⟨id, x⟩
def FreeF.lower [Functor f] (x : FreeF f a) : f a := Functor.map x.h x.fi

#guard (Functor.map (· * 10) (FreeF.lift [1, 2, 3])).lower == [10, 20, 30]
```

（`#guard evenAsString.h (7 : Nat) == "7"` 那一行能通过类型检查，是因为 `evenAsString` 隐藏的类型 `i` 在这里就是 `Nat`——Lean 在定义处能看到它。在一般的使用中，隐藏类型对你是不透明的。）

或者，我们也可以用右 Kan 扩张达到同样的目的：

```lean
/-- 用右 Kan 扩张构造的自由函子：Ran_J f a = ∀ i, (a → i) → f i -/
def FreeR (f : Type → Type) (a : Type) : Type 1 := (i : Type) → (a → i) → f i
```

很容易验证它确实是一个函子：

```lean
instance : Functor (FreeR f) where
  map g r := fun _ bi => r _ (bi ∘ g)

instance : LawfulFunctor (FreeR f) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

## 补充：“所有概念都是 Kan 扩张”

Saunders Mac Lane 在他的经典教材《Categories for the Working Mathematician》中，有一节的标题就叫“All Concepts are Kan Extensions”（所有概念都是 Kan 扩张）。读完这一章，你已经可以验证这句话的大半了：

| 概念 | 作为 Kan 扩张 |
|---|---|
| 极限 $\lim D$ | 沿 $K : \mathcal{I} \to \mathbf{1}$ 的右 Kan 扩张 $\mathrm{Ran}_K D$（本章开头） |
| 余极限 $\mathrm{colim}\, D$ | 沿 $K : \mathcal{I} \to \mathbf{1}$ 的左 Kan 扩张 $\mathrm{Lan}_K D$ |
| $K$ 的左伴随 | $\mathrm{Ran}_K I$（在 $K$ 保持它时）；例：自由幺半群 `Lst` |
| $K$ 的右伴随 | $\mathrm{Lan}_K I$（在 $K$ 保持它时）；例：指数对象 `ExpQ` |
| 米田引理 | 沿恒等函子的 Kan 扩张就是函子本身：$\mathrm{Ran}_{I} D \cong D \cong \mathrm{Lan}_{I} D$ |
| 余密度单子 | $\mathrm{Ran}_K K$ |
| 自由函子 | 沿 $J : |\mathcal{C}| \to \mathcal{C}$ 的左（或右）Kan 扩张 |

“米田引理”那一行值得多说一句。把 $K$ 取成恒等函子，端公式变成 $\mathrm{Ran}_I D\ a \cong \int_i \mathbf{Set}(\mathcal{A}(a, i), D i)$——这正是上一章忍者米田引理的左边，所以它同构于 $D a$。用 Lean 证明这件事是本章的挑战题之一。左 Kan 扩张那边同理：$\mathrm{Lan}_I D \cong D$ 就是“余米田”（Coyoneda）。

为什么 Kan 扩张如此无处不在？因为几乎所有泛构造都可以表述为“在一堆候选者中找最好的那一个”，而 Kan 扩张恰好是这件事在函子层面的最一般形式：它在所有“沿 $K$ 近似 $D$”的函子中，找出最好的那个。极限是“最好的锥顶点”，伴随是“最好的逆”，而 Kan 扩张是“最好的延拓”。

```lean hidden
end Ch311
```

## 挑战

原书本章没有挑战题。下面是本书新增的练习。

1. 为带商的左 Kan 扩张证明伴随：`NT (LanQ k d) F' ≅ NTD d F' k`，其中 `NTD d F' k` 表示自然变换 $D \Rightarrow F' \circ K$。顺便写出单位 $\eta : D \Rightarrow \mathrm{Lan}_K D \circ K$。
2. 沿恒等函子的右 Kan 扩张就是米田引理：证明 `RanN Id d a ≅ d a`（`d` 守法）。
3. 在偏序例子中，设 $\mathcal{A} = \{a_0 < a_1 < \cdots < a_5\}$，$\mathcal{I} = \{a_1, a_4\}$，$D(a_1) = 2$，$D(a_4) = 7$。手算 $\mathrm{Ran}_K D$ 和 $\mathrm{Lan}_K D$ 在每个 $a_j$ 上的值，然后用上面的小工具验证。
4. 构造一个 `strange : Lst Unit`，并证明 `toLst (fromLst strange) ≠ strange`。提示：找一个“不守法”的 `MyMonoid` 实例。
5. 当 `m` 是单子时，写出 `liftCod : m α → Codensity m α` 和 `lowerCod : Codensity m α → m α`，并证明 `lowerCod (liftCod x) = x`（需要 `LawfulMonad m`）。

::: details 参考答案
```lean
namespace Ch311

-- 1. 左 Kan 扩张的伴随
structure NTD (d : Type → Type) (F' : Type → Type u) (k : Type → Type)
    [Functor d] [Functor F'] [Functor k] where
  app : (i : Type) → d i → F' (k i)
  nat : ∀ {i j : Type} (f : i → j) (x : d i),
    app j (Functor.map f x) = Functor.map (Functor.map f) (app i x)

theorem NTD.ext' {F' : Type → Type u} [Functor d] [Functor F'] [Functor k] {σ τ : NTD d F' k}
    (h : σ.app = τ.app) : σ = τ := by
  cases σ; cases τ; cases h; rfl

/-- 单位 η : D ⟹ Lan_K D ∘ K -/
def lanUnit [Functor k] [Functor d] : NTD d (LanQ k d) k where
  app _ di := LanQ.mk id di
  nat f di := Quot.sound (LanRel.glue f id di)

def lanAdj (F' k d : Type → Type) [Functor F'] [Functor k] [Functor d]
    [LawfulFunctor F'] [LawfulFunctor k] [LawfulFunctor d] :
    NT (LanQ k d) F' ≅ NTD d F' k where
  toFun σ := {
    app := fun i di => σ.app (k i) (LanQ.mk id di)
    nat := fun {i j} f di => by
      rw [← σ.nat]
      exact congrArg (σ.app (k j)) (Quot.sound (LanRel.glue f id di)) }
  invFun η := {
    app := fun _ => Quot.lift (fun l => Functor.map l.run (η.app l.i l.di)) (by
      intro x y r
      cases r with
      | glue f h di =>
        show Functor.map h (η.app _ (Functor.map f di)) = Functor.map (h ∘ Functor.map f) (η.app _ di)
        rw [η.nat, comp_map])
    nat := fun g q => by
      induction q using Quot.ind with
      | mk l =>
        show Functor.map (g ∘ l.run) (η.app l.i l.di) = Functor.map g (Functor.map l.run (η.app l.i l.di))
        rw [comp_map] }
  left_inv σ := by
    apply NT.ext'
    funext a q
    induction q using Quot.ind with
    | mk l =>
      show Functor.map l.run (σ.app (k l.i) (LanQ.mk id l.di)) = σ.app a (Quot.mk _ l)
      rw [← σ.nat]
      rfl
  right_inv η := by
    apply NTD.ext'
    funext i di
    show Functor.map id (η.app i di) = η.app i di
    rw [id_map]

-- 2. Ran 沿恒等函子 = 米田引理
def ranYoneda (d : Type → Type) [Functor d] [LawfulFunctor d] (a : Type) : RanN Id d a ≅ d a where
  toFun r := r.run a id
  invFun x := {
    run := fun _ h => Functor.map h x
    nat := fun f h => by
      show Functor.map (fun y => f (h y)) x = Functor.map f (Functor.map h x)
      rw [Functor.map_map] }
  left_inv r := by
    apply RanN.ext
    funext i h
    exact (r.nat (k := Id) h id).symm   -- 自然性：run i h = map h (run a id)
  right_inv x := id_map x

-- 4. 不守法的“幺半群”让 Lst 多出了不来自任何列表的元素
def strange : Lst Unit := fun _ _ _ => MyMonoid.mul MyMonoid.one MyMonoid.one

instance weirdNat : MyMonoid Nat := ⟨0, fun a b => a + b + 1⟩   -- mul one one = 1 ≠ one

example : toLst (fromLst strange) ≠ strange := by
  intro h
  -- 在 weirdNat 上求值：左边是 one = 0，右边是 mul one one = 1
  have := congrArg (fun (l : Lst Unit) => l Nat (fun _ => 0)) h
  revert this
  decide

-- 5. Codensity 的提升与下降
def liftCod [Monad m] (x : m α) : Codensity m α := fun _ h => x >>= h
def lowerCod [Monad m] (c : Codensity m α) : m α := c α pure

theorem lower_lift [Monad m] [LawfulMonad m] (x : m α) : lowerCod (liftCod x) = x := by
  simp [lowerCod, liftCod]   -- x >>= pure = x

end Ch311
```

第 3 题答案：$\mathrm{Ran}_K D(a_j) = \min\{D(i) \mid a_j \le i\}$，$\mathrm{Lan}_K D(a_j) = \max\{D(i) \mid i \le a_j\}$。

| | $a_0$ | $a_1$ | $a_2$ | $a_3$ | $a_4$ | $a_5$ |
|---|---|---|---|---|---|---|
| $\mathrm{Ran}_K D$ | 2 | 2 | 7 | 7 | 7 | $\top$ |
| $\mathrm{Lan}_K D$ | $\bot$ | 2 | 2 | 2 | 7 | 7 |

在 $a_1$、$a_4$ 上两者都等于 $D$；在 $a_2$、$a_3$ 这段“空白”上，$\mathrm{Ran}$ 乐观地取了后面的 7，$\mathrm{Lan}$ 保守地取了前面的 2；在两端，没有信息的那一侧只能取 $\top$ 或 $\bot$。
:::

## 本章小结

- 用三个范畴重述极限：极限就是沿 $K : \mathcal{I} \to \mathbf{1}$ 的**右 Kan 扩张**，锥就是自然变换 $\varepsilon : F \circ K \Rightarrow D$。
- 把 $\mathbf{1}$ 换成任意 $\mathcal{A}$：$\mathrm{Ran}_K D$ 是所有“$F' \circ K \Rightarrow D$”中最好的 $F'$，任何候选都经由唯一的 $\sigma$ 分解到它；$\mathrm{Lan}_K D$ 是对偶的，方向反过来。
- Kan 扩张 = 沿嵌入 $K$ 把 $D$ **延拓**到更大范畴上的“最好近似”；在偏序上，$\mathrm{Ran}$ 是最大的下方延拓（取 $\min$），$\mathrm{Lan}$ 是最小的上方延拓（取 $\max$）。
- **伴随**：$\mathrm{Lan}_K \dashv (- \circ K) \dashv \mathrm{Ran}_K$；恒等函子的 Kan 扩张可以计算伴随：$\mathrm{Ran}_K I \dashv K \dashv \mathrm{Lan}_K I$（在保持条件下）。$\mathrm{Ran}_K K$ 是**余密度单子**。
- **端公式**：$\mathrm{Ran}_K D\ a \cong \int_i \mathbf{Set}(\mathcal{A}(a, K i), D i)$，$\mathrm{Lan}_K D\ a = \int^i \mathcal{A}(K i, a) \times D i$。
- 在 Lean 中：`Ran k d a = ∀ i, (a → k i) → d i`（全称量化，住在 `Type 1`），`Lan k d a = Σ i, (k i → a) × d i`（存在类型）；两者都是守法的 `Functor`。
- Lean 胜出：带自然性的 `RanN` 让我们**证明**了 $\mathrm{Ran}$ 是右伴随；带商的 `LanQ` 让 `Exp` 与函数类型的同构**两个方向**都成立——朴素版本只能靠 Haskell 的参数性“假装”。
- **自由函子**是沿离散范畴嵌入 $J$ 的 Kan 扩张：对任何类型构造器（哪怕是逆变的 `Pred`），`FreeF f` 都是守法的函子。
- Mac Lane：“所有概念都是 Kan 扩张”——极限、余极限、伴随、米田引理、余密度单子都是它的特例。
