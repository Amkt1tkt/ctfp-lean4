# A 术语表（中英对照）

本附录收录全书使用的术语。表中的中文译名是全书统一的译法（以 `STYLE.md` 的术语表为基础扩充而来）；
“一句话解释”只求帮你快速回忆，准确的定义请点击“首次出现”一栏回到正文。术语按主题分组，同一组内大致按在书中出现的先后排列。

“首次出现”指该术语在本书中**正式引入**的章节；有些术语在更早的章节里被顺带提到过。
带 0.1、0.2 的条目是本书新增的导读章节，原书没有对应内容。

<div><ChAGlossaryFilter /></div>

## 集合、函数与基础数学

| 中文 | English | 一句话解释 | 首次出现 |
|---|---|---|---|
| 集合 | set | 只关心“谁在里面”的一堆东西，不计顺序与重复 | [0.2 §1](/guide/math-toolkit) |
| 元素 | element | 集合里的成员，记作 $x \in A$ | [0.2 §1](/guide/math-toolkit) |
| 空集 | empty set | 没有任何元素的集合 $\varnothing$；对应 Lean 的 `Empty` | [0.2 §1](/guide/math-toolkit) |
| 子集 | subset | $A$ 的每个元素都在 $B$ 中，记作 $A \subseteq B$ | [0.2 §2](/guide/math-toolkit) |
| 幂集 | power set | 一个集合的全部子集组成的集合 | [0.2 §2](/guide/math-toolkit) |
| 外延性 | extensionality | 集合由元素决定；函数由它在每个点上的值决定 | [1.3](/part1/03-categories-great-and-small) |
| 笛卡尔积 | Cartesian product | 所有有序对 $(a, b)$ 组成的集合 $A \times B$ | [0.2 §3](/guide/math-toolkit)、[1.8](/part1/08-functoriality) |
| 不交并 | disjoint union | 给元素贴上“左/右”标签后放在一起，$A + B$ | [0.2 §3](/guide/math-toolkit) |
| 函数 | function | 给定义域中每个元素分配陪域中恰好一个元素的规则 | [0.2 §4](/guide/math-toolkit)、[1.2](/part1/02-types-and-functions) |
| 定义域 / 陪域 | domain / codomain | 函数 $f \colon A \to B$ 中的 $A$ 与 $B$ | [0.2 §4](/guide/math-toolkit) |
| 像 | image | 函数实际取到的值组成的集合 | [0.2 §4](/guide/math-toolkit) |
| 良定义 | well-defined | 每个输入恰好对应一个输出，规则不自相矛盾 | [0.2 §4](/guide/math-toolkit) |
| 单射 | injective (one-to-one) | 不同的输入给出不同的输出 | [1.5](/part1/05-products-and-coproducts) |
| 满射 | surjective (onto) | 陪域中每个元素都有原像 | [1.5](/part1/05-products-and-coproducts) |
| 双射 | bijective / bijection | 既单又满；两个集合元素的完美配对 | [1.5](/part1/05-products-and-coproducts) |
| 反函数（逆） | inverse | 与 $f$ 复合后在两边都得到恒等函数的函数 | [0.2 §4](/guide/math-toolkit) |
| 截面 / 收缩 | section / retraction | 若 $g \circ f = \mathrm{id}$，则 $f$ 是 $g$ 的截面，$g$ 是 $f$ 的收缩 | [0.2 §4](/guide/math-toolkit) |
| 关系 | relation | 对每一对元素回答“有没有联系”的规则 | [0.2 §5](/guide/math-toolkit) |
| 等价关系 | equivalence relation | 自反、对称、传递的关系，表达“某种意义下一样” | [0.2 §5](/guide/math-toolkit)、[3.10](/part3/10-ends-and-coends) |
| 商 | quotient | 把等价的元素视为同一个后得到的集合 | [0.2 §5](/guide/math-toolkit) |
| 基数 | cardinality | 集合的大小；有限集合即元素个数 $\lvert A \rvert$ | [0.2 §7](/guide/math-toolkit) |
| 谓词 | predicate | 对每个元素给出一个命题（真或假）的函数 | [1.2](/part1/02-types-and-functions) |
| 群 | group | 每个元素都有逆元的幺半群 | [0.2 §10](/guide/math-toolkit) |
| 同态 | homomorphism | 保持代数结构（运算与单位元）的函数 | [2.3](/part2/03-free-monoids) |
| 半环 / 环 | semiring (rig) / ring | 有加法和乘法、满足分配律的代数结构；半环不要求有减法 | [1.6](/part1/06-simple-algebraic-data-types) |

## 逻辑与证明

| 中文 | English | 一句话解释 | 首次出现 |
|---|---|---|---|
| 命题 | proposition | 或真或假的陈述；Lean 中是 `Prop` 中的类型 | [0.2 §8](/guide/math-toolkit)、[0.1 §14](/guide/lean-for-rustaceans) |
| 蕴涵 | implication | “若 P 则 Q”，记作 $P \Rightarrow Q$；Lean 中就是函数类型 `P → Q` | [0.2 §8](/guide/math-toolkit) |
| 全称量词 / 存在量词 | universal / existential quantifier | “对所有” $\forall$ 与“存在” $\exists$ | [0.2 §8](/guide/math-toolkit) |
| 唯一存在 | unique existence | 存在，并且任何两个满足条件的东西都相等，记作 $\exists!$ | [0.2 §11](/guide/math-toolkit)、[1.5](/part1/05-products-and-coproducts) |
| 空真 | vacuous truth | 前提为假时蕴涵自动成立，例如“空集的每个元素都……” | [0.2 §8](/guide/math-toolkit) |
| 反证法 | proof by contradiction | 假设结论不成立，推出矛盾 | [0.2 §9](/guide/math-toolkit) |
| 逆否命题 | contrapositive | “若非 Q 则非 P”，与“若 P 则 Q”等价 | [0.2 §9](/guide/math-toolkit) |
| 数学归纳法 | mathematical induction | 证明基础情况，再证明“对 k 成立则对 k+1 成立” | [0.2 §9](/guide/math-toolkit) |
| 构造性证明 | constructive proof | 通过真正构造出见证者来证明“存在” | [0.2 §9](/guide/math-toolkit) |
| 排中律 | law of excluded middle | 任何命题要么真要么假；Lean 中为 `Classical.em` | [0.1 §14](/guide/lean-for-rustaceans) |
| 肯定前件（假言推理） | modus ponens | 由“P”和“若 P 则 Q”得到“Q”；对应函数应用 | [1.9](/part1/09-function-types) |
| 命题即类型 | propositions as types (Curry–Howard) | 命题是类型，证明是该类型的值（程序） | [0.1 §14](/guide/lean-for-rustaceans)、[1.9](/part1/09-function-types) |
| 等式推理 | equational reasoning | 反复用等式替换来证明两个表达式相等 | [1.7](/part1/07-functors) |
| 交换图 | commutative diagram | 同起点同终点的路径复合结果都相等的图 | [0.2 §12](/guide/math-toolkit)、[1.1](/part1/01-category) |
| 追图 | diagram chasing | 拿一个元素沿图中不同路径走一遍，检验交换性 | [0.2 §12](/guide/math-toolkit) |

## 范畴的基本概念

| 中文 | English | 一句话解释 | 首次出现 |
|---|---|---|---|
| 范畴 | category | 对象、态射、可结合的复合与恒等态射组成的结构 | [1.1](/part1/01-category) |
| 对象 | object | 范畴中的“点”；其内部结构对范畴不可见 | [1.1](/part1/01-category) |
| 态射 / 箭头 | morphism / arrow | 从一个对象指向另一个对象的箭头，两者混用 | [1.1](/part1/01-category) |
| 复合 | composition | 首尾相接的两个态射得到一个新态射 $g \circ f$（“g 在 f 之后”） | [1.1](/part1/01-category) |
| 恒等态射 | identity (morphism) | 每个对象上“什么都不做”的态射 $\mathrm{id}_a$，是复合的单位 | [1.1](/part1/01-category) |
| 结合律 | associativity | $h \circ (g \circ f) = (h \circ g) \circ f$ | [1.1](/part1/01-category) |
| 单位律 | unit laws (identity laws) | $f \circ \mathrm{id} = f = \mathrm{id} \circ f$ | [1.1](/part1/01-category) |
| 可复合的 | composable | 前一个态射的终点是后一个态射的起点 | [1.3](/part1/03-categories-great-and-small) |
| hom-集 | hom-set | 两个对象之间所有态射组成的集合 $\mathcal{C}(a, b)$（态射集合） | [1.3](/part1/03-categories-great-and-small) |
| 集合范畴 | category of sets ($\mathbf{Set}$) | 对象是集合、态射是函数的范畴 | [1.2](/part1/02-types-and-functions) |
| 范畴的范畴 | category of categories ($\mathbf{Cat}$) | 对象是（小）范畴、态射是函子的范畴 | [1.3](/part1/03-categories-great-and-small)、[1.7](/part1/07-functors) |
| 自由范畴 | free category | 由一张有向图添加恒等与全部复合后生成的范畴 | [1.3](/part1/03-categories-great-and-small) |
| 预序 / 偏序 / 全序 | preorder / partial order / total order | 自反传递 / 再加反对称 / 再加任意两元可比的关系 | [1.3](/part1/03-categories-great-and-small) |
| 偏序集 | poset | 带偏序的集合 | [1.5](/part1/05-products-and-coproducts) |
| 瘦范畴 | thin category | 任意两对象间至多一个态射的范畴；即预序 | [1.3](/part1/03-categories-great-and-small) |
| 幺半群 | monoid | 带可结合二元运算与单位元的集合；等价于单对象范畴 | [1.3](/part1/03-categories-great-and-small) |
| 无点风格 | point-free | 只谈函数的复合、不提及参数的写法 | [1.3](/part1/03-categories-great-and-small) |
| Kleisli 范畴 | Kleisli category | 态射是修饰函数 $a \to m\,b$ 的范畴 | [1.4](/part1/04-kleisli-categories) |
| 修饰函数 | embellished function | 返回值附带额外信息（日志、可能失败等）的函数 | [1.4](/part1/04-kleisli-categories) |
| 同构 | isomorphism / isomorphic | 有逆的态射；“只差改个名字”的两个对象 | [1.5](/part1/05-products-and-coproducts) |
| 在同构意义下唯一 | unique up to isomorphism | 满足条件的对象可能很多，但两两同构 | [1.5](/part1/05-products-and-coproducts) |
| 对偶 | duality / dual | 把所有箭头反向后得到的概念 | [1.5](/part1/05-products-and-coproducts) |
| 对偶范畴（反范畴） | opposite category | 对象相同、箭头全部反向的范畴 $\mathcal{C}^{op}$ | [1.5](/part1/05-products-and-coproducts) |
| 单态射 / 满态射 | monomorphism / epimorphism | 可左消去 / 可右消去的态射；在 $\mathbf{Set}$ 中即单射 / 满射 | [3.13](/part3/13-topoi) |
| 骨架 | skeleton | 每个同构类只保留一个对象的子范畴 | [3.14](/part3/14-lawvere-theories) |

## 泛构造

| 中文 | English | 一句话解释 | 首次出现 |
|---|---|---|---|
| 泛构造 / 泛性质 | universal construction / property | 在所有“候选者”中挑出最好的那个的定义方式 | [1.5](/part1/05-products-and-coproducts) |
| 始对象 | initial object | 到每个对象都恰有一个态射的对象；$\mathbf{Set}$ 中是空集 | [1.5](/part1/05-products-and-coproducts) |
| 终对象 | terminal object | 每个对象到它都恰有一个态射的对象；$\mathbf{Set}$ 中是单元素集 | [1.5](/part1/05-products-and-coproducts) |
| 积 | product | 带两个投影、对任何候选者都有唯一分解的对象 $a \times b$ | [1.5](/part1/05-products-and-coproducts) |
| 余积 | coproduct | 积的对偶，带两个内射；$\mathbf{Set}$ 中是不交并 | [1.5](/part1/05-products-and-coproducts) |
| 投影 / 内射 | projection / injection | 从积出发的 $\pi_1, \pi_2$ / 进入余积的 $\iota_1, \iota_2$ | [1.5](/part1/05-products-and-coproducts) |
| 分解子 | factorizer | 泛构造中把候选者唯一分解出来的那个态射的构造函数 | [1.5](/part1/05-products-and-coproducts) |
| 幺半范畴 | monoidal category | 带张量积和单位对象、满足结合与单位律（在同构意义下）的范畴 | [1.6](/part1/06-simple-algebraic-data-types)、[3.6](/part3/06-monads-categorically) |
| 张量积 | tensor product | 幺半范畴中“把两个对象合成一个”的双函子 $\otimes$ | [3.6](/part3/06-monads-categorically) |
| 函数类型 / 指数对象 | function type / exponential | 代表“从 a 到 b 的态射”的对象 $b^a$ | [1.9](/part1/09-function-types) |
| 求值 | evaluation | 把函数作用到参数上的态射 $b^a \times a \to b$ | [1.9](/part1/09-function-types) |
| 柯里化 | currying | $(a \times b) \to c$ 与 $a \to (b \to c)$ 之间的一一对应 | [1.9](/part1/09-function-types) |
| 笛卡尔闭范畴 | cartesian closed category | 有终对象、积与指数对象的范畴 | [1.9](/part1/09-function-types) |
| 双笛卡尔闭范畴 | bicartesian closed category | 笛卡尔闭，并且还有始对象与余积 | [1.9](/part1/09-function-types) |
| 内部 hom | internal hom | 范畴内部代表 hom-集的对象，例如指数对象 | [1.9](/part1/09-function-types) |

## 类型与编程

| 中文 | English | 一句话解释 | 首次出现 |
|---|---|---|---|
| 类型 | type | 值的集合（在 Lean 中是这样的好模型） | [1.2](/part1/02-types-and-functions) |
| 纯函数 | pure function | 无副作用、相同输入总给出相同输出的函数 | [1.2](/part1/02-types-and-functions) |
| 副作用 | side effect | 函数在返回值之外对外界造成的影响（打印、改变状态等） | [1.2](/part1/02-types-and-functions)、[1.4](/part1/04-kleisli-categories) |
| 全函数 / 偏函数 | total / partial function | 对每个输入都有定义 / 对某些输入没有定义的函数 | [1.4](/part1/04-kleisli-categories)、[0.1 §8](/guide/lean-for-rustaceans) |
| 底（⊥） | bottom | 不终止的计算对应的“值”；Lean 的全函数中不存在 | [1.2](/part1/02-types-and-functions) |
| 类型推断 | type inference | 编译器自动推算出表达式的类型 | [1.2](/part1/02-types-and-functions) |
| 指称语义 / 操作语义 | denotational / operational semantics | 用数学对象 / 用执行步骤来解释程序的含义 | [1.2](/part1/02-types-and-functions) |
| 代数数据类型 | algebraic data type | 由积类型与和类型组合而成的类型 | [1.6](/part1/06-simple-algebraic-data-types) |
| 积类型 / 和类型 | product type / sum type | 有序对、结构体 / 枚举、`α ⊕ β` | [1.6](/part1/06-simple-algebraic-data-types) |
| 记录（结构体） | record | 字段带名字的积类型；Lean 中为 `structure` | [1.6](/part1/06-simple-algebraic-data-types) |
| 类型类 | type class | 描述“某类型支持哪些操作”的接口；≈ Rust 的 trait | [1.3](/part1/03-categories-great-and-small)、[0.1 §10](/guide/lean-for-rustaceans) |
| 实例 | instance | 某个类型对某个类型类的具体实现；≈ Rust 的 impl | [1.7](/part1/07-functors) |
| 高阶类型 | higher-kinded type | 对 `Type → Type` 这样的类型构造器做抽象；Rust 缺少此能力 | [0.1 §10](/guide/lean-for-rustaceans)、[1.7](/part1/07-functors) |
| 参数多态 | parametric polymorphism | 对所有类型一视同仁地工作的泛型函数 | [1.8](/part1/08-functoriality)、[1.10](/part1/10-natural-transformations) |
| 特设多态 | ad hoc polymorphism | 针对不同类型给出不同实现的多态（如类型类方法） | [1.10](/part1/10-natural-transformations) |
| 免费的定理 | theorems for free | 从参数多态函数的类型直接推出的性质 | [1.8](/part1/08-functoriality) |
| 透镜 | lens | 聚焦于数据结构某个部分的读写抽象 | [1.8](/part1/08-functoriality)、[3.7](/part3/07-comonads) |
| Writer / Reader / State 单子 | writer / reader / state monad | 附带日志 / 读取环境 / 读写状态的计算 | [1.4](/part1/04-kleisli-categories)、[3.5](/part3/05-monads-and-effects) |
| Kleisli 箭头 | Kleisli arrow | 形如 $a \to m\,b$ 的函数，Kleisli 范畴中的态射 | [3.4](/part3/04-monads-programmers-definition) |
| 上下文计算 | contextual computation | 余单子所刻画的“依赖于上下文的计算” | [3.7](/part3/07-comonads) |

## 函子与自然变换

| 中文 | English | 一句话解释 | 首次出现 |
|---|---|---|---|
| 函子 | functor | 范畴之间保持复合与恒等的映射（对象到对象、态射到态射） | [1.7](/part1/07-functors) |
| 自函子 | endofunctor | 从一个范畴到它自身的函子；如 `List`、`Option` | [1.7](/part1/07-functors) |
| 函子性 | functoriality | “能像函子一样提升函数”的性质 | [1.8](/part1/08-functoriality) |
| 双函子 | bifunctor | 两个参数的函子，如积与和 | [1.8](/part1/08-functoriality) |
| 协变 / 逆变 | covariant / contravariant | 保持箭头方向 / 反转箭头方向 | [1.8](/part1/08-functoriality) |
| 剖函子 | profunctor | 第一个参数逆变、第二个参数协变的双函子，如函数类型 | [1.8](/part1/08-functoriality) |
| 自然变换 | natural transformation | 两个函子之间、与态射“协调一致”的一族态射 | [1.10](/part1/10-natural-transformations) |
| 分量 | component | 自然变换在某个对象处的那个态射 $\alpha_a$ | [1.10](/part1/10-natural-transformations) |
| 自然性条件 / 自然性方块 | naturality condition / square | $G f \circ \alpha_a = \alpha_b \circ F f$ 及其交换图 | [1.10](/part1/10-natural-transformations) |
| 自然同构 | natural isomorphism | 每个分量都是同构的自然变换 | [1.10](/part1/10-natural-transformations) |
| 函子范畴 | functor category | 对象是函子、态射是自然变换的范畴 | [1.10](/part1/10-natural-transformations) |
| 垂直 / 水平复合 | vertical / horizontal composition | 自然变换的两种复合方式 | [1.10](/part1/10-natural-transformations) |
| 2-范畴 | 2-category | 除对象与态射外，还有“态射之间的态射”的结构 | [1.10](/part1/10-natural-transformations) |

## 极限、自由构造与米田引理

| 中文 | English | 一句话解释 | 首次出现 |
|---|---|---|---|
| 锥 / 余锥 | cone / cocone | 从一个顶点到图表各处（/ 从各处到顶点）的一族相容态射 | [2.2](/part2/02-limits-and-colimits) |
| 极限 / 余极限 | limit / colimit | 最好的锥 / 最好的余锥（终锥 / 始余锥） | [2.2](/part2/02-limits-and-colimits) |
| 等化子 / 余等化子 | equalizer / coequalizer | 使两个平行态射相等的“最大子对象” / “最大商对象” | [2.2](/part2/02-limits-and-colimits) |
| 拉回 / 推出 | pullback / pushout | 形如 $a \to c \leftarrow b$ 的图的极限 / 其对偶的余极限 | [2.2](/part2/02-limits-and-colimits) |
| 连续性 | continuity (of functors) | 函子保持极限的性质 | [2.2](/part2/02-limits-and-colimits) |
| 预层 | presheaf | 从 $\mathcal{C}^{op}$ 到 $\mathbf{Set}$ 的函子 | [2.2](/part2/02-limits-and-colimits) |
| 自由幺半群 | free monoid | 由一个集合生成、除定律外不附加任何等式的幺半群（即列表） | [2.3](/part2/03-free-monoids) |
| 遗忘函子 | forgetful functor | 忘掉结构、只保留底层集合的函子 | [2.3](/part2/03-free-monoids) |
| 底层集合 | underlying set | 带结构的对象去掉结构后剩下的集合 | [2.3](/part2/03-free-monoids) |
| 可表函子 | representable functor | 自然同构于某个 hom-函子 $\mathcal{C}(a, -)$ 的函子 | [2.4](/part2/04-representable-functors) |
| 表示 | representation | 可表函子与 hom-函子之间的那个自然同构 | [2.4](/part2/04-representable-functors) |
| 米田引理 | Yoneda lemma | 从 hom-函子到 $F$ 的自然变换与 $F a$ 一一对应 | [2.5](/part2/05-the-yoneda-lemma) |
| 米田嵌入 | Yoneda embedding | 把范畴完全忠实地嵌入其预层范畴的函子 | [2.6](/part2/06-yoneda-embedding) |

## 伴随、单子与代数

| 中文 | English | 一句话解释 | 首次出现 |
|---|---|---|---|
| 伴随 | adjunction | 两个反向函子间 hom-集的自然同构 $\mathcal{D}(L d, c) \cong \mathcal{C}(d, R c)$ | [3.2](/part3/02-adjunctions) |
| 左伴随 / 右伴随 | left adjoint / right adjoint | 伴随中的 $L$ / $R$ | [3.2](/part3/02-adjunctions) |
| 单位 / 余单位 | unit / counit | 伴随的两个自然变换 $\eta \colon \mathrm{Id} \to R L$ 与 $\varepsilon \colon L R \to \mathrm{Id}$ | [3.2](/part3/02-adjunctions) |
| 自由函子 | free functor | 遗忘函子的左伴随，构造“自由”对象 | [3.3](/part3/03-free-forgetful-adjunctions) |
| 单子 | monad | 带 `pure` 与 `bind`（或 $\eta$ 与 $\mu$）并满足定律的自函子 | [3.4](/part3/04-monads-programmers-definition) |
| 余单子 | comonad | 单子的对偶，带 `extract` 与 `duplicate` | [3.7](/part3/07-comonads) |
| F-代数 / F-余代数 | F-algebra / coalgebra | 对象加态射 $F a \to a$ / $a \to F a$ | [3.8](/part3/08-f-algebras) |
| 始代数 / 终余代数 | initial algebra / terminal coalgebra | F-代数范畴的始对象 / F-余代数范畴的终对象 | [3.8](/part3/08-f-algebras) |
| 卡塔态射 | catamorphism | 从始代数出发的唯一同态，即“折叠” | [3.8](/part3/08-f-algebras) |
| 安娜态射 | anamorphism | 到终余代数的唯一同态，即“展开” | [3.8](/part3/08-f-algebras) |
| 不动点 | fixed point | 满足 $F x \cong x$ 的对象 $x$，例如递归类型 | [3.8](/part3/08-f-algebras) |
| 单子的代数 | algebra for a monad | 与单子结构相容的 F-代数 | [3.9](/part3/09-algebras-for-monads) |
| Eilenberg–Moore 范畴 | Eilenberg–Moore category | 单子的全部代数组成的范畴 | [3.9](/part3/09-algebras-for-monads) |

## 高阶主题

| 中文 | English | 一句话解释 | 首次出现 |
|---|---|---|---|
| 端 / 余端 | end / coend | 剖函子的一种“广义极限 / 余极限”，记作 $\int_c$ / $\int^c$ | [3.10](/part3/10-ends-and-coends) |
| 楔形条件 | wedge condition | 端的定义中替代自然性条件的那个交换条件 | [3.10](/part3/10-ends-and-coends) |
| Kan 扩张 | Kan extension | 沿一个函子“最好地”延拓另一个函子的泛构造 | [3.11](/part3/11-kan-extensions) |
| 富集范畴 | enriched category | hom-集换成某个幺半范畴中对象的范畴 | [3.12](/part3/12-enriched-categories) |
| 拓扑斯 | topos | 像集合范畴一样“好”的范畴：笛卡尔闭、有极限、有子对象分类子 | [3.13](/part3/13-topoi) |
| 子对象分类子 | subobject classifier | 推广“特征函数 $A \to \mathtt{Bool}$”的对象 $\Omega$ | [3.13](/part3/13-topoi) |
| Lawvere 理论 | Lawvere theory | 用范畴描述代数结构（运算与等式）的方式 | [3.14](/part3/14-lawvere-theories) |
| 元数 | arity | 一个运算接受的参数个数 | [3.14](/part3/14-lawvere-theories) |
| 双范畴 | bicategory | 复合只在同构意义下结合的“弱” 2-范畴 | [3.15](/part3/15-monads-monoids-and-categories) |

## Lean 4 术语

| 中文 | English | 一句话解释 | 首次出现 |
|---|---|---|---|
| 定义 | definition (`def`) | 给一个值或函数起名字 | [0.1 §3](/guide/lean-for-rustaceans) |
| 定理 | theorem (`theorem`) | 类型为命题的定义；它的值就是证明 | [0.1 §14](/guide/lean-for-rustaceans) |
| 结构体 | structure (`structure`) | 带命名字段的类型，字段可以是证明 | [0.1 §5](/guide/lean-for-rustaceans) |
| 归纳类型 | inductive type (`inductive`) | 由若干构造子定义的类型；≈ Rust 的 enum | [0.1 §6](/guide/lean-for-rustaceans) |
| 构造子 | constructor | 归纳类型的每一种“形状”，如 `some`、`List.cons` | [0.1 §6](/guide/lean-for-rustaceans) |
| 模式匹配 | pattern matching | 按构造子分情况处理值 | [0.1 §7](/guide/lean-for-rustaceans) |
| 结构递归 | structural recursion | 递归调用只作用于参数的“一部分”，因此必然终止 | [0.1 §8](/guide/lean-for-rustaceans) |
| 隐式参数 | implicit argument | 用花括号 `{α : Type}` 声明、由 Lean 自动推断的参数 | [0.1 §9](/guide/lean-for-rustaceans) |
| 实例参数 | instance argument | 用方括号 `[C α]` 声明、由实例解析自动填入的参数 | [0.1 §10](/guide/lean-for-rustaceans) |
| 宇宙 | universe | 类型的类型的层级：`Prop`、`Type`、`Type 1`…… | [0.1 §13](/guide/lean-for-rustaceans) |
| 依值类型 | dependent type | 依赖于值的类型，如 `Vector α n`、`∀ n, P n` | [0.1 §9](/guide/lean-for-rustaceans) |
| 定义相等 | definitional equality | 把两边按定义计算后完全相同；`rfl` 能证明的相等 | [0.1 §14](/guide/lean-for-rustaceans) |
| 函数外延性 | function extensionality | 两个函数在每点取值相同则相等；tactic `funext` | [0.1 §15](/guide/lean-for-rustaceans) |
| 证明项 | proof term | 直接写出的、类型为命题的表达式 | [0.1 §14](/guide/lean-for-rustaceans) |
| 证明策略 | tactic | 在 `by` 之后逐步变换目标来构造证明的指令 | [0.1 §15](/guide/lean-for-rustaceans) |
| 目标 | goal | 当前还需证明的命题，在 Infoview 中显示于 `⊢` 之后 | [0.1 §15](/guide/lean-for-rustaceans) |
| 假设 | hypothesis | 证明中已有的前提，在 Infoview 中显示于 `⊢` 之上 | [0.1 §15](/guide/lean-for-rustaceans) |
| 可判定 | decidable | 可以用算法算出真假的命题；`decide` tactic 的适用对象 | [0.1 §14](/guide/lean-for-rustaceans) |
| 命名空间 | namespace | 给名字加前缀的作用域；≈ Rust 的 mod | [0.1 §11](/guide/lean-for-rustaceans) |
| `do` 记法 | do-notation | 串联单子计算的语法，`←` ≈ Rust 的 `?` | [0.1 §16](/guide/lean-for-rustaceans) |

## 符号速查表

下表列出全书常见的数学记号与 Lean 记号。“Lean 输入”一栏是在 VS Code 或 live.lean-lang.org 中输入该符号的方式：
敲反斜杠、缩写，再敲空格（见 [0.1 §1.5](/guide/lean-for-rustaceans)）。没有填写的符号只出现在数学公式里，不会出现在 Lean 代码中。

### 集合、函数与逻辑

| 符号 | 读法 | 含义 | Lean 输入 |
|---|---|---|---|
| $x \in A$ | x 属于 A | x 是集合 A 的元素 | `∈`：`\in` |
| $x \notin A$ | x 不属于 A | | `∉`：`\notin` |
| $A \subseteq B$ | A 包含于 B | A 是 B 的子集 | `⊆`：`\sub` |
| $\varnothing$ | 空集 | 没有元素的集合 | `∅`：`\empty` |
| $A \times B$ | A 叉 B | 笛卡尔积；Lean 中的积类型 | `×`：`\x` |
| $A + B$，$A \sqcup B$ | A 加 B | 不交并；Lean 中的和类型 `α ⊕ β` | `⊕`：`\oplus` |
| $\lvert A \rvert$ | A 的基数 | 有限集合的元素个数 | |
| $f \colon A \to B$ | f 从 A 到 B | 定义域为 A、陪域为 B 的函数 | `→`：`\to` |
| $x \mapsto e$ | x 映到 e | 匿名函数；Lean 中写 `fun x => e` | `↦`：`\mapsto` |
| $g \circ f$ | g 复合 f，g 在 f 之后 | 先做 f 再做 g | `∘`：`\comp` 或 `\o` |
| $\mathrm{id}_A$ | A 上的恒等 | 恒等函数 / 恒等态射 | `id` |
| $f^{-1}$ | f 的逆 | 反函数 | `⁻¹`：`\inv` |
| $B^A$ | B 的 A 次方 | 从 A 到 B 的函数集合 / 指数对象 | |
| $a \mid b$ | a 整除 b | | `∣`：`\mid` |
| $\le$，$\ge$，$\ne$ | 小于等于，大于等于，不等于 | | `\le`，`\ge`，`\ne` |
| $\wedge$ | 并且 | 合取；Lean 的 `And` | `∧`：`\and` |
| $\vee$ | 或者 | 析取；Lean 的 `Or` | `∨`：`\or` |
| $\neg$ | 非 | 否定；Lean 中 `¬p` 即 `p → False` | `¬`：`\not` |
| $\Rightarrow$ | 蕴涵，推出 | 若……则……；Lean 中写 `→` | `→`：`\to` |
| $\Leftrightarrow$，$\leftrightarrow$ | 当且仅当 | 双向蕴涵；Lean 的 `Iff` | `↔`：`\iff` |
| $\forall$ | 对所有 | 全称量词 | `∀`：`\forall` |
| $\exists$ | 存在 | 存在量词 | `∃`：`\exists` |
| $\exists!$ | 存在唯一 | 见 [0.2 §11](/guide/math-toolkit)；核心库无此记号 | |
| $\top$，$\bot$ | 真，假（底） | Lean 中为 `True`、`False`；本书中 ⊥ 也指不终止的计算 | `\top`，`\bot` |
| $\vdash$ | 推出 | Infoview 中目标的前缀 | `⊢`：`\vdash` |

### 范畴论

| 符号 | 读法 | 含义 | Lean 输入 |
|---|---|---|---|
| $\mathcal{C}$，$\mathcal{D}$ | 范畴 C，范畴 D | 花体字母通常表示范畴 | |
| $\mathbf{Set}$ | 集合范畴 | 对象是集合、态射是函数 | |
| $\mathbf{Cat}$ | 范畴的范畴 | 对象是范畴、态射是函子 | |
| $a \to b$，$a \longrightarrow b$ | 从 a 到 b 的态射 | 本书 Lean 代码中写作 `a ⟶ b` | `⟶`：`\hom` |
| $g \circ f$ | g 在 f 之后 | 范畴中的复合；本书 Lean 代码中写作 `g ⊚ f` | `⊚`：`\oo` |
| $\mathrm{id}_a$ | a 上的恒等态射 | 本书 Lean 代码中写作 `𝟙 a` | `𝟙`：`\b1` |
| $\mathcal{C}(a, b)$ | hom-集 | 从 a 到 b 的所有态射 | |
| $\mathcal{C}^{op}$ | C 的对偶 | 箭头全部反向的范畴 | `ᵒᵖ`：`\op` |
| $a \cong b$ | a 同构于 b | | `≅`：`\iso` |
| $a \times b$，$\pi_1$，$\pi_2$ | 积，投影 | | `\x`，`\pi` |
| $a + b$，$\iota_1$，$\iota_2$ | 余积，内射 | | `\oplus`，`\iota` |
| $0$，$1$ | 始对象，终对象 | 在类型中分别是 `Empty`、`Unit` | |
| $F a$，$F f$ | F 作用在 a / f 上 | 函子作用于对象与态射 | |
| $\alpha \colon F \Rightarrow G$ | 从 F 到 G 的自然变换 | 本书 Lean 代码中写作 `F ⟹ G` | `⟹`：`\==>` |
| $\alpha_a$ | α 在 a 处的分量 | | `\a`，`\_a` 用于下标 |
| $[\mathcal{C}, \mathcal{D}]$，$\mathcal{D}^{\mathcal{C}}$ | 函子范畴 | 从 C 到 D 的函子与自然变换 | |
| $L \dashv R$ | L 左伴随于 R | 伴随 | `⊣`：`\dashv` |
| $\eta$，$\varepsilon$ | eta，epsilon | 伴随的单位与余单位；单子的单位 | `\eta`，`\e` |
| $\mu$ | mu | 单子的乘法（“压平”）$T T \to T$ | `\mu` |
| $\delta$ | delta | 余单子的 duplicate | `\de` |
| $\otimes$ | 张量积 | 幺半范畴的双函子 | `⊗`：`\ox` |
| $\int_c$，$\int^c$ | 端，余端 | | `∫`：`\integral` |
| $\Omega$ | Omega | 子对象分类子 | `Ω`：`\Omega` |
| $\mathrm{Lan}_K F$，$\mathrm{Ran}_K F$ | 左 / 右 Kan 扩张 | | |

### Lean 语法记号

| 符号 | 读法 | 含义 | Lean 输入 |
|---|---|---|---|
| `x : T` | x 的类型是 T | 类型标注 | |
| `:=` | 定义为 | 给出定义或证明 | |
| `fun x => e`，`λ x => e` | 匿名函数 | ≈ Rust 闭包 | `λ`：`\la` |
| `(· + 1)` | 占位符 | `fun x => x + 1` 的简写 | `·`：`\.` |
| `⟨a, b⟩` | 匿名构造子 | 构造结构体、有序对、∃ 与 ∧ 的证明 | `\<`，`\>` |
| `{α : Type}` | 隐式参数 | 由 Lean 推断 | |
| `[Monoid α]` | 实例参数 | 由实例解析填入；≈ trait bound | |
| `@f` | 显式化 | 让 f 的隐式参数都需要手写 | |
| `α × β`，`α ⊕ β` | 积类型，和类型 | `Prod α β`、`Sum α β` | `\x`，`\oplus` |
| `a = b`，`a == b` | 命题相等，布尔相等 | 前者需证明，后者可计算 | |
| `h ▸ e` | 用 h 改写 e | 按等式 h 替换 e 的类型 | `▸`：`\t` |
| `f <$> x` | f 映射到 x 上 | `Functor.map f x` | |
| `x >>= f` | bind | `Monad` 的绑定；≈ `and_then` | |
| `let x ← e` | 从 e 中取出 x | `do` 记法中，≈ Rust 的 `?` | `←`：`\l` |
| `by tac` | 用 tactic 证明 | 进入 tactic 模式 | |
| `#eval`，`#check`，`#guard` | 求值，查看类型，断言 | 编辑器命令 | |
