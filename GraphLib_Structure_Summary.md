# GraphLib 结构与内容梳理

本文档梳理当前工作区 `/Users/yzll/GraphAlgorithms_wx` 下 `GraphLib` Lean 4 项目的结构、模块内容、完成度与构建状态。

## 1. 项目定位

`GraphLib` 是一个基于 Lean 4 与 Mathlib 的形式化图论与图算法库。README 中给出的目标是覆盖图论结构、标准定理以及图算法实现与证明。

项目的核心设计与 Mathlib 内置图结构不同：`GraphLib` 显式携带顶点集和边集，使用 `Set` 表达图的顶点与边，从而更贴近教材和算法中的动态图操作，例如删点、删边、诱导子图、收缩、minor 等。

当前项目更接近早期框架阶段：一部分基础图结构和有限性 API 已经较完整；很多理论、算法和数据结构模块还是占位；若干文件包含 `sorry`、不完整定义或导入路径错误。

## 2. 工程元信息

| 文件 | 内容 |
|---|---|
| `lakefile.toml` | Lake 项目配置，项目名 `GraphLib`，版本 `0.1.0`，默认目标 `GraphLib` |
| `lean-toolchain` | 固定 Lean 工具链版本 |
| `lake-manifest.json` | 依赖锁定文件 |
| `README.md` | 项目目标、路线图与构建方式 |
| `LICENSE` | Apache 2.0 |
| `docs/index.html` | 文档目录文件 |

`lakefile.toml` 中依赖：

| 依赖 | scope |
|---|---|
| `mathlib` | `leanprover-community` |
| `cslib` | `leanprover` |

Lean 选项包括：

| 选项 | 值或作用 |
|---|---|
| `pp.unicode.fun = true` | pretty print 使用 `fun a ↦ b` |
| `autoImplicit = false` | 关闭自动隐式参数 |
| `relaxedAutoImplicit = false` | 关闭宽松自动隐式参数 |
| `weak.linter.mathlibStandardSet = true` | 启用较弱的 Mathlib 风格检查 |
| `maxSynthPendingDepth = 3` | 限制类型类合成深度 |

## 3. 顶层入口

### `GraphLib.lean`

顶层入口文件，当前导入：

| 类别 | 导入 |
|---|---|
| 图核心 | `GraphLib.Graph.Basic` |
| 理论聚合 | `GraphLib.Theory.Basic` |
| Walks | `GraphLib.Theory.Walks.Basic` |
| Trees | `GraphLib.Theory.Trees.Basic` |
| Connectivity | `GraphLib.Theory.Connectivity.Basic` |
| Spectral | `GraphLib.Theory.Spectral.Basic` |
| Matching | `GraphLib.Theory.Matching.Basic` |
| Coloring | `GraphLib.Theory.Coloring.Basic` |
| Minors | `GraphLib.Theory.Minors.Basic` |
| Embeddings | `GraphLib.Theory.Embeddings.Basic` |
| Algorithms | `GraphLib.Algorithms.*` |
| DataStructures | `GraphLib.DataStructures.UnionFind.Basic` |

重要问题：

| 问题 | 说明 |
|---|---|
| 缺失导入 | `GraphLib.Theory.Walks.Basic` 当前不存在，仓库里实际是 `GraphLib/Theory/Structures/*` |
| 图核心导出不全 | 顶层只导入 `GraphLib.Graph.Basic`，没有导入 `GraphLib.Graph.Finite`、`Degree`、`Subgraph`、`Graphs` |
| 理论结构未聚合 | `GraphLib.Theory.Basic` 目前只是占位文件，没有导入 `Theory/Structures` 下的实现 |

## 4. 目录总览

```text
GraphLib/
├── Graph/
│   ├── Basic.lean
│   ├── Finite.lean
│   ├── Degree.lean
│   ├── Subgraph.lean
│   └── Graphs.lean
├── Theory/
│   ├── Basic.lean
│   ├── Connectivity/Basic.lean
│   ├── Matching/Basic.lean
│   ├── Trees/Basic.lean
│   ├── Spectral/Basic.lean
│   ├── Coloring/Basic.lean
│   ├── Minors/Basic.lean
│   ├── Embeddings/Basic.lean
│   └── Structures/
│       ├── Basic.lean
│       ├── VertexSeq.lean
│       ├── Walk.lean
│       ├── SimpleWalk.lean
│       ├── Forest.lean
│       ├── Tree.lean
│       ├── Eulerian.lean
│       ├── Hamiltonian.lean
│       └── 若干空壳文件
├── Algorithms/
│   ├── Basic.lean
│   ├── Search/Basic.lean
│   ├── ShortestPath/Basic.lean
│   ├── MST/Basic.lean
│   ├── Flow/Basic.lean
│   └── SCC/Basic.lean
└── DataStructures/
    └── UnionFind/Basic.lean
```

当前 `GraphLib` 目录共有 34 个 Lean 文件，约 3261 行。

## 5. `Graph` 核心模块

### 5.1 `GraphLib/Graph/Basic.lean`

这是目前最核心、最完整的基础文件，定义四类图结构和统一记号。

主要结构：

| 名称 | 含义 | 边表示 | 是否允许重边 | 是否允许 loop |
|---|---|---|---|---|
| `Edge α β` | 无向带标签边 | 标签 `β` 加无序端点 `Sym2 α` | 允许，通过标签区分 | 允许 |
| `Arc α β` | 有向带标签边 | 标签 `β` 加有序端点 `α × α` | 允许，通过标签区分 | 允许 |
| `Graph α β` | 一般无向图或多重图 | `Set (Edge α β)` | 允许 | 允许 |
| `SimpleGraph α` | 简单无向图 | `Set (Sym2 α)` | 不允许 | 不允许 |
| `DiGraph α β` | 一般有向图或多重有向图 | `Set (Arc α β)` | 允许 | 允许 |
| `SimpleDiGraph α` | 简单有向图 | `Set (α × α)` | 不允许 | 不允许 |

关键字段：

| 字段 | 说明 |
|---|---|
| `vertexSet` | 顶点集合 |
| `edgeSet` | 边集合 |
| `incidence'` | 每条边的端点都属于顶点集 |
| `loopless'` | 简单图和简单有向图中的无自环约束 |

统一接口：

| 名称 | 作用 |
|---|---|
| `HasVertexSet` | 图类结构的顶点集 typeclass |
| `HasEdgeSet` | 图类结构的边集 typeclass |
| `V(G)` | 顶点集记号 |
| `E(G)` | 边集记号 |

主要 API：

| 定理或定义 | 作用 |
|---|---|
| `SimpleGraph.toGraph` | 将简单图遗忘为一般无向图 |
| `SimpleDiGraph.toDiGraph` | 将简单有向图遗忘为一般有向图 |
| `Graph.incidence` | 用 `V(G)`、`E(G)` 表述一般图端点属于顶点集 |
| `SimpleGraph.incidence` | 简单图端点属于顶点集 |
| `SimpleGraph.loopless` | 简单图边不是对角边 |
| `DiGraph.incidence` | 有向图边的源点和终点属于顶点集 |
| `SimpleDiGraph.incidence` | 简单有向图端点属于顶点集 |
| `SimpleDiGraph.loopless` | 简单有向边源点不等于终点 |

完成度：较完整，是其他模块的基础。

### 5.2 `GraphLib/Graph/Finite.lean`

该文件围绕有限简单图和有限简单有向图，提供有限性实例、`Finset` 视图和边数上界。

主要目标是让用户只需要写 `[Finite V(G)]`，后续自动得到边集有限、`Fintype`、`Finset` 等辅助结构。

主要内容：

| 名称 | 说明 |
|---|---|
| `SimpleGraph.instFiniteEdgeSet` | 有限顶点集推出简单图边集有限 |
| `SimpleDiGraph.instFiniteEdgeSet` | 有限顶点集推出简单有向图边集有限 |
| `SimpleGraph.vertexFinset` | 顶点集的非计算性 `Finset` |
| `SimpleDiGraph.vertexFinset` | 简单有向图顶点 `Finset` |
| `SimpleGraph.edgeFinset` | 边集的非计算性 `Finset` |
| `SimpleDiGraph.edgeFinset` | 简单有向图边集 `Finset` |
| `mem_*` 与 `coe_*` 引理 | 连接 `Finset` 成员关系和原始 `Set` |
| `ncard_vertexSet`、`ncard_edgeSet` | `Set.ncard` 和 `Finset.card` 的对应 |
| `card_edgeFinset_le_card_choose_two` | 简单无向图边数不超过 `choose |V| 2` |
| `card_edgeFinset_le_two_card_choose_two` | 简单有向图边数不超过 `2 * choose |V| 2` |
| `computeVertexFinset` | 可计算版本的顶点 `Finset` |
| `computeEdgeFinset` | 可计算版本的边 `Finset` |
| `compute*_eq_*Finset` | 可计算版本与非计算版本一致 |
| `vertexSet_finite`、`edgeSet_finite` | 从 `[Finite V(G)]` 得到 `Set.Finite` |

完成度：较完整，证明较多，是当前库中完成度最高的文件之一。

### 5.3 `GraphLib/Graph/Subgraph.lean`

定义子图关系和诱导子图。

主要定义：

| 名称 | 说明 |
|---|---|
| `Graph.subgraphOf` | 一般无向图子图关系 |
| `SimpleGraph.subgraphOf` | 简单图子图关系 |
| `DiGraph.subgraphOf` | 有向图子图关系 |
| `SimpleDiGraph.subgraphOf` | 简单有向图子图关系 |
| `Graph.induce` | 在 `S : Set α` 上诱导一般图 |
| `SimpleGraph.induce` | 在 `S` 上诱导简单图 |
| `DiGraph.induce` | 在 `S` 上诱导有向图 |
| `SimpleDiGraph.induce` | 在 `S` 上诱导简单有向图 |
| `GetElem` 实例 | 支持 `G[S]` 形式访问诱导子图 |

设计特点：

| 设计点 | 说明 |
|---|---|
| 诱导顶点集 | 使用 `S ∩ V(G)`，即使 `S` 包含图外顶点也安全 |
| 一般图边比较 | 使用底层 `edgeSet : Set (Edge α β)`，保留重边标签差异 |
| loopless 继承 | 简单图诱导子图的无环性直接继承自原图 |

当前问题：

| 问题 | 说明 |
|---|---|
| 未完成记号 | 文件末尾有 `notation G ≤ H`、`notation G < H`、`notation G \ e`、`notation G - v`，没有右侧展开定义 |

### 5.4 `GraphLib/Graph/Degree.lean`

该文件规划了邻居、关联边、度数、最大最小度等 API，但当前不完整。

已写出的主要概念：

| 名称 | 说明 |
|---|---|
| `Graph.neighborSet` | 一般无向图中与 `v` 共享边且不等于 `v` 的邻居 |
| `SimpleGraph.neighborSet` | 简单图邻居，定义为 `s(u, v) ∈ G.edgeSet` |
| `DiGraph.outNeighborSet` | 有向图出邻居 |
| `DiGraph.inNeighborSet` | 有向图入邻居 |
| `SimpleDiGraph.outNeighborSet` | 简单有向图出邻居 |
| `SimpleDiGraph.inNeighborSet` | 简单有向图入邻居 |
| `Graph.incidenceSet` | 一般图中关联到顶点的边 |
| `SimpleGraph.incidenceSet` | 简单图中关联到顶点的边 |
| `DiGraph.outIncidenceSet` | 源点为 `v` 的有向边 |
| `DiGraph.inIncidenceSet` | 终点为 `v` 的有向边 |
| `degree`、`outDegree`、`inDegree` | 基于 `Set.ncard` 的度数 |
| `maxDegree`、`minDegree` 等 | 使用 `ℕ∞` 表达极值度数 |

当前问题：

| 问题 | 说明 |
|---|---|
| 多个 `neighborFinset` 为 `sorry` | `Graph`、`SimpleGraph`、`DiGraph`、`SimpleDiGraph` 均有未证明或未实现部分 |
| `incidenceFinset` 类型不匹配语义 | 名称是 `Finset`，返回类型却是 `Set` |
| 平均度和邻接未完成 | `SimpleGraph.avgDegree`、`SimpleGraph.adj` 是 `sorry` |
| 存在语法不完整定义 | `def SimpleGraph.inc (G : SimpleGraph α) (e : E(G)) (v : )` 未完成 |
| 多个 notation 只有声明头 | 如 `N(G,v)`、`d(G,v)`、`δ(G)`、`Δ(G)` 等未展开 |

完成度：草稿阶段，不可作为稳定 API。

### 5.5 `GraphLib/Graph/Graphs.lean`

这是典型图族的占位文件。

列出的图族：

| 名称 |
|---|
| `complete_graph` |
| `cycle` |
| `path` |
| `star` |
| `wheel` |
| `grid` |
| `hypercube` |
| `kneser` |
| `complete_bipartite_graph` |
| `berge_graph` |
| `tuttle_graph` |
| `peterson_graph` |
| `product_graph` |
| `sum_graph` |
| `complement` |
| `cayley` |

当前问题：每一项都只有 `def name`，没有类型和实现，属于语法层面的占位草稿。

## 6. `Theory/Structures` 结构理论模块

该目录是当前理论部分最有实质内容的地方，但内部有两个并行方向：

| 路线 | 文件 | 状态 |
|---|---|---|
| 拆分后的实现 | `VertexSeq.lean`、`Walk.lean`、`SimpleWalk.lean` 等 | 结构较清晰，但仍有 `sorry` |
| 旧版或实验性聚合 | `Structures/Basic.lean` | 内容大量重叠，且包含无法通过的草稿定义 |

### 6.1 `GraphLib/Theory/Structures/VertexSeq.lean`

定义非空顶点序列，是 walk、path、cycle 的底层载体。

核心定义：

| 名称 | 说明 |
|---|---|
| `Snoc` | 支持右追加操作的 typeclass |
| `VertexSeq α` | 非空顶点序列，构造子为 `singleton` 和右扩展 `cons` |
| `length` | 边数意义的长度，单点序列长度为 0 |
| `head` | 第一个顶点 |
| `tail` | 最后一个顶点 |
| `toList` | 转成顶点列表 |
| `dropHead` | 删除第一个顶点，单点时保持不变 |
| `dropTail` | 删除最后一个顶点，单点时保持不变 |
| `append` | 拼接两个非空序列 |
| `reverse` | 反转序列 |
| `prefixUntil` | 到某个顶点首次出现为止的前缀 |
| `suffixFrom` | 从某个顶点首次出现开始的后缀 |
| `map`、`foldl`、`foldr`、`zip` | 函数式操作 |
| `any`、`all` | 谓词聚合 |
| `nodup` | 无重复顶点 |
| `nonstalling` | 相邻顶点不相等 |
| `closed` | 首尾相同 |
| `takeWhile`、`dropWhile` | 按谓词切分 |
| `splitAt` | 按顶点出现切分 |
| `insert` | 在索引处插入顶点 |
| `loopErase` | 去除相邻重复 |
| `cycleErase` | 去除重复顶点导致的绕行 |

主要引理和实例：

| 名称 | 说明 |
|---|---|
| `length_toList` | `toList.length = length + 1` |
| `toList_injective` | `toList` 单射 |
| `Membership` 实例 | 支持 `v ∈ w` |
| `HasSubset` 实例 | 支持顶点序列包含关系 |
| `Append` 实例 | 支持 `++` |
| `length_append`、`tail_append`、`head_append` | 拼接性质 |
| `reverse_append`、`reverse_reverse` | 反转性质 |
| `head_reverse`、`tail_reverse` | 反转交换首尾 |
| `Functor`、`LawfulFunctor` | `VertexSeq` 函子实例 |

当前 `sorry`：

| 位置 | 内容 |
|---|---|
| `mem_append` | 拼接成员关系证明未完 |
| `mem_reverse` | 反转成员关系证明未完 |
| `nodup_nonstalling` | 无重复推出 nonstalling 未完 |
| `loopErase_nonstalling` | `loopErase` 结果 nonstalling 未完 |
| `cycleErase_nodup` | `cycleErase` 结果 nodup 未完 |

完成度：主体设计明确，证明仍需补齐。

### 6.2 `GraphLib/Theory/Structures/Walk.lean`

定义带边标签的非空 walk，镜像 `VertexSeq`，额外携带边序列。

核心定义：

| 名称 | 说明 |
|---|---|
| `Walk α ε` | 顶点和边交替的非空归纳序列 |
| `length` | 边数 |
| `head`、`tail` | 首尾顶点 |
| `toVertexList` | 顶点列表 |
| `toEdgeList` | 边标签列表 |
| `hasEdge`、`∈ₑ` | 边成员关系 |
| `dropHead`、`dropTail` | 删除首尾 |
| `reverse` | 反转 walk |
| `prefixUntil`、`suffixFrom` | 按顶点切分 |
| `mapV`、`mapE` | 分别映射顶点和边 |
| `foldl`、`foldr` | 顶点折叠 |
| `any`、`all` | 顶点谓词聚合 |
| `nodup`、`nonstalling`、`closed` | walk 性质 |
| `takeWhile`、`dropWhile` | 按谓词截取 |
| `loopErase`、`cycleErase` | 删除停顿和绕行 |
| `toVertexSeq` | 遗忘边，转为 `VertexSeq` |
| `edges` | 转成 `List (Edge α ε)` |
| `arcs` | 转成 `List (Arc α ε)` |
| `toGraph` | walk 诱导的一般无向图 |
| `toDiGraph` | walk 诱导的一般有向图 |

主要证明：

| 名称 | 说明 |
|---|---|
| `length_toVertexList` | 顶点列表长度等于 `length + 1` |
| `length_toEdgeList` | 边列表长度等于 `length` |
| `toVertexSeq_*` 系列 | 各类操作与遗忘边映射交换 |
| `toVertexSeq_nodup` | `VertexSeq.nodup` 与 `Walk.nodup` 对应 |
| `toVertexSeq_nonstalling` | nonstalling 对应 |
| `toVertexSeq_closed` | closed 对应 |

完成度：较完整，未在搜索结果中看到 `sorry`，但依赖 `VertexSeq` 中未完成证明。

### 6.3 `GraphLib/Theory/Structures/SimpleWalk.lean`

定义简单 walk，底层是 `VertexSeq` 加上 `nonstalling` 证明。

主要内容：

| 名称 | 说明 |
|---|---|
| `SimpleWalk α` | `{ w : VertexSeq α // w.nonstalling }` |
| `VertexSeq.edges` | 顶点序列中连续顶点形成的无向边列表 |
| `VertexSeq.arcs` | 顶点序列中连续顶点形成的有向边列表 |
| `SimpleWalk.val` | 取底层 `VertexSeq` |
| `SimpleWalk.nonstalling` | 取 nonstalling 证明 |
| `SimpleWalk.toSimpleGraph` | simple walk 诱导的简单无向图 |
| `SimpleWalk.toSimpleDiGraph` | simple walk 诱导的简单有向图 |

完成度：主体完整，围绕 `SimpleGraph` 和 `SimpleDiGraph` 的转换已经实现。

### 6.4 `GraphLib/Theory/Structures/Forest.lean`

定义森林相关谓词。

| 名称 | 说明 |
|---|---|
| `SimpleGraph.Contains` | 图 `G` 包含某个 `SimpleWalk` 的全部顶点和边 |
| `SimpleGraph.IsForest` | 没有闭合、长度至少 3、内部顶点无重复的 simple walk |

完成度：定义层面完成，没有定理。

### 6.5 `GraphLib/Theory/Structures/Tree.lean`

定义树相关谓词。

| 名称 | 说明 |
|---|---|
| `SimpleGraph.IsConnected` | 任意两个图中顶点之间存在被 `G` 包含的 `SimpleWalk` |
| `SimpleGraph.IsTree` | `IsForest ∧ IsConnected` |

完成度：定义层面完成，没有定理。

### 6.6 `GraphLib/Theory/Structures/Eulerian.lean`

定义欧拉 walk 和欧拉回路。

| 名称 | 说明 |
|---|---|
| `Walk.IsEulerian` | walk 中边集合恰好等于图边集，且边无重复 |
| `Walk.IsEulerianCircuit` | Eulerian 且 closed |
| `SimpleWalk.IsEulerian` | 简单图版本 |
| `SimpleWalk.IsEulerianCircuit` | 简单图欧拉回路 |

完成度：定义层面完成，没有判定或定理。

### 6.7 `GraphLib/Theory/Structures/Hamiltonian.lean`

定义哈密顿 walk 和哈密顿 cycle。

| 名称 | 说明 |
|---|---|
| `Walk.IsHamiltonian` | walk 访问的顶点恰好为图顶点集，且顶点无重复 |
| `Walk.IsHamiltonianCycle` | 去掉最后顶点后 Hamiltonian，且 closed，长度至少 3 |
| `SimpleWalk.IsHamiltonian` | 简单图版本 |
| `SimpleWalk.IsHamiltonianCycle` | 简单图哈密顿环 |

完成度：定义层面完成，没有定理。

### 6.8 `GraphLib/Theory/Structures/Basic.lean`

这是一个大型聚合或旧版实验文件，内容与 `VertexSeq.lean`、`Walk.lean` 重叠，但文件顶部包含大量草稿代码。

包含内容：

| 区段 | 内容 |
|---|---|
| 顶部实验区 | `complete`、多种 `Walk`/`SimpleWalk` 方案、`ClosedWalk`、`Path`、`Cycle`、`Trail` 等 |
| 旧版 `VertexSeq` | 重新定义了 `toList`、`length`、`head`、`tail`、`append`、`reverse` 等 |
| `IsWalk` | 图无关的 walk 合法性谓词，要求相邻顶点不同 |
| bundled `Walk` | `def Walk (α) := { w : VertexSeq α // IsWalk w }` |
| Path/Cycle | `IsPath`、`Path`、`toPath`、`IsCycle`、`Cycle` |
| cycle reroot | `rerootCycle` 和 `isCycle_rerootCycle` |

主要问题：

| 问题 | 说明 |
|---|---|
| 类型错误草稿 | 如 `def complete (n : ℕ) : Graph n := sorry` 中 `Graph` 需要两个类型参数 |
| 重复定义 | 文件中同时出现归纳版和结构体版 `Walk`、`SimpleWalk` 草案 |
| 非 Lean 语法 | 如 `fst vertices`、`lst vertices`、`distinct vertices`、`internally distinct vertices` |
| 多处 `sorry` | 顶部转换、disjoint、SimpleTrail 等未完成 |
| 与拆分文件重叠 | 后半部分与 `VertexSeq.lean` 的实现大量相同或相近 |

建议：后续应决定保留拆分版本还是聚合版本。按当前结构看，更适合保留 `VertexSeq.lean`、`Walk.lean`、`SimpleWalk.lean` 等拆分文件，并清理或重写 `Structures/Basic.lean`。

### 6.9 空壳结构文件

以下文件目前只有版权头，没有实际定义：

| 文件 |
|---|
| `Theory/Structures/Cycle.lean` |
| `Theory/Structures/InGraph.lean` |
| `Theory/Structures/InSimpleGraph.lean` |
| `Theory/Structures/Path.lean` |
| `Theory/Structures/SimpleCycle.lean` |
| `Theory/Structures/SimplePath.lean` |
| `Theory/Structures/Trail.lean` |

## 7. 其他理论模块

### 7.1 `GraphLib/Theory/Basic.lean`

理论侧聚合占位文件。文档说明它将聚合 walks、trees、connectivity、spectral、matching、coloring、minors、planarity 等，但当前没有实际导入。

### 7.2 `GraphLib/Theory/Connectivity/Basic.lean`

连通性占位文件。

列出的概念：

| 名称 |
|---|
| `SimpleGraph.cutVertex` |
| `SimpleGraph.cutEdge` |
| `SimpleGraph.vertexCut` |
| `SimpleGraph.edgeCut` |
| `SimpleGraph.boundary` |
| `SimpleGraph.vertexConnectivity` |
| `SimpleGraph.edgeConnectivity` |
| `SimpleGraph.vertexSeparator` |
| `SimpleGraph.edgeSeparator` |
| `SimpleGraph.STvertexCut` |
| `SimpleGraph.STedgeCut` |
| `SimpleGraph.isStronglyConnectedComponent` |
| `SimpleGraph.stronglyConnectedComponents` |
| `SimpleGraph.connected` |

当前问题：这些 `def` 多数没有类型和实现，`SimpleGraph.connected` 只有类型头和 `:=`，未给定义体；记号 `κ(G)`、`κ'(G)`、`∂(G,S)` 也没有展开。

### 7.3 `GraphLib/Theory/Matching/Basic.lean`

匹配理论草稿。

已有内容：

| 名称 | 说明 |
|---|---|
| `Matching (G : Graph α β)` | 匹配结构，字段为 `edges : Set (Edge α β)` 和边端点 disjoint 约束 |
| `Matching.size` | 匹配边数，使用 `M.edges.card` |

规划但未实现：

| 名称 |
|---|
| `Matching.IsMaximal` |
| `Matching.IsMaximum` |
| `Matching.IsPerfect` |
| `Matching.covered` |
| `Path.augmenting` |
| `Path.alternating` |
| `Matching.augment` |
| `Matching.union` |
| `Matching.xor` |

当前问题：

| 问题 | 说明 |
|---|---|
| 导入缺失 | 导入 `GraphLib.Theory.Walks.Basic`，但该路径不存在 |
| 未完成定义 | 多个 `def` 没有类型或实现 |
| 匹配约束可能写错范围 | `disjoint` 当前量化 `e ∈ E(G)` 与 `f ∈ E(G)`，没有限制 `e`、`f` 属于 `M.edges` |

### 7.4 `GraphLib/Theory/Trees/Basic.lean`

占位文件。说明未来放树和森林核心定义以及 Cayley 定理。

注意：真正的 `IsForest` 和 `IsTree` 当前在 `Theory/Structures/Forest.lean` 与 `Theory/Structures/Tree.lean` 中。

### 7.5 `GraphLib/Theory/Spectral/Basic.lean`

占位文件。规划内容包括 Laplacian、Cheeger 不等式、expansion、expander graph。

### 7.6 `GraphLib/Theory/Coloring/Basic.lean`

占位文件。规划内容包括点染色、边染色、色数以及基本上下界。

### 7.7 `GraphLib/Theory/Minors/Basic.lean`

占位文件。规划内容包括边收缩、点收缩、minor 关系、topological minor。

### 7.8 `GraphLib/Theory/Embeddings/Basic.lean`

占位文件。规划内容包括图嵌入、平面图、Euler 公式、Kuratowski 定理、环面和高亏格嵌入。

## 8. 算法模块

`GraphLib/Algorithms` 目前全部是占位文件，没有算法实现和正确性证明。

| 文件 | 规划内容 |
|---|---|
| `Algorithms/Basic.lean` | 算法侧聚合入口 |
| `Algorithms/Search/Basic.lean` | BFS、DFS |
| `Algorithms/ShortestPath/Basic.lean` | Dijkstra、Bellman-Ford、Floyd-Warshall |
| `Algorithms/MST/Basic.lean` | Kruskal、Prim、Boruvka |
| `Algorithms/Flow/Basic.lean` | Ford-Fulkerson、Edmonds-Karp、Push-Relabel、Kyng 近线性最大流 |
| `Algorithms/SCC/Basic.lean` | Tarjan、Kosaraju |

完成度：路线图阶段。

## 9. 数据结构模块

### `GraphLib/DataStructures/UnionFind/Basic.lean`

占位文件。规划内容为并查集、按秩合并和路径压缩。

完成度：路线图阶段。

## 10. 当前构建状态

执行：

```bash
lake build
```

当前失败信息：

```text
error: no such file or directory
  file: /Users/yzll/GraphAlgorithms_wx/GraphLib/Theory/Walks/Basic.lean
```

直接原因是 `GraphLib.lean` 和 `Theory/Matching/Basic.lean` 导入了不存在的 `GraphLib.Theory.Walks.Basic`。

即使修正该导入，后续仍可能遇到这些构建阻塞：

| 文件 | 风险 |
|---|---|
| `Graph/Graphs.lean` | 多个只有名字的 `def`，没有类型或实现 |
| `Graph/Degree.lean` | 未完成定义 `SimpleGraph.inc`，多个 notation 无展开 |
| `Theory/Connectivity/Basic.lean` | 多个只有名字的 `def`，`connected` 未完成 |
| `Theory/Matching/Basic.lean` | 多个只有名字的 `def` |
| `Theory/Structures/Basic.lean` | 含非 Lean 草稿语法和重复定义 |
| `Theory/Structures/VertexSeq.lean` | 多处 `sorry`，若项目禁止 `sorry` 会失败 |

## 11. 完成度分层

### 相对成熟

| 模块 | 说明 |
|---|---|
| `Graph/Basic.lean` | 四类图结构、端点合法性、统一记号 |
| `Graph/Finite.lean` | 有限简单图的 `Finset` API 和边数上界 |
| `Graph/Subgraph.lean` | 子图和诱导子图主体实现 |
| `Theory/Structures/Walk.lean` | 带边 walk 的主体 API |
| `Theory/Structures/SimpleWalk.lean` | simple walk 与图转换 |

### 部分实现

| 模块 | 说明 |
|---|---|
| `Graph/Degree.lean` | 已有概念定义，但未完成和语法残缺较多 |
| `Theory/Structures/VertexSeq.lean` | 主体 API 已有，若干关键证明 `sorry` |
| `Theory/Structures/Forest.lean` | 定义已有，无定理 |
| `Theory/Structures/Tree.lean` | 定义已有，无定理 |
| `Theory/Structures/Eulerian.lean` | 定义已有，无定理 |
| `Theory/Structures/Hamiltonian.lean` | 定义已有，无定理 |
| `Theory/Matching/Basic.lean` | 只有 `Matching` 结构雏形和若干规划项 |

### 占位或草稿

| 模块 | 说明 |
|---|---|
| `Graph/Graphs.lean` | 图族名称列表 |
| `Theory/Basic.lean` | 聚合占位 |
| `Theory/Connectivity/Basic.lean` | 连通性概念列表 |
| `Theory/Trees/Basic.lean` | 占位 |
| `Theory/Spectral/Basic.lean` | 占位 |
| `Theory/Coloring/Basic.lean` | 占位 |
| `Theory/Minors/Basic.lean` | 占位 |
| `Theory/Embeddings/Basic.lean` | 占位 |
| `Algorithms/*` | 全部占位 |
| `DataStructures/UnionFind/Basic.lean` | 占位 |
| `Theory/Structures/Cycle.lean` 等空壳 | 只有版权头 |

## 12. 主要设计脉络

### 12.1 图结构

`GraphLib` 把“图是什么”定义得很显式：

| 层面 | 表达方式 |
|---|---|
| 顶点 | `Set α` |
| 无向一般边 | `Edge α β`，包含标签和 `Sym2 α` 端点 |
| 有向一般边 | `Arc α β`，包含标签和 `α × α` 端点 |
| 简单无向边 | `Sym2 α` |
| 简单有向边 | `α × α` |
| 合法性 | 边的端点必须属于顶点集 |
| 简单性 | 用 `loopless'` 排除自环 |

这样做的好处是：子图、诱导子图、删点删边、收缩等操作可以直接操作集合，形式上接近教材。

### 12.2 Walk 结构

当前有两种 walk 思路：

| 思路 | 文件 | 特点 |
|---|---|---|
| `VertexSeq` 加性质 | `Structures/VertexSeq.lean`、`SimpleWalk.lean` | 简单 walk 是非停顿顶点序列 |
| 带边 walk | `Structures/Walk.lean` | walk 同时携带顶点和边标签 |

这两者互补：`VertexSeq` 适合 simple graph 上的无边标签路径；`Walk α ε` 适合带标签边、多重图、有向图等情形。

### 12.3 有限图 API

`Graph/Finite.lean` 的设计重点是避免用户重复携带有限性证明：

```lean
[Finite V(G)]
```

在该假设下，库希望自动提供：

| 自动得到 | 用途 |
|---|---|
| `Finite G.edgeSet` | 边集有限 |
| `Fintype G.vertexSet` | 可枚举顶点子类型 |
| `Fintype G.edgeSet` | 可枚举边子类型 |
| `vertexFinset` | 顶点 `Finset` |
| `edgeFinset` | 边 `Finset` |
| `Set.Finite` 引理 | 与 Mathlib API 对接 |

### 12.4 路线图范围

README 规划范围很大：

| 方向 | 内容 |
|---|---|
| Walk 与连通性 | walks、paths、cycles、Eulerian walks、components |
| 树 | trees、forests、Cayley 定理 |
| 谱图理论 | Laplacian、Cheeger、expander |
| 匹配 | augmenting paths、Hall、Konig |
| 染色 | proper coloring、chromatic number |
| minors | contractions、minor、topological minor |
| 嵌入和平面性 | planar graphs、Euler formula、Kuratowski |
| 算法 | BFS、DFS、最短路、MST、最大流、SCC、Union-Find |

实际代码目前只实现了这些路线图中的基础骨架。

## 13. 建议的后续整理顺序

1. 修正入口导入  
   将不存在的 `GraphLib.Theory.Walks.Basic` 替换为实际存在的结构模块，或新建 `Theory/Walks/Basic.lean` 作为兼容聚合层。

2. 先让 `lake build` 通过  
   暂时从入口移除明显草稿模块，或补齐最小可编译定义。优先处理 `Graph/Graphs.lean`、`Graph/Degree.lean`、`Theory/Connectivity/Basic.lean`、`Theory/Matching/Basic.lean`、`Theory/Structures/Basic.lean`。

3. 确定 walk 体系  
   在 `Structures/Basic.lean` 与拆分文件之间选择一个主线。建议保留拆分文件，清理 `Basic.lean` 为聚合导入文件。

4. 补齐 `Graph` 聚合层  
   增加 `GraphLib/Graph/Basic.lean` 之外的聚合文件，或在顶层入口导入 `Finite`、`Degree`、`Subgraph`。

5. 完成 `Degree` API  
   明确 `neighborFinset` 所需有限性和可判定性假设，修正 `incidenceFinset` 返回类型，并补齐 `adj`、`inc`、平均度及 notation。

6. 为核心定义补测试或示例  
   使用小图验证 `vertexFinset`、`edgeFinset`、诱导子图、walk 转图等核心 API。

7. 再推进算法模块  
   在核心图结构和 walk/path API 稳定后，再实现 BFS、DFS、MST、最短路等算法及证明。

## 14. 总结

当前 `GraphLib` 已经有清晰的项目愿景和较好的基础结构雏形。`Graph/Basic.lean`、`Graph/Finite.lean`、`Graph/Subgraph.lean` 和部分 `Theory/Structures` 文件体现了项目的主要设计方向：显式集合表示图，分离顶点序列、带边 walk 和简单 walk，并用 Lean 证明有限性、端点合法性和基本结构性质。

但从工程状态看，它还不是一个可直接构建和使用的库。最主要的问题是入口导入缺失文件，多个模块仍是占位草稿，少数文件存在语法未完成内容。下一阶段的关键不是继续扩展算法，而是先统一模块结构、清理草稿、修复构建，再围绕核心 API 补齐证明和示例。
