# 仅在接受前提下需要循环进展的宿主设计

这是一项后续设计与验收，尚未提供 Rocq 接口、全局定理或实际编译器。当前已运行的两种宿主及其边界见 [宿主分类](host-capabilities.md)。这个问题不能通过扩大循环模板列表解决。

## 要覆盖的真实行为

现有宏片段宿主先用独立 source progress 将源小步收集为正常完成执行，再调用局部规则并运输 continuation。它支持变化的 loaded bounds，但选中的整个 source 仍需要独立进展。若只有 `D∧P` 能保证源有限，guard 拒绝后的源可能无限，该证明路线不能直接消费此规则。

一个最小 Clight／Csem 验收例子是普通 unsigned word：

```c
unsigned i = start;
for (; i != *bound; ++i)
  *out = i + 2U;
```

候选将 bound 缓存一次，并保持循环 body。接受前提包括读取稳定：活动 store 与 bound word 分离。非 alias 时固定目标在 unsigned 单位递增下可到达；候选与源需要保留实际写入、出口 i、完整 memory 及所有原 temps。

当 `out==bound` 且入口 start=0、bound=2 时，每轮 body 将 bound 写为当前 i+2，增量后的 i 与 bound 的模距离始终为 1。这个具体 source 在 CompCert 的 unsigned 模运算下持续运行；检查应拒绝并保留原循环。这里需要覆盖完整 source 的发散，不能用“无限外围中的有限头部 rewrite”代替。

## 不改变已有语言无关职责

使用者仍提交 source、candidate、condition、D／P 与局部证明，选择位置和遍历算法。语言实例负责实际表达式、内存动作、检查／分派和全局宿主定律。核不需要理解整数上界或 alias。

需要加强的是语言宿主的进入与进展协议：检查安全的 D 不能只由 source 正常完成取得；source 的进展只能在 P 成立的分支要求。拒绝分支必须回到原小步语义，覆盖有限执行、无限执行、控制出口和原有未定义行为的定理边界。

| 候选证明义务 | 与现有宏宿主的差异 |
| --- | --- |
| 有限源前缀足以建立 D | 不需要等待整个 source 完成；初始实例只使用无事件的头部／首次 store 前缀 |
| 条件可达安全、完成、只读、接受蕴含 P | 继续使用原只读条件证书；不能在 D 偷放稳定性或终止性 |
| P 下的源执行不变式与进展 | rank 可以依赖接受后建立的稳定参数；没有要求拒绝分支满足它 |
| P 下的局部对应与公开出口 | 可先用条件性有限执行等价；若候选也可能无限，则另需覆盖无限行为的局部模拟 |
| 拒绝分支的实际 prefix 运输 | 目标原片段追上用于证明的源前缀，再回到相同 source 小步与 continuation |
| 实际程序的模拟 | 要处理检查前、检查完成后、接受和拒绝的状态关系，不能只证终止 big-step |

前缀是证明见证。运行时仍只执行 guard 和选择的一份片段，没有先运行 source 以询问检查域。拒绝分支的 prefix 运输是两个程序执行之间的对应，不是将原片段在目标中执行两次。

## 原型先验证的证明路线

先限制为 quiet 单词写入和短的只读 guard。小步宿主收集有限头部／首次 store 的见证，建立入口中读取与比较的定义性；这段收集有自身有限度量，与整个循环的 rank 分开。

检查拒绝后，目标执行实际原片段的同一前缀并恢复原 pc／memory／原 temps 的关系，随后复用原语义。检查接受后，使用 P 下的 source invariant 与 rank，再复用局部等价、private scope 和 continuation 桥接。状态关系还须显式处理已经收集的 source 前缀和新增 private temps；不能仅给现有 `region_progress` 加一个 Boolean 字段便宣称完成。

这条路线仍需在 Rocq 中证明：是否能直接扩展当前 forward simulation 宿主，以及有限 prefix／有条件 rank 的具体记录结构，要由最小实例检验后固定。若改用仅针对安全 source 行为的证明，必须另提供它到 CompCert 完整行为 refinement 的桥；不能静默弱化现有全程序结论。

## 验收标准

1. 同一完整循环规则实际插入 guard、缓存候选和原循环回退，连到 Csem→Asm；不只改循环头。
2. 原生有限输入覆盖普通分离、同对象不同 word、bound=0 与 null out、unsigned 边界，以及所有原 counter／word 出口。
3. `out==bound,bound=2` 的输入不执行原生无限循环；以源／目标的实际无限执行或覆盖它的小步模拟定理证明保留发散，并检查提取产物确实含原回退。
4. 检查读取与 alias 比较的安全来自有限真实前缀，接受后的稳定性与 rank 独立交付；不使用 source completion 或 runtime ghost 查询作为入口假设。
5. 新规则与至少另一条现有 rewrite 在一个完整程序中组合，检查使用每次实际入口；文档明确新增宿主能力和保留的限制。

通过这项验收才可以主张“guard 为快路建立有限实例域，回退保留可能无限的整个 source”。它是完整 [OLO 验收](optimistic-loop-acceptance.md) 中进展能力的补充，与更大布局、廉价足迹、多个依赖 preload 和 affine／tiling 迁移分别跟踪。

该例子的两个机器整数事实 `Int.add i 1 <> Int.add i 2` 与 `Int.add i 2 = Int.add (Int.add i 1) 1` 已在锁定 Rocq／CompCert 工具链中单独编译为闭合证明；这项算术实验没有计入项目端点，也不代替实际 Clight 无限执行和宿主模拟证明。
