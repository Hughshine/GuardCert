# CGO 2017 Figure 2：源问题与当前覆盖

2026-10-06。按 narrative `226ba94`，先选择一个具体源例，而不是把若干独立 fixtures 的能力
相加称为 OLO 已覆盖。本文的参照是论文 Figure 1／2 的 NPB BT motivating excerpt，
不把该 excerpt 的测试称为完整 benchmark。

论文的源有三层循环，前两层的上界分别由两个 grid word 加一得到，第三层长度固定为五。
相关前提包括读取的稳定性、控制表达式不溢出、维度界和数组分离；Figure 2 将逐位置假设
概括成区域入口条件。§6 另要求按实际可达域安排 preload，并处理检查算术的回绕。
[作者 PDF，Figures 1–2、§§5–6](https://pollylabs.org/publications/grosser-2017-Optimistic-Loop-Optimization.pdf)

## 适配与证据边界

[独立 C 适配](../examples/olo_figure2_adapted.c)保留两个重复 loaded bounds、各自的 `+1`、
三层循环和第五维分量的五次迭代。为了匹配当前 Mint32 body 服务，输出改成固定 16×16×5
布局的 flat `int*`，实际 body 是 `row+column+component` 的 store。论文 excerpt 没有给出
完整计算 body；因此这个版本用于源覆盖和 guard 需求核对，不支持原 kernel 的性能结论。

没有把第二 bound 提前手动缓存，也没有将它改成函数参数。这样的改写会消除 alias 改变
后续 header 的行为，不能拿来验收原 loaded-source 需求。内存 layout 的 flat 适配也不算
已证明 C 多维对象恢复；逻辑维度界与 CompCert 物理权限继续分开。

[运行／绑定检查](../scripts/native_olo_figure2.py)比较逐单元 word 模型、GCC `-fwrapv` 参考和
提取编译器的 disabled／interchange 输出。它还要求 `bt_excerpt` 两份 emitted-Clight body 完全相同，
仍是三层原循环，明确记录 `optimizer_coverage = not-supported`。
输入包含 shape 与 output 自别名、写到后续 shape word、只有一个 shape word 的空外层、
根 `+1` 回绕后的空域，以及内层为空的 null output。合法完成仅证明原程序行为被保留。
本轮两个模式共 16 次 native 调用与绑定复核通过；三层 body 完全相同，没有安装候选。
结果详见 [当前阶段报告](research-checkpoint-2026-10-06-loaded-affine-reduced.md)。

## 按义务记录差距

| 具体需求 | 当前可复用设施 | 此源尚缺什么／归因 |
| --- | --- | --- |
| 根 header 的 load＋1 | 新 signed-expression capture、raw observation／computed cache 对应、generic body-prefix／cached-source transport 和 checked affine numeric site | 可运行 main descriptor 仍只接直接 `i<*limit`；新服务的真实 body stability scan、entry relation、factory／typed host 尚未接入，属于 domain／frontend 与语言安装证明缺口 |
| 在外层可达后读取第二 bound | 两观察 dependent prefix、旧 dual-loaded 有界矩形、源许可运输 | recursive child decoder 当前要求稳定 temp affine bounds；不能把这些旧实例当作该三层源已经支持，属于 domain／源覆盖缺口 |
| 写入可能改变两个观察 | 实际写 trace coverage、byte separation、接受后 cached-source bridge | 当前 recursive main 只稳定一个根观察；需要将多个依赖观察的服务接到同一三层 package |
| 第三层五次迭代与实际 body | 当前 canonical arbitrary-finite child depth、Mint32 多操作 body、依赖 checker | 深度本身已有一般证明；适配 body 是新 store，原 BT 计算并未建模或证明 |
| 整数／逻辑维度与物理地址 | numeric/profile 编码、affine math domain、window locations／capabilities | flat adapter 的 window 不代替原多维 delinearization／维度证书；须明确取舍或加入恢复证据 |
| 由前提生成紧凑入口条件 | affine 包络编码、同许可基址的物理分离、short-circuit／保守拒绝、当前 fact transport | 尚无此例的 compact guard；数学 endpoint 非空／非重叠不自动许可真实 pointer comparison，属于条件算法与语言证明缺口 |
| repeated rewrite／完整程序 | 当前 materialized certificate、region progress／placement、Csem→Asm | 本 source 没有 accepted site，不能用 host 的一般定理推断其优化已经安装 |
| 可用性与人工工作 | 自动 source/candidate 提案、独立 validator、原生 artifact binding | 需要记录 kernel 接入元数据、实际接受率、guard 与完整运行成本；本例没有这些结果 |

这些差距不能统称为“因为做 verification”。其中直接 load＋1 和 loaded child 首先是当前
source grammar／adapter 的缺口；如何安全把它们接到已有 proof chain 仍是必须完成的具体工作。
不同 pointer 语义确实限制某些快速检查，但也不免除寻找有证明的充分条件或观察许可的责任。

## 当前简化工作的作用与局限

本轮 fact transport 证明 numeric／first-path 事实仅依赖受保护的早先坐标与参数；
未来 child controls 可以未定义或在扫描中改变。稳定性接受后的 alias 检查因此不再重复初始化／
验证相同 first path 和 numeric 条件。它复用旧 candidate P 和语言 host，属于已接受事实下的
residualization；没有自动解出此例的 parameter condition，也没有消除 pointwise stability work。

下一步分别推进：已支持源的 affine write-vs-observation 紧凑充分条件；以及本例的
checked load-expression root 和 dependent loaded child 覆盖。每个新条件需证明检查安全、
接受可靠性和原入口／checked-entry 运输。继续保留安全 scan／refusal，允许更强条件缩小接受域，
并单独测量这项代价。

[Expression-header 后继](research-checkpoint-2026-10-06-expression-headers.md)已关闭 capture、
generic source prefix／cache transport 和第一 numeric 检查阶段的语言服务缺口。它区分
raw=2 与 cache=3，并用真实 alias 源证明提前停止；另证 `INT_MAX+1` 的实际空域检查。
这些服务尚未被提取编译器消费，不能更新本例的 `not-supported` 结果。原表达式的数学
non-overflow 与 cached-word 数值域也保持不同义务，具体 HEADER／body-preservation／coverage
参数必须由完整 domain 实例填入。


[Loaded＋offset 完整后继](research-checkpoint-2026-10-06-loaded-offset-affine.md)已在真实 C 上
接通根 `load + signed constant` 的稳定性 scan、候选／factory／host、Csem→Asm 和提取运行。
其 native 三层例中的 child 仍是稳定 temp 上的 affine expression。此进展消除根表达式这一项
接入缺口，但不是本页 Figure 2 探针的优化验收；第二 loaded child 的层次 receipt／安全 capture
仍未实现。原 16 调用 coverage 报告保持 `not-supported`，没有借新例改写旧证据。


## 后继语言服务：原 coverage 结果仍保持

[第二 loaded header 阶段](research-checkpoint-2026-10-06-nested-headers.md)已证明 outer-active
才读取 child 的 ordered capture、保持真实 memory 的 inner prefix、保护全部 observations 后的
两层缓存源运输，以及从 captured words 许可旧 numeric probe。`shape[1]+delta` 的 actual
Mint32 read／raw snapshot 定律已提供；active outer／empty indexed child、changing-bound 原源
和相邻 word store 的真实 Clight fixtures 单列。

这些服务没有改变 coverage producer、factory 或 compiler。本文原 `not-supported` 报告和
16 次原生行为对照保持；没有新增本例的 native 优化接受。下一项仍是 actual child 访问许可／
joint scan、canonical model（含第三层原 `<5`）的 projected transport、真正原 AST 的安装和
完整提取运行。不将 generic service 参数或手动 cached model 当作此源已被 optimizer 覆盖。
