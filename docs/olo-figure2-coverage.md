# CGO 2017 Figure 2：源问题与当前覆盖

2026-10-07 后继：[nested frontend BODY／contexts](nested-frontend-coverage.md)在
既有三层 loaded-header／固定 flat-stride source profile 上验证七类函数，包含
真实多数组读写、dependence、alias、同 allocation 分离 slices、BODY value wrap、
重复 sites 和外围 control。Default profile 为 714 assembly calls；另提出更强
child-count∈[1,2) 前提，同一 checker 接受 chain 的 interchange／tiling，238
assembly calls 验证 fast／fallback。Clight 和 GDB 的分支证据分别报告。

这是已声明 profile 内的能力，不覆盖完整原 BT 的动态 stride／delinearization。
原 16-call `not-supported` report 固定保留；新 source 与报告另列。重新核对
narrative `271f6fc` 后，OLO 仍同时是功能与 usability 参照：guard size、runtime
work 和有用接受域分开验收。当前扫描证明已接通；compact condition、成本、
作者工作及更广 affine source 仍有缺口，不能用调用数量或 verification 解释。

以下为先前固定阶段；其后继待办以本段及最新 checkpoint 为准。

2026-10-07 最新实运行：[actual nested frontend](nested-frontend-native.md)已在既有
Figure 2 适配源实际安装并运行 interchange／tiling；zero-index root 和 prefixed
resets 的执行对应由语言库证明，fallback 保留原 AST。新 Csem→Asm entry 已提取；
75 full assembly calls、16 Clight dispatch calls 与 6 machine probes 单列并通过。
Kernel 未改，三方责任／四条证书链保持。下面旧阶段与原 16-call `not-supported`
报告固定保留其当时范围；当前能力以新 native 报告为准，仍无 compact 条件／
成本／完整 BT layout／作者工作验收，完整目标 active。

2026-10-07 最新后继：[nested guarded candidate／compiler](nested-constant-multi.md)
已连接实际 canonical source→alias guard→candidate→kernel preservation→projected region
contract→typed factory／语言 host→Csem→Asm。Model anchor 及实际 checked-entry frame
由执行 receipt 生产，没有 source/model 语义回调；kernel 不变。三层原 AST 的 host
progress 支持有 fixture。后文阶段记录保留当时边界；新入口的 extraction／实际 C
识别和非空数组非 identity 优化运行仍待验收，原 Figure 2 16-call report 不变。
Narrative 重新 fetch 到 `271f6fc`，正文与 main 一致；三方责任和四条证书链按新文档核对。

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

2026-10-07：[完整 physical guard 后继](nested-constant-physical.md)已从 data-only
原 site 接入 helper 准备与全部 scan inputs，接受导出 canonical Clight 与真实
Loop source；model entry framed 到 actual guard exit。安全域是原源 silent
normal completion。Candidate 跨入口／dependency-alias、typed factory／host
progress-divergence／placement 和新的 frontend／extraction／native 优化安装
仍待完成；本文 16-call 原 coverage 结果不变。

| 具体需求 | 当前可复用设施 | 此源尚缺什么／归因 |
| --- | --- | --- |
| 根 header 的 load＋1 | Loaded-offset compiler 已连接实际 stability scan、factory／host、Csem→Asm 和提取 | 单根接入缺口已关闭；仍须与第二 loaded child 组合，不能改写原 Figure 2 的 `not-supported` 报告 |
| 在外层可达后读取第二 bound | Checked 原 site、ordered capture、numeric、helper 新入口与完整 physical guard 已接通 | Candidate factory 和语言 host 尚待安装；profile 的安全域为原源 silent normal completion |
| 写入可能改变两个观察 | 完整 guard 在原源许可下实际比较，接受保护全部观察并导出 canonical／Loop source；代码使用固定 observer templates | Candidate 跨入口及 dependency/alias 检查、typed host／progress-divergence 接入；局部 endpoints 不证明本例已安装优化 |
| 第三层五次迭代与实际 body | Literal-bound model／permissions 桥及适配 leaf 完整五次原 store／实际检查 fixture 已证明；quantified outer consumer 已接受任意 checked leaf | 完整 active 原 C 接受／回退与候选安装仍待完成；适配 body 不等于原 BT 计算 |
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
当时仍未实现，后继服务见下段。原 16 调用 coverage 报告保持 `not-supported`，没有借
新例改写旧证据。


## 后继语言服务：原 coverage 结果仍保持

[第二 loaded header 阶段](research-checkpoint-2026-10-06-nested-headers.md)已证明 outer-active
才读取 child 的 ordered capture、保持真实 memory 的 inner prefix、保护全部 observations 后的
两层缓存源运输，以及从 captured words 许可旧 numeric probe。`shape[1]+delta` 的 actual
Mint32 read／raw snapshot 定律已提供；active outer／empty indexed child、changing-bound 原源
和相邻 word store 的真实 Clight fixtures 单列。

这些服务没有改变 coverage producer、factory 或 compiler。本文原 `not-supported` 报告和
16 次原生行为对照保持；没有新增本例的 native 优化接受。后继的 BODY 消费者与当前
待连接义务如下；不将 generic service 参数或手动 cached model 当作此源已被 optimizer 覆盖。

[Constant BODY joint scan](constant-body-joint-scan.md)已从原 `<5` BODY permissions
许可写地址与 `shape`、`shape+1` 的实际比较，接受后生产全部观察保持及 inner-prefix
advance。具体适配 leaf 在 `row=column=0` 的完整五次 store 和检查执行已证明，同 block
分离接受、与 headers 重叠拒绝。30 端点审计通过，没有新 compiler 或 native。
下一项是完整 inner/outer 短路扫描、canonical model、真正原 AST 的安装和提取运行；
完整 acceptance、成本与人工工作尚未验收，原 coverage 结果不变。

2026-10-07：[inner scan 后继](constant-joint-inner-scan.md)已将此 BODY 消费者接到
实际 private short-circuit loop，整行接受生产所有 column 的观察保持和下一 outer
prefix。14 端点审计通过；首次拒绝保持 private cursor 为零，空 child 不要求
output/BODY receipts。上述 runtime 内层的证明缺口已关闭，实际 outer loop、完整
模型／安装与本例的新 native 接受仍待完成。原 16 调用 coverage 报告继续保持。

[Outer 后继](constant-joint-outer-scan.md)现已关闭上述实际 outer／所有 rows 的
证明缺口，并填入旧两缓存运输，得到原／缓存源相同出口 temps 和 final memory。
独立 empty outer guard 不要求第二 header／output receipt；empty 源运输不要求
child cache。14 端点／565 依赖审计通过，没有新 fixture、提取或 native。
完整 canonical model、实际 factory／候选／host 和本例的运行接受仍未完成；原
16 调用覆盖结果保持 `not-supported`，紧凑条件与成本／作者工作仍待验收。

[完整 canonical 后继](nested-constant-model.md)现已将双缓存源运输到旧三层
affine AST，消费 checked package 取得实际 memory 上的 Loop source 执行。
12 端点审计通过，leaf quiet/write 和具体循环 frame 由证明内部生产。
原 capture／numeric 输入 producer、原 AST factory／候选／语言安装仍待连接；
本页原 native coverage 与 16 调用保持，不把模型服务当作优化已安装。
