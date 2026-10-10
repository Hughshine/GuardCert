# 从分片证书到实际整体融合

原 `fusion2` 的整体候选现在通过新 factory 安装到完整程序。Untiled 候选有六个
静态 pieces，tiled 候选有七个；两者的实际 Clight 都将 A、B 写入放进共享循环。
这项交付解决一源语句到多个不同深度片段的执行对应及安装，不完成整个 OLO
条件合成与成本目标。[结果摘要](piece-factory-results.json)绑定证明、native
compiler、原始输入、实际候选、执行观察和安装拒绝测试。

## 优化实现者提供的接口

新 [prepared producer](../adapters/compcert-memory/GuardMemoryDoublePiecePrepared.v)
消费两个不受信任的数据生产接口：

```text
adapt   : parameter intervals -> original source Loop -> raw generated Loop
          -> result candidate Loop
propose : retained checked model -> actual candidate model
          -> option (piece groups * coverage trees)
```

`adapt` 可以失败。`propose` 可以返回 None；返回 Some 也只表示提案可用。
它不返回安装许可证或语义定理。每个 group 对应一个源 instruction，每个 piece
含实际候选 instruction、domain、embed/project 等数据；coverage tree 由 verified
checker 验证。普通 C 使用者提交标注源码和策略，不填写这些数据或证明 callbacks。

`checked_double_piece_prepared_loop`执行以下编译期操作：

1. 用既有数学 Loop guard 编码参数区间，提取实际 source model。
2. 运行 checked phase，保留真实 scheduled/tiled model 与见证。
3. 调用 adapt，使用 source 的 context/vars 提取实际 candidate body。
4. 调用 propose，并对实际 model/candidate 运行 `check_double_piece_model`。
5. 只在 checker 接受后返回候选。提取、适配、提案或检查失败时返回 None。

参数约束已进入两侧实际 extracted domains，所以这个调用的附加 `guards` 为
空列表。Loop environment 与 polyhedral parameter vector 的反序由已证明的
guard/extractor 桥处理，adapter 不另外猜测参数顺序。数学 guard 不是新发射的
runtime condition；其使用前提由语言实例的真实参数值与区间证据建立。

## 一个真实输入的经过

原始输入的核心是两个顺序执行的 nests：

```c
for (long x = 0; x < 100; ++x)
  for (long y = 0; y < 100; ++y)
    A[x+2][y+2] = 1;
for (long x = 0; x < 100; ++x)
  for (long y = 0; y < 100; ++y)
    B[x+2][y+2] = A[x+3][y+2] + A[x+2][y+3];
```

A、B 保持原 `double[105][105]`、`double[104][104]`，初始化、halo、算术树和
完整输出逻辑不变。调度器提出按对角线交错的整体执行，codegen 则产生内部、
边界与单点 pieces。六或七个静态 pieces 要精确覆盖两条源语句的所有动态
instances，不能凭静态语句数量不同而放行，也不能把两个分别分块的 nests
当作整体候选。

分片检查器先验证覆盖／互斥、参数前缀、完整 typed instruction 与 affine
arguments，再将 pieces 重定时到 retained model，最后验证 actual candidate
次序的依赖正确性。源坐标恢复与合法重排是两条不同的证明。

实际最终 Clight 的 A/B 写入共享循环。未修改 assembly/binary 的观察也确认：
原程序先执行 A 的最后一次更新，再执行 B 的第一次更新；两个目标均先执行
B 的第一次更新，再完成 A 的最后一次更新。三种完整程序输出都匹配原 GCC
reference。观察只 watch 两个位置，不宣称计数全部两万次更新，也不主张性能收益。

## 库和语言分别提供什么证明

| 责任 | 实际交付 |
| --- | --- |
| Domain `C_opt` | Checked piece groups 构造完整 point isomorphism；静态 ordinal 拼接、动作与时间对应、实际依赖验证；source/candidate model 执行 iff |
| Domain／语言桥 | 同一 captured parameters 上的完整 tiling/retained phase iff，actual source/candidate Loop 有限执行 iff |
| 语言实例 | 既有 source/Loop、参数值、NonAlias、private cache/frame、实际 machine lowering、公开 iterator exits 与独立 source-region progress |
| Factory | 从真实 source、参数、候选和 checker 结果 discharge region contract；拒绝保留 fallback |
| 语言 host／backend | 在实际当前程序上安装，再接 CompCert，得到 Csem→Asm backward simulation |
| Kernel | 局部 guarded correctness 与证书组合；本次没有修改其接口或定律 |

新 [execution producer](../adapters/compcert-memory/GuardMemoryPieceLiteralDoubleTreeExecution.v)
与 [factory](../prototype/interface/PieceLiteralDoubleTreeFactory.v)消费真正的 checker
结果。全程序 forward simulation 需要已有的独立 source-region progress，本次
直接复用已证明协议；不必为相同源族再要求一份新的 Clight progress 定律。
完整有限 Loop iff 另行证明，不能把它称为所有 Clight/divergence 行为的 iff。

[完整 tiling 服务](../theories/PolCertTilingExecutionOn.v)接收现有已检查 progress
module，而不是重新实例化一个外观相同、类型 brand 不同的 checker。
[实际 Loop 定理](../adapters/compcert-memory/GuardMemoryDoublePieceEquivalence.v)
因此消费当前 retained phase 的真实 tiling checker；两个方向都使用同一参数值。

新的完整 compiler 入口为
`PieceLiteralCombinedDoubleCompiler.compile_selected_piece_literal_combined_double_program`。
它先 normalize selected literals、安装 checked piece regions，再把**实际所得
当前程序**交给原 combined passes。其
`compile_selected_piece_literal_combined_double_program_correct`证明
`Csem.semantics original`到`Asm.semantics compiled`的 backward simulation。
优化生产者不需要受信任；模型、机器、frame/site 与 backend 义务均由实例化证明
承担。源执行是证明起点，不是在运行时先执行原循环。

## 已做的拒绝验证与剩余边界

[实际安装入口测试](piece-policy-results.json)使用同一 formal compiler root 和
只改数据的 native proposer：正确提案安装整体 untiled fusion；None、遗漏片段、
重复片段、错误参数前缀、错误 affine arguments、错误 typed instruction 六种
情形均不安装整体 fusion。七个完整输出匹配。拒绝后旧 passes 仍可优化独立
局部 nests。这些是**编译期提案／检查器拒绝**，没有测试发射代码的 runtime
guard-false 分支。

[Factory 审计](piece-factory.json)覆盖五模块525行／十端点，最多42项既有 globals，
六次编译保留一次失败。[同参数 iff 审计](piece-equivalence.json)覆盖三模块317行／
五端点，最多十二项既有 globals，六次编译保留三次失败。两者无新增 globals、
kernel/host law 或 semantic extraction override。行数包括实例化与重复接线，
不是作者负担减少的度量。Native preflight 因尚未产生 proof report 而拒绝的记录
也保留；没有开始该次 compiler build。

当前 proposer 的启发式处理至多两个 point axes、其 tile/prefix 坐标和已支持的
整数可逆映射。通用 checker 可验证更一般的有效数据，但不等于 native producer
已覆盖全部顺序 PolCert 功能。旧 shape counters 没有计入新 pass；本例通过实际
store ancestry 与执行次序确认安装。

同 compiler 的[完整语料回归](piece-factory-corpus.json)已完成192配置：原例180/186、
两 adaptations 6/6，合计186完整输出匹配。Source/configuration hashes 和 status
与前序完全一致，仅六个既有 frontend 拒绝，无 compiler timeout、link failure
或 native mismatch。独立核对保留本例整体 fusion、fusion10 和 nodep 的原 tiled
形状；全语料输出匹配不作为全部 requested transformations 的支持率。

[七类 contexts／14配置](piece-factory-contexts.json)也全部通过：两个标注位置、
标注与未标注并存、halo 修改与后续读取、外层条件、private pool 不足、公开
iterators、callee 与 caller 的 live temp。两配置各安装两个标注 fusion；混合例
只在标注处安装；公开出口为`100,100`，caller cookie 保持71；private pool 不足
不安装。完整输出分别与这些**已披露的上下文变体**自己的 GCC reference 比较。
这些不替代未修改原始输入的验收，也不宣称支持任意 goto／exits 或 guard-false。

下一具体接线是将 data-only piece producer 接到既有动态 loaded-bound tree 的
capture／frame／progress／factory，验证随输入变化的实际 guard 接受与回退，随后
扩展其他顺序变换。OLO 的 local obligations→有用入口条件 `B⇒A`、safe machine
`G accepts⇒B`、accepted/refused state transport、共享检查与完整成本继续独立
交付。常量源的 private caches 无条件初始化，动态 loaded-bound 的 source-read
许可与 unreached-zero 契约保持原证明，不能套用本例静态精确区间。
