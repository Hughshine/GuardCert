# 2026-10-06：源观察 alias 条件的完整编译入口

接续 main `61edb43` 的 [片段库阶段](research-checkpoint-2026-10-06-observed-pointer.md)。本轮将真实源 load prefix、符号化足迹包络、原 candidate／scan 和保留的后缀接入 normalized Clight source matcher、三类候选、真实程序安装、Csem→Asm 及提取。完整目标继续活动；一般 affine pointer 域、共享 fallback、性能和作者负担对照仍未完成。

## 当前入口与责任

实际入口为 [compile_preserving_observed_pointer](../prototype/interface/ClightObservedPointerCompiler.v)，correctness 端点是 `ClightObservedPointerCompiler.compile_preserving_observed_pointer_correct`，结论为 Csem→Asm backward simulation。source 经 SimplExpr／SimplLocals，proposer 仍用原 `pointer_preserving_request`；mapped、schedule generation 后重新核对、tiling 都消费原 verified candidate／dependence checker。

| 提供方 | 新工作与复用 |
| --- | --- |
| 框架 | kernel 没有修改，继续消费同一 guard／conditional preservation 证书；未加入 Clight、pointer 或 polyhedral 语义 |
| Clight 语言库 | [SequenceContracts](../prototype/interface/ClightSequenceContracts.v) 运输真实序列重组、scope、公开 temps 和 memory；保留后缀实际 store。[SequenceProgressSelector](../prototype/interface/ClightSequenceProgressSelector.v) 组合已有 framed 小步协议，证明 prefix＋loop＋suffix 的 placement；复用 private pool、globalenv、continuation、程序 simulation 和后端 |
| 优化／domain 方 | [ObservedPointerSyntax](../prototype/interface/ClightObservedPointerSyntax.v) 核对类型／属性完整的 normalized AST；[ObservedPointerCandidates](../prototype/interface/ClightObservedPointerCandidates.v) 连接原三类 checker、checked source profiles 与新 target。receipt、全 footprint 包络、实际 Boolean 编码与 C_opt 复用前一阶段及原 domain 库 |

最难连接有实际运行的反馈：第一版虽然证明了 prefix＋loop＋suffix contract，旧 source-progress classifier 却只接受根部 loop，实际程序因此没有安装快捷条件。新序列 checker 由已有协议证明 sound；没有假定 source progress，也没有弱化原 host。观察许可仍来自普通源读取，不能由 `p+k` capability 推出 raw p weak-valid；全部访问覆盖仍来自实际 source footprint 与包络桥接。

## 证明与提取

`make interface-observed-pointer-proof` 通过：67 个公开端点（语言 32／domain 35），502 项实际 user closure，849 份源码摘要。语言端点不超出 CompCert 的 35 项基线；完整 domain／compiler 端点继承原 PolCert/VPL 的七项假设，没有额外全局公理。不是从完整编译器中消除了这七项假设。

本轮逐项编译新增／变更模块及必要依赖，没有声称 clean rebuild 整个 CompCert 或全部 502 项。audit 自身不运行 extraction 或 native；下面的 build／运行报告另行绑定。

| 产物 | SHA-256 |
| --- | --- |
| `build/interface-observed-pointer/report.json` | `7f4a90af3a80a0f32d38817b97f363d4bf24f6d16718a6bf8f9a7bbf6ede9e3f` |
| `build/compcert-observed-pointer/.guard-build.json` | `af9553b02dab8f2d08ff2e93e0e64528976bd11e7a8ad7256e417e77a6d52937` |
| 实际 extracted `build/compcert-observed-pointer/ccomp` | `67d716daa836be1f555b545fd91dbe647050c1c65fb200832e95f723eac74c93` |
| `build/native-interface-observed-pointer/report.json` | `b1101ce3887cd67a3fa6b85e278c98970b2311644939a84baf0cbbc694c44d15` |
| `build/native-interface-observed-pointer/runtime-path-report.json` | `a968d518d6dd284a28af9223c1a9ac1b0c9e7b3486e5665297574580153c52fd` |
| `build/interface-observed-pointer/validation.json` | `6c81c042af1c5ff5f8f8fdd938fa539a3e4cac25ccebc1be7eee2c5789ef4a97` |

工具链按 [lock](../toolchain.lock.json)：CompCert v3.18 commit `14d616046360a0b2611ebdfc2f98368af402e1f7`、Rocq／Stdlib 9.2.0、OCaml 4.14.1。CompCert tag 的 VERSION 文件仍写 3.17，锁定依据是实际 tag／commit。

## 原生与路径验收

[完整 C fixture](../examples/native_interface_observed_pointer.c) 含七个真实函数、一／二／三维源、分组和条件包围、缺失／破坏观察的拒绝案例。每个配置执行同一组 376 次调用，对照独立 modular word 模型与 GCC `-O0 -fwrapv`：所有两份 4096 单元 buffer、公开 i／j／k、原 prefix 值及外围 context／后缀真实 store 都要保持。实际重叠源与无 guard 的 interchange 候选存在输出反例，回退具有必要性。

最终十五个配置全部通过，共 5,640 次配置内调用，唯一源输入为同一组 376 次。包括 direct 的一／二／三维候选、schedule 生成／重新核对、`2×3` 和 `17×13` 分块，以及无效坐标、资源限制、错误证书、缺失和损坏提案的静态拒绝。后五种输出保持源程序，未安装快捷条件或扫描候选。

首轮八个配置通过，`tile-2-3` 编译超过原 600 秒预算而失败；原日志和绑定的 partial 产物保留，不能将首轮称为全矩阵通过。恢复时重新执行这八份二进制并核对所有摘要、AST 和输出；另外七个配置在本轮编译并执行。新编译使用显式 1800 秒诊断预算，超时仍失败；没有删除分块案例或放宽输出／guard 检查。完整报告标明八份旧产物重执行与七份新编译，`validate_interface_observed_pointer.py --runtime-paths` 绑定完整 native／十探针及其来源通过。这不是本轮重新编译全部十五配置，也不是 clean rebuild 或受控性能测量。

源 fixture SHA-256 为 `bb62918974f0d39c88b5bcd578cf4636d3969f0638c76b7ab7326361c75b992b`；审计脚本为 `36891498ee7e9fa090d5ced9ed0fb64238faf52c5bfed81689e19e51dfcfd6af`，最终 native 脚本为 `07eaedad33a496d95d86f4700d8a68a57ed97c84078d518e478a9bbb404aba09`。恢复的原八配置 driver 摘要与 archive 在 partial 来源报告中记录，不能将它们重标为最终 driver 新编译的输出。

十个 linked-machine 探针已通过：direct interchange 和 schedule interchange 各有五种入口。实际地址比较分类绑定 disassembly、原 p／q operands、GDB 命令／日志与二进制摘要；硬件观察点确认候选或源的真实写入顺序。

| 每个入口的案例 | base 比较次数 | scan 地址比较次数 | 结果 |
| --- | ---: | ---: | --- |
| 同 base／包络分离 | 2 | 0 | 候选 interchange |
| 包络重叠 | 1 | 112 | scan 后源顺序 |
| 不同分配／实际分离 | 1 | 32 | scan 后候选顺序 |
| 移位 base／实际 alias | 1 | 32 | scan 后源顺序 |
| 源条件分支为空且 p／q 为 null | 0 | 0 | 原空路径，无新增读取／比较 |

这些是 fixture／x86_64 的功能路径证据，不是一般机器 probe 分类定理，也没有计时。原 private-scan 和参数化 readonly 的已有报告／源码／compiler／二进制绑定继续通过（38 端点／15 配置／四探针／三上下文配置；29 端点／134 配置／十探针）；本轮没有重跑这些旧 native suites。

## 下一项和评审吸收

同 base 包络分离是保守充分条件；不同 base 即便实际分离也继续原 scan。当前 source package 是稳定寄存器 counts、非负参数范围和受限矩形访问，不能与另一 pass 的非矩形／loaded-bound 能力拼成一般 pointer polyhedron。

实际二维 direct fixture 有 13 份原 scan AST，接受时保留两个对称访问对。下一项优先证明并安装共享 fallback；临时 Rocq 草案已验证正常 direct-tree 执行到既有共享控制的转换、原 candidate 证书复用和一个 Csem→Asm 端点，在同环境核对后不超出 35＋7 既有假设。但它没有成为公开 source／提取／运行配置，未计入本阶段 67 个审计端点或 native 能力。保持同一 D／P／candidate、prefix receipt、覆盖和保守拒绝，再验证新入口及最终代码规模；性能仍按 [正式方案](native-performance-plan.md) 在无并发证明／构建时测量。一般 affine 域、依赖 preload 和同例作者负担比较继续列在 [当前计划](current-work-plan.md)。

本轮再次 fetch 三个评审分支，保持 `f7936299fa6272fbf50db6b94a1bd0333808ea09`／`9673381676e18ed0afbc6114e0a62bea9c48002c`／`3e9f0080def8c029cceedbd35184b4de7b8b96bc`。方向和验收继续进入 [责任矩阵](framework-responsibilities.md)；没有新增评审意见，不从正确性计数主张性能、证明负担收益或文献新颖性。
