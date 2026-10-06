# 2026-10-06：符号 affine 包络及实际宽度使用者

本阶段后继于 main `5bd8cc5`，继续按 [topdown narrative](topdown/paper-narrative.md) 实现三方责任及困难义务。新增受限包络推导、实际机器编码与检查替换服务，真实参数化 compiler 消费其宽度条件，复用已有候选／依赖证书和完整程序安装。完整研究目标仍活动；footprint scan 的符号替代尚未完成。

## 实际交付与责任

| 交付 | 责任与证明边界 |
| --- | --- |
| [AffineBoxEnvelope.v](../prototype/interface/AffineBoxEnvelope.v)，182 行 | 无语言依赖的 domain 算术服务；按系数符号生成任意有限维盒状域的仿射上下界，覆盖所有点；整数包络分离蕴含值不同。五个审计端点没有全局假设 |
| [ClightAffineEnvelope.v](../prototype/interface/ClightAffineEnvelope.v)，157 行 | Clight 实例证明实际 modular 仿射求值及最终 signed 比较范围，支持负参数 interval；不声称中间运算全无 overflow 或硬件 flags |
| [ClightReadonlyCheckReplacement.v](../prototype/interface/ClightReadonlyCheckReplacement.v)，102 行 | 语言服务复用既有 reachable-test 安全／结果确定性，替换依赖检查链的一个阶段，保持 D／P／candidate 和 local proof；拒绝不执行 suffix |
| [ClightParametricEnvelope.v](../prototype/interface/ClightParametricEnvelope.v)，234 行 | domain 实例证明实际源编码、全部行宽覆盖、实际 Boolean 可用与接受结论，以及接受蕴含旧宽度接受 |
| [ClightParametricEnvelopeGuard.v](../prototype/interface/ClightParametricEnvelopeGuard.v)，65 行 | source-derived D、header／range 的依赖域证据；组合新宽度与真实数组检查；静态编码失败保留旧树 |
| [ClightParametricPreservation.v](../prototype/interface/ClightParametricPreservation.v) 接入 | 实际生成新宽度树；保留 source/model/candidate、scope/progress 和 direct/shared host，接 Csem→Asm |

行数包括定义、实现、证明和审计命令，只用于描述提交规模，不是作者负担或复用收益测量。语言无关 kernel 没有新增 Clight 或 polyhedral 语义。旧候选／局部证明与 compiler host 源文件未修改；实际替换 hook 调用 `preserving_rule_with_check`。

算法与使用示例见 [推导说明](affine-box-condition-derivation.md)。旧一轴宽度检查本来也是符号 endpoint 算法，本阶段没有把它称作 footprint 枚举替代。旧宽度 lowering 成功仍是 selector／局部证书的静态条件，未声称扩大其源选择域。

## 证明、提取和运行

工具链沿用锁定的 CompCert v3.18、Rocq/Stdlib 9.2、OCaml 4.14.1。当前实际入口仍是 `ClightParametricCompiler.compile_preserving_parametric`；完整端点 `_correct` 给出 Csem→Asm backward simulation。

- 29 个审计端点、337 项实际 user 依赖、818 份源码摘要。35 项 CompCert 基线之外仅有原有七项 PolCert/VPL 继承假设：`CoqAddOn.posPr/zPr`、`PedraQBackend.add/isEmpty/pr/t/top`，没有新增全局公理。
- 提取并构建 `build/compcert-readonly-parametric/ccomp`；实际 Clight 已出现三个新宽度比较，`affine_growing` 的 direct/shared interchange 各有三处包络测试。完整 affine fixture 的所有选中函数均检查到新树，未用未改动的旧编译器代替。
- 六份原有 C fixture 与独立模型均未修改。134 个 direct/shared 配置通过，合计 568,298 行输出全部与 GCC `-O0 -fwrapv` 及模型一致；输出行数不是独立调用数。候选包含真实 schedule generation/rechecking、mapped 变化、tiling；错误映射、维数、系数、缺候选、oracle/resource 故障与依赖拒绝保持原验收集合。
- 十个 x86-64/GDB 探针均通过，并绑定该报告的实际二进制和汇编。探针是功能见证，不是形式定理的额外假设，也不是性能测量。

| 函数／入口 `(i,n,m,p)` | 预期及实际前两处观察写入（direct/shared 均通过） |
| --- | --- |
| growing `(0,2,2,0)` | 接受 interchange：`a[20]=44`，然后 `a[1]=8` |
| growing `(2,4,5,1)` | 非零起点回退：`a[41]=82`，然后 `a[60]=118` |
| growing `(0,3,0,0)` | 首行空回退：`a[21]=45`，然后 `a[40]=81` |
| descending `(0,2,5,-1)` | 负行系数／负参数接受：`a[20]=44`，然后 `a[1]=8` |
| descending `(0,3,3,0)` | 末行负宽度回退：`a[1]=8`，然后 `a[20]=44` |

完整数组、多读取及回绕 data 算术、不同布局、偏移、连续替换与外围控制继续由六份 fixture 验收。当前安装仍是正常有限 region，不据这些样例宣称任意无限 pointer fallback 或一般深度源已经实现。

## 当前产物绑定

| 产物 | SHA-256 |
| --- | --- |
| `build/interface-parametric/report.json` | `e478caefeee97e3ae6b608b5f248c83d7966bf72724793c7f7a0f87a1a394fb9` |
| `build/compcert-readonly-parametric/ccomp` | `ca20ec63a72a88b4e05645670969c651f4c101571a3053e1f9cc6b3c7724d7f7` |
| compiler `.guard-build.json` | `ffdd381df4a7c99397f301749f69380adc255731d342bc54d6746808e3d41840` |
| `build/interface-parametric-native/report.json` | `99366d2f151221bfc7404b30a79435077a5228d84c6df0cb599980ae5bf00887` |
| `build/interface-parametric-native/runtime-order-report.json` | `50c7a0222bf51b6b9a5b2f10fa4f5e4a6334ab304f0953ffea201360961af1e8` |

`validate_interface_parametric.py --runtime-order` 已核对入口、源码／脚本／compiler stamp、实际 binary／assembly／Clight／output 和探针绑定。主接口验证继续通过 415 端点／864 摘要、25 配置／40 报告及 40 份原 C／Clight 摘要保持；named 的 40＋8 配置绑定和 private-scan 的 38 端点／15 原生配置／4 探针／3 上下文配置绑定也均通过。

复现：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_interface_polyhedral.py --parametric
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_compiler.py --readonly-parametric
python3 scripts/native_interface_parametric.py --jobs 2
python3 scripts/probe_interface_parametric.py
python3 scripts/validate_interface_parametric.py --runtime-order
```

GDB 需要运行环境允许 ptrace。正式测量尚未进行；本轮不从构建耗时、端点数量或打印的 AST 大小推导收益。

## 最难的位置与下一项

实际语义核对否定了原来的直接 pointer base 快捷检查计划：`p+k` 的 capability 不蕴含 p weak-valid；[Cop.cmp_ptr](../vendor/CompCert/cfrontend/Cop.v) 使用 [Val.cmpu_bool/cmplu_bool](../vendor/CompCert/common/Values.v)，其有效性条件不能省略。因此未来 alias 推导须先获得 source-prefix／placement 的合法观察证据，再证明全部源访问的包络与物理 separation。普通源没有这份证据时保留 scan，不偷加 base-valid 到 D。

下一项可从真实源中已经发生的普通 p/q base 读取开始，证明其 observation receipt，并运输至局部入口；然后仅在已许可比较的路径消费 offset 包络，否则继续原 scan。该方案仍需真实 source/candidate 对应及完整 compiler 安装，不能仅写一个 domain 假设或多一个接口字段算作完成。一般 affine 源与多个依赖 preload、P4 的同版 CompCert 对照、同例作者负担和已有工作比较继续按 [计划](current-work-plan.md) 验收。

本阶段再次 fetch 三个评审分支，均保持 `f793629`／`9673381`／`3e9f008`；无新增意见。完整 SHA 与吸收记录见 [评审整理](review-synthesis-2026-10-05.md)。
