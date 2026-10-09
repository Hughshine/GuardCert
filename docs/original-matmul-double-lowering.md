# 原 matmul：实际 guarded Clight 执行与 double lowering

2026-10-09 后继把[同参数 candidate model progress](original-matmul-candidate-progress.md)
接到实际 Clight statement。原 C、double 数组、IEEE 运算树、I64 controls、
100×100 global layouts 和 padding=2 均保留。实际 prepared pipeline 返回的
generated body 经 final checker 和 lowering 成功后，用同一 captured M/N/K
执行真实候选，再恢复公开 i/j/k。拒绝从实际 capture exit 执行原 source。

已证结论是：给定原 selected source 的有限正常执行、static bindings 和
真实 pipeline/lowering receipts，完整 guarded statement 有有限正常执行，
最终 memory 与原执行相同，完整 program 的公开 temps 相同。这关闭原
matmul 的 local forward Clight execution。Static metadata 的自动生产、
source-total progress/divergence、selected installation 与 Csem→Asm 仍缺；
新增已安装优化 benchmark 仍为零。

## 接口修补与复用

旧 `FramedNestedClightFor` 的 operand view 只携带 I32 expression evaluation。
Affine compiler 已证明 signed range，但该接口把它丢掉了。只有
`Vint (Int.repr z)` 不能推出 signed I32→I64 cast 的结果是 `Int64.repr z`。
后继 `RangedNestedClightFor` 保留这项已有证据；同一 Loop AST、nested
lowering 结构和 private frame 证明继续使用，kernel 与 optimizer 不改。

| 服务 | 输入／证据 | 已证结论 |
| --- | --- | --- |
| `compile_operands_ranged` | 实际 affine compilation、typed caches 和 bounds | 真实 I32 evaluation，加 signed range |
| `double_long_operand_exact` | ranged operand | 实际 Clight I32→I64 cast 精确 |
| `double_long_affine_execution` | ranged operands、仿射 coefficients/bias | 实际 I64 affine calculation 返回数学值的 `Int64.repr` |
| `double_lower_access_receipt` | actual lowering、global resolution、tensor index、static layout | 实际任意 rank global double lvalue 与八字节 physical location 对应 |
| `double_tensor_instruction_execution` | 同一 INSTR 的真实 memory action、上述 receipts | 实际 `Sassign`、相同 memory action、E0／temp frame |
| `compile_double_tensor_loop_correct` | actual nested lowering receipt、typed caches、同参数 Loop execution | 实际候选 Clight execution 和 private frame |
| `double_matmul_exit_execution` | 精确 private dimensions、public/cached IDs 分离 | 实际 I64 i/j/k 恢复，包括空父域保留子 counters |

I64 地址运算以 CompCert 的模运算证明对应；physical offset 的合法范围单独
来自 tensor index 和 layout span。这里没有假定所有 I64 intermediates 都是
无溢出的数学整数，也没有改变 double 表达式的求值树。Global tensor backend
不假定数据预先可读；真实 model action 生产实际 read/store receipts。

## 原输入上的实际组合

`OriginalMatmulDoubleLowering` 从原 exported AST 和完整 program 建立五项
global layout registry、三 private parameter caches，以及三组 nested scratch
pairs。Capture 的四个 private IDs 和 candidate 的六个 private IDs 均取自
实际 program-wide name pool；scratch check 成功，cache/public ID 分离已证。
Candidate compiler 消费 generator 真正返回的 body，没有另写 i/k/j fixture。

实际生成的 versioned statement 是：

```text
capture original M/N/K, with dependent reads and I64 range gates
if private flag then
    lower(actual final generated body)
    restore original public I64 i/j/k exits
else
    original selected source
```

`original_matmul_guarded_candidate_execution` 复用原 source 的 reached-header
license、safe capture、source entry transport 和 final-candidate model progress。
接受时 private values 精确为实际非负维数，范围为 0..98，candidate 在这些
值下完成；它只改变 fresh temps 和 model 所对应的 memory。Exit restoration
随后恢复原公开 counters：M=0 保留 j/k；M>0、N=0 保留 k；活动路径设置
i=M、j=N、k=K。拒绝时执行的 source entry 是 capture 真正到达的 entry。

该 endpoint 保持所有 `program_temps prog`，而非只检查三个 iterator。
原 finite execution 是语义证明的起点，不在运行时预执行。静态 bindings
仍是显式逻辑输入：实际 factory 必须从 program declarations、scope 和
global-environment 定律生产它们，不能转交 marked C 用户。

## 责任与未完成项

本次重新 fetch 全部 origin refs 后，narrative 最新仍为 `8ce9c8b`，与 main
正文一致。按其三层责任：language 服务交付 ranged casts、实际 tensor
memory execution、private frame 和 public exits；domain 实例消费真实
source/capture、同参数 candidate 与 lowering receipts；kernel 保持原来的
local guarded composition 边界。Local finite theorem 不建立 source-total
progress、divergence 或 contextual closure。

现有 `projected_region_contract` 对任意 program/locals 量化，当前定理则
依赖实际 globals/no-shadow bindings。静态声明检查还不构成该 universal
contract；需要[环境事实的生产与运输](framework-responsibilities.md#实际程序事实与-host-契约的量化差距)，
或证明在旧契约全部环境下适用的对应。该衔接尚未实现。

下一项接入要自动生产 static registry/bindings，把实际 capture/candidate/
fallback 交付给既有 selected host，建立适用的 typing、placement、progress
和 private-resource 义务，再连接 Csem→Asm。其他真实 source、tiling/ISS/
intra-tile/diamond/two-level/unroll-jam 路线和完整成本比较仍在总目标中；
当前 affine output 或 lowering 的限制不缩减验收范围。

## 可复现证据

机器摘要见 [original-matmul-double-lowering.json](original-matmul-double-lowering.json)。
五模块713行，21个实例化审计端点／4 closed，269 reachable sources／7,557
bindings，至多14个继承 globals，全部属于原42-global baseline，无新增公理。
六次成功和22次拒绝／中断证明尝试保留；两次中断的日志明确标记，后继用
tactic timing 定位并修复 cache-view 的不可约末尾 index 分支。

Proof report 为 `build/original-matmul/double-lowering-proof-v1/report.json`；
actual source report 为 `build/original-matmul/source-double-lowering-v1/report.json`。
摘要绑定它们与 native report 的 SHA-256。Native 六项验收接受 identity 和
real Pluto i/k/j；wrong-witness、reverse、malformed、external Err 均拒绝，
全无 alarm，绑定8,328文件。检查器实际运行 Pluto、
final validation 和提取后的 Clight lowering，输出 candidate 与 guarded AST。
它不执行 Clight statement、source/candidate C 或完整 Asm，不能作为新优化
benchmark 或收益／成本结果。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_double_lowering.py --validate
python3 scripts/verify_original_matmul_double_lowering.py --validate
python3 scripts/summarize_original_matmul_double_lowering.py --validate
```
