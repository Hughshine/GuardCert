# 原 matmul：安全条件式 capture、范围检查与固定参数 source model

2026-10-09 后继接通[header 读取许可](original-matmul-header-license.md)：
生成真实 Clight 检查，从原入口捕获 M/N/K，在接受时建立同一组参数下的
source Loop 语义；拒绝后的原 source 可从实际 checked state 执行。
三个新模块 562 行、20 个审计端点，无新增公理。**生成候选的固定参数桥、
candidate Clight、progress 和 selected Csem→Asm 尚未接通，原 corpus 新
optimized cases 仍为零。** 本阶段没有完成整个编译路径。

## 发出的检查是什么

原 global headers 和 i/j/k controls 保持 signed I64。私有模型参数使用 I32，
只有 I64 范围检查通过才转换。对于 reached header，实际代码是：

```text
if (header < 0LL) flag = 0;
else if (98LL < header) flag = 0;
else { cache = (int)header; flag = 1; }
```

随后只有 `flag` 为真且该 cache 为正，才检查下一 header。cache 为零时，
把剩余私有参数填为零并接受，不加载未到达的 headers。拒绝时直接停止
后续检查。Flag 在每条 dispatch 路径上已定义。检查不执行 source body。

| 入口 | 结果 | 私有 M/N/K | 后续读取 |
| --- | --- | --- | --- |
| 96/96/96 | 接受 | 96/96/96 | 三个 headers 都读取 |
| M=0，N/K 未定义 | 接受 | 0/0/0 | 跳过 N/K |
| M=1，N=0，K 未定义 | 接受 | 1/0/0 | 跳过 K |
| M=-1，N/K 未定义 | 拒绝 | 未写参数 | 跳过 N/K |
| M=4294967296 | 拒绝 | 未写 M | 在 I32 截断前拒绝 |

98 来自当前 100×100 布局与 pad=2 的 source/model bridge。本服务支持任意
非负且不大于 `Int.max_signed` 的 limit；本次实际原 matmul 实例选择 98。
它不检查全部 body operands、alias 或任意布局，也未声称自动处理所有 I64 域。

## 三层责任与证明输入

`GuardMemoryLongRangeCapture` 是 language machine 服务：实际 I64 比较
等于 signed 数学比较；接受精确等价于 `0 <= signed(word) <= limit`；
通过后 I64→I32 转换无截断，保留数值。原读取许可与范围接受分别证明。

`GuardMemoryLongCapturePath` 是可复用的依赖式检查库：消费只在父维数正时
要求子读取的 license；证明实际 Clight 执行存在，并证明**所有完成的检查执行**
均为 E0、memory 不变、Normal、flag 已定义，接受产生 cache/entry-value
证书。它只写 flag 和指定 private caches，零路径有精确填充语义。

`GuardMemoryDoubleMatmulCapture` 是 domain 实例：原 matmul 的 source 执行
生产上述 license；接受证书生产三维 nat bounds、私有值与条件式 header
invariant。Language 的 frame/transport 定理将原 source 从原 entry 搬到
checked entry，保留 memory 与 public entry/exit agreement。拒绝可以保留
此前写过的私有 cache，但不能因此改变原 fallback 的公开行为。

实际 exported AST 后继 `OriginalMatmulCapture` 从完整原 program 的
`program_temps` 提议四个 fresh names，用 `private_pool_check` 核对，并证明
这些资源不出现在实际 source 的 temp scope。最终端点
`original_matmul_capture_and_source_model` 连接同一 selected source，提供：

- 实际 capture execution 与 public entry frame；
- 原 source 从 checked state 的 execution 和 public exit agreement；
- 接受时，与实际 captured M/N/K 相同的 **source** `PL.loop_semantics` 参数，
  及原 i/j/k 的精确出口。

端点仍消费 static/layout、实际 ge/locals 的 global bindings，以及给定有限
正常 source execution。入口 header loads 与非负范围已不作为前提。源执行
是证明起点，不在运行时预执行 source。这不自动生产适用于发散 source 的
progress，也不是已完成的 C 用户 factory；static metadata 与 host 义务仍需
最终 producer discharge。

## 原生检查与证据边界

提取同一个实际 Clight capture AST 和 CompCert `Cop.sem_cmp`、`sem_cast`、
`bool_val`、`Mem.alloc/load/store`。Probe 初始化三个真实 memory blocks，
用小型未证明 AST interpreter 执行该检查；global identifier→block lookup
由 probe 提供。因此它是 capture/machine/memory 边界验证，不是整个 Clight
interpreter 的验证，也没有执行原 source、candidate、fallback C 或 Asm。

16 次有读取许可的 capture 执行通过：6 接受、10 拒绝；包括 I64 极值、
±2^32、越界、零路径和 `Vundef` 子 header。另两次缺少许可的用例按预期
产生 undefined-operation 错误，明确不算 runtime fallback。每次 AST hash
相同。每个 reached/accepted header 当前读取三次；负值拒绝读一次，上界
拒绝读两次；正常三维合计九次。这是 probe 中的工作计数，不是完整性能
或收益实验。现有 source/global-block 分离保证 header 的 model stability，
本次 guard 不扫描 body footprint。

## 固定检查点与后续连接

机器摘要见 [original-matmul-capture.json](original-matmul-capture.json)。Proof
audit 跟踪 243 reachable sources、7,332 bindings：20 端点中 4 closed，
其他端点最多 6 个继承 globals，无新增公理；保留 4 成功与 16 失败的证明
尝试。Native audit 绑定 7,625 文件。

- Proof：`build/original-matmul/capture-proof-v1/report.json`，SHA-256
  `2297a0f313c0d9d576efa782a1888d006fbb2eef042b4e8cbb7b84e5a1acb055`。
- Actual source：`build/original-matmul/source-capture-v1/report.json`，SHA-256
  `7d3f42aae61f67be58bfdebb5ce1f0072b04fc77dcae47abbfb247e4fd7401fb`。
- Native：`build/original-matmul/capture-native-check-v1/report.json`，SHA-256
  `749b0d2ece37fc4a1ca768c8c5c735a9e63b15b6526f586cfe1d782a4331eae2`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_capture.py --validate
python3 scripts/verify_original_matmul_capture.py --validate
python3 scripts/summarize_original_matmul_capture.py --validate
```

成功 source/helper/native artifacts 冻结；新证明和干净重现使用 successor
module/checkpoint，失败记录保留。下一步必须消费[真实 prepared pipeline](original-matmul-prepared-pipeline.md)
的实际生成结果，在同一 captured 参数下证明 candidate 对应与进展，再降低
到 double Clight、恢复 public exits 并安装。Wrapped Loop 的存在参数／长度
匹配不能代替该连接；当前 source 固定参数端点也不证明 generated candidate。
