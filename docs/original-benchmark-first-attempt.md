# 原始 benchmark：首轮运行与浮点接入边界

2026-10-08。按 narrative `8ce9c8b`，先用固定版本的实际计算定位支持缺口。
本轮尝试了全部 62 个 PolCert baseline C harness 和原 serial NPB BT Class S。
运行结果通过，但 **没有一个案例完成所请求的优化**。这不是完整 corpus 的
配置、效果或成本对齐；原始案例接入仍是[当前计划](current-work-plan.md)的首要任务。

## 实际做了什么

| 输入 | 编译与运行 | 优化证据 | 观察范围 |
| --- | --- | --- | --- |
| PolCert 全部 62 项，upstream smoke tier | disabled／schedule／tile 共 186 次初始编译；180 次原生比较一致，另外六次因两个 harness 初始化被 frontend 拒绝 | 成功的 120 次 active 输出均与 disabled 的 Clight 相同，未调用 pipeline | upstream digest 覆盖所有建模的 scalar 和 array cell；不是完整 C 状态的普遍等价证明 |
| `corcol3`、`pca` 的显式初始化适配 | 六次新的原生比较与原 GCC harness 一致；适配后的 GCC digest 也保持 | 四次 active 输出仍相同，未调用 pipeline | 保留 double 数据、long long 控制与原 kernel，仅折叠静态初始化常量 |
| 原 NPB BT Class S，12×12×12、60 iterations | 每配置完整编译 17 个单元；三配置均通过 NPB 自检，十行数值 norm 与 GCC 一致 | `compute_rhs` 的 11 个 top-level loop 已标注，active Clight 仍相同，未调用 pipeline | 原 NPB 自检及十行数值结果；未做逐内存单元比较 |

补适配后，62 项的三配置都有匹配的建模状态结果；这是初始 180 次加上新的
六次，不能把它写成一次全部成功的原样编译。Active 共有 124 个 case/configuration
对，全部保持 disabled Clight。后来的 BT 脚本复现不重复计为新覆盖。
单次运行时长只作诊断，没有速度收益、guard 成本或统计性能结论。

PolCert 固定到 `ca1ae3199c816594bab9d51eb77309a0d17527aa`，使用该提交
的 `generated_harness.py` 从原 `.loop` 生成 baseline C；不是 PolCert 产生的
优化目标。保留 19 个 saved-best 用过并发的案例；它们也运行本轮三配置。
保留实际 double arrays/scalars、long long counters、原始计算和参数 tier。
特别是 `fusion3` 的 literal 10000×10000 未缩小，该项原生比较通过。
本轮未运行 saved sequential routes 的全部选项、其他 tiers 或与其优化目标的
成本比较。

CGO artifact 固定到 `1b23e28261eb1c161192afa86ab996eb67d65f0c`。
154 个 serial NPB 原始 blobs 已按 Git hash 核对。BT 使用原程序、原
`setparams` 生成的 Class S header 和周围 16 个编译单元；对 `rhs.c` 唯一的
计算源修改是原 `compute_rhs` 中 11 个顶层 loop 外的 pragma pair。脚本检查
去掉这些标注后字节等于原源。缓存保留 Git symlink target blob，构建副本恢复
链接，未修改固定源缓存。

`corcol3` 和 `pca` 的原 harness 含有：

```c
static const long long n = 96;
static double float_n = (double)n;
```

GCC 接受并运行；CompCert frontend 拒绝这个非 compile-time-constant 初始化。
显式适配将第二行改为 `static double float_n = (double)96;`，原 `init_data`
中的重新赋值和 kernel 均保留。两个 diff、原 GCC digest、适配 GCC digest 与
六次 compiler/native 结果分别保存。这是 parser 边界的 harness 适配，
不是一个新验证的 Clight 优化。

## 哪些阶段真的到达了

| 阶段 | 本轮原案例状态 | 对实现的含义 |
| --- | --- | --- |
| 原 C 的 pragma selection 与 CompCert 编译 | 除两个上述初始化外通过；BT 11 个 label 保留 | 类型和实际计算可以进入现有 CompCert 工具链 |
| Conditional source/model producer | 未得到可用请求 | 原 harness 的 I64 控制、全局数组及 F64 运算超出已安装 source family |
| Proposal、phase validation、prepared codegen | 无 pipeline artifacts | 没有调度或分块结果；不能把安全拒绝计为支持 |
| Candidate lowering、guard、factory installation | 原案例没有新 target | 旧 compiler 安全保留原程序，不说明这些案例的优化链已完成 |
| Csem→Asm | 复用既有 selected compiler 的成功返回定理 | 不增加 F64 优化定理；native parsing、assembly／linking 仍在原边界 |
| 效果与完整调用成本 | 未测 | 必须在实际 retained transformation 接通后比较 |

类型差距有源码依据：现有 `GuardMultiTensorAffineRegionCandidate.ml` 的标量
识别要求 `Etempvar`／`Econst_int` 的 `type_int32s`；snapshot syntax／factory
也要求 signed32，既有 layout／guard 路径主要是 `Mint32`。原 harness 则有
I64 控制、global multidimensional array 地址和 double 运算。BT 还需要
inclusive comparisons、非零 starts、loaded global dimensions、多语句和
精确 scalar/public exits。这里是源码核对得到的具体差距，不声称已有完整的
逐 AST refusal 分类器。

## 本轮新增的证明能力

两个新模块共 259 行，沿用原 framework 与真实 CompCert memory：

- [`GuardMemoryValueInstr.v`](../adapters/compcert-memory/GuardMemoryValueInstr.v)
  将一个显式 reads／write footprint 的 value computation 参数化，实例化
  PolCert 的 `INSTR`。计算只能看到显式 loaded values 和参数。
- [`GuardMemoryDoubleValue.v`](../adapters/compcert-memory/GuardMemoryDoubleValue.v)
  提供闭合的 double 实例，支持 bit constants、loaded operands、加减乘除和
  negate，直接使用 CompCert `Float` 与 `Cop` 语义。

它复用任意 memory chunk 的既有 independent-footprint reorder 证明：
分离的动作可交换，因而每个动作读到相同 operands、执行相同表达式树。
这不要求浮点加法结合律，也不把浮点语义当作实数。对 matmul，未来调度必须
保留每个输出的依赖顺序；这个模块并未许可 reassociation、FMA 或任意并行归约。
控制／地址的 no-wrap 条件仍单独证明。

独立审计查询五个端点，绑定 114 个 reachable sources 和 256 个文件；
每个端点最多继承五个已有 globals，未加入公理。`MEMORY_VALUE_CODE` 的
`Parameter` 是模块签名，实际 `DoubleMemoryValue` 以定义实例化它，不是
留给源码用户的 semantic callback。

当前表达式定理的方向严格是：**模型求值 + typed operand evaluation receipts
+ emitted code → 实际 Clight expression 求值**。这不是原 Clight 执行到
模型的 decode；也不是无需前提的双向等价。还缺 source decoder、Mfloat64
的 8-byte 地址／权限／alignment 与 guard 对应、I64 控制、typed candidate
lowering 及 selected factory／compiler 安装。故本轮新增的 F64 optimized
case 数仍为零。

责任保持三层：kernel 没有新增语义；语言实例负责 IEEE／memory／control
对应、安全检查、入口出口运输和安装；优化实现者负责源模型、访问关系、
实际调度依赖与候选证书。最终 site producer 必须自动生产原源许可、
typing／resources／scope 等前提，源码用户仍只交标注与策略选项。

## 后续执行链

先接原 `matmul`：完整解码其 double expression 和全局 scalar／array
读写，再证明 Mfloat64 view 与原 I64 loop。不能通过将原 C 改成 I32 数据／
控制来宣称支持。静态 caps 可以支持私有坐标选择，但要证明源 Int64 无回绕
和公共控制出口的准确恢复。

同时实例化 typed polyhedral validation／codegen、guard、factory、selected
host 与 Csem→Asm；保存真正的 source、transformed model、generated candidate
和接受／回退执行。随后处理 fusion、multi-stmt-stencil-seq 和原 BT 的 loaded
与 scalar exits。其他 61 项、适用顺序配置、其余 NPB、LLVM Test Suite／SPEC
和 SIMD 调查继续保留，不因首轮拒绝而移出目标。

## 检查点与复现

[可审阅摘要](original-benchmark-first-attempt.json)记录逐阶段边界及报告 SHA-256。
组合检查点为 `build/benchmark-alignment/stage-v2/report.json`，SHA-256：
`0598d459e2badca6e2fb585516db538cb614138f8b7008f33ae40c92d310826a`。
源、二进制、日志与 `.vo` 位于忽略的 `build/` 或相应 proof directory；
仓库摘要不代替这些原始证据。

已存在检查点只验证，不覆盖：

```sh
python3 scripts/summarize_original_benchmark_attempt.py --validate
```

固定源 materialization：

```sh
python3 scripts/benchmark_alignment_inventory.py --fetch
python3 scripts/materialize_benchmark_source_pins.py --fetch
```

已有本地 PolCert Git 对象可用 `--polcert-git /path/to/polcert` 读取固定版本，
不修改它。Source probe 与 BT probe 要求已构建、hash 匹配的
`build/affine-empty-runtime/compiler-v1/ccomp`、proof report 和 Pluto checkpoint。

```sh
python3 scripts/benchmark_polcert_source_probe.py
python3 scripts/analyze_benchmark_source_probe.py
python3 scripts/benchmark_harness_constant_compat.py
python3 scripts/benchmark_cgo_bt_probe.py
```

这些脚本拒绝覆盖已有输出；在当前 workspace 不要重跑同名 checkpoint。
Corpus probe 原报告误把 CompCert dump 当作 `program.light.c`；只读的 analysis
后继核对真实 cwd 下的 `marked.light.c`，没有重做 native batch。
Compatibility report 保存的是继承环境，其中 dump 路径在 helper 中另行覆盖为
新目录；actual artifacts 与 helper 绑定，不能将继承字段冒充最终环境。

BT 新 helper 的首次复现遗漏 subprocess 环境，selection assertion 失败；
原生自检和十行结果当时已通过。该脚本与原因归档于 `bt-probe-v2`；修正后的
`bt-probe-v3` 记录实际环境并通过三配置，不将重跑计为新覆盖。浮点 proof 的
三个 rejected attempts 与两个成功 attempts 也保留，不覆盖成功 `.v/.vo`。

工具链源 pin 确认是 v3.18；其 upstream `VERSION` 仍写 3.17，因此 `ccomp`
banner 的 3.17 不表示用了旧源。见[工具链说明](toolchain.md)。本轮不改变该 pin。
全链 clean rebuild 和完整效果对齐仍属未完成验收。
