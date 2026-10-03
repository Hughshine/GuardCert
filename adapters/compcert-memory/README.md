# 基于 CompCert Mem 的具体多面体指令实例

这个适配实例将一般多面体 validator 的 `INSTR` 参数具体化为实际 CompCert 内存。`GuardMemoryCompiler.compile_memory_regions` 已将真实源循环、实际多面体依赖检查、guard、候选循环与原片段回退接到完整 Csem→Asm 定理。完整 C 输入的交换路径支持三种矩形循环体；`GuardMemoryTiledCompiler.compile_memory_tiled_regions` 另支持矩形纯写、原地更新和行前缀读取的二维分块、尾块和公开 iterator 出口修复。`GuardMemoryCutCompiler.compile_memory_cut_regions` 支持仿射叶子条件选择出的三角形、斜切等迭代域，并已接通完整定理和实际分块。`GuardMemorySequenceCompiler.compile_memory_sequence_regions` 已支持同布局数组上的非空纯写语句列表，保留每条语句的编号与先后顺序并接通完整 C 分块定理。`GuardMemoryOperationsCompiler.compile_memory_operations_regions` 进一步支持同数组的非空混合纯写／原地更新／行首读取列表，获得完整 Csem→Asm 分块定理。独立 IR 检查器支持更一般的仿射提案与二维 tiling。支持范围分别记录。

## 已证明的接口

`GuardMemoryRuntime` 的状态是不可变 cell→物理 location 映射与实际 `Mem`。映射是语言视图；不能在生成的 C 中查询它。一次操作解析实际位置，执行 Mem.load，把加载值交给纯计算，再执行 Mem.store，并保存映射。三项 Bernstein 条件由映射的物理不相交性质推出真实操作的交换。

`flat_array_locations` 只解析某个普通 Mint32 数组的合法一维下标。`flat_array_locations_nonalias` 是闭合证明，没有假定不同逻辑 cell 自然对应不同物理地址。源 Clight 的数组绑定、类型、机器下标范围和偏移仍由具体 bridge 证明。

`GuardMemoryInstr` 实现实际 PolCert `INSTR` 的全部字段。状态关系是映射和 Mem 的精确相等；读写访问函数由结构相等检查绑定到 instruction，实际语义的 footprint 是这些函数计算出的 cell。payload 支持常量、参数、已加载值及 Int.add/sub/mul；失效输入或访问不产生成功执行。`InitEnv` 在这个物理指令实例中只约束参数数量；完整语言 bridge 必须将具体入口 temporaries 与参数值绑定。它没有沿用 CState.valid。

`GuardMemoryRectangles` 从真实 Clight 的纯数组写、同格子读改写、行首读取恢复具体指令执行。`GuardMemoryLoops` 与 `GuardMemoryClightRectangles` 把完整矩形循环的实际执行接到真实 Loop 语义，并重建完整候选执行，保留全部公共 temporaries 和 Mem。

`GuardMemoryPolyhedral` 实例化实际一般仿射和 tiling validator。`guarded_memory_validate_refines` 的输出是精确的状态结果，无遗留 INSTR 语义参数。`validate_memory_equivalence` 对仿射提案进行双向验证；接受时 `validated_memory_equivalence` 给出两种执行方向，因而源执行可以建立候选进展。双向检查是当前可用的构造，不声称是最便宜的算法。

`GuardMemoryTilingProgress` 进一步构造原迭代点与新增 tile 坐标的双向对应，证明有限点覆盖、唯一性、排序及单点执行保持，从源执行构造 retiled 执行。`validate_memory_tiling_equivalence` 在结构检查后，对 retiled 点空间与候选执行双向调度检查。接受时，`validated_memory_single_tiling_progress_at` 对单条多面体语句、任意合法 tiling witness 给出源到候选的实际执行进展，保留具体参数值与完整状态；`GuardMemoryTilingMultipleProgress.validated_memory_multiple_tiling_progress_at` 已把同一端点推广到多个语句，保留语句编号，证明整个有限域的覆盖、唯一性和源时间戳／实际执行保持，见 [多语句进展证明](../../docs/memory-multiple-statement-tiling.md)。同布局纯写列表的具体 C 源／候选 bridge 已接通 `GuardMemorySequenceCompiler.compile_memory_sequence_regions` 和完整 Csem→Asm 定理。所有提案仍继承原有候选到源的正确性端点。

`validated_memory_equivalence_at` 保留具体入口参数值；仅用存在量词包装参数的实例级端点不足以建立 Clight 对应。`GuardMemoryPolyhedralRectangles` 证明完整矩形域的点覆盖、唯一性、排序与实际执行对应；`GuardMemoryValidatedRectangles` 用真实双向依赖验证的结果建立 guarded Clight 规则。`GuardMemoryCompiler` 检查源 AST、构造源与交换候选的 IR，消费上述规则并证明 `compile_memory_regions_correct`。定理要求无 alarm 的 `mayReturn (OK assembly)`，结论是原 Csem 到实际 Asm 的 backward simulation。

[二维分块证明链](../../docs/memory-two-dimensional-tiling.md) 从源循环建立候选执行，经具体 `GuardMemoryFlatArrayBackend` 生成包含真实读取和写入的 Clight，并通过私有状态宿主获得完整 Csem→Asm 保证。一般结构化 Loop 的纯写编码器允许下标包含已检查的仿射运算和正整数除法。

[仿射条件域证明链](../../docs/memory-affine-conditional-domains.md) 证明域筛选、真实源条件执行、机器算术、实际依赖检查和候选分块执行的对应，支持两个动态边界与静态 cut。具体 C 入口要求非负 cut 常量，以真实执行建立数组绑定；更广的域交集与结构化条件 Loop 定理分别记录。

## 原生检查器与编译器

```sh
# 已有当前 proof profile 和适配模块审计时，可直接执行脚本。
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_validator.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_memory_validator.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_compiler.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_memory_compiler.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_compiler.py --tiling
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_memory_tiling.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_compiler.py --cuts
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_memory_cuts.py
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/build_memory_compiler.py --sequences
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/native_memory_sequences.py
```

完整依赖构建目标为 `make native-memory-validator` 与 `make native-memory-compiler`。两种提取共用有资源上限的非可信 Fourier–Motzkin 证书搜索；证书由提取的 VPL LCF 检查。错误证书和搜索耗尽均拒绝变换。OCaml 的整数表示转换、文本读取与拓扑排序属于非可信输入侧；检查器验证它们产生的结果。

`make native-memory-tiling` 构建独立的二维分块 C 编译入口。`build/native-memory-tiling/report.json` 记录五组块大小、3975 个正动态矩形（纯写、原地更新、行前缀读取）、19 个实际分块函数，以及非法块大小、溢出、错误证书和资源耗尽的源回退；所有数组元素和公开 iterator 出口与 GCC 和独立模型一致。

`make native-memory-cuts` 构建仿射条件域 C 编译入口。`build/native-memory-cuts/report.json` 记录五组块大小、4800 个正动态条件域、九个实际分块函数和五条拒绝路线；每组 1294 行完整程序输出与 GCC 和独立模型一致，逐元素检查数组及公开计数器。

`make native-memory-sequences` 构建多语句 C 分块入口。`build/native-memory-sequences/report.json` 记录五组块大小、4125 个正动态矩形、8 个实际分块函数和五条拒绝路线；每组 1138 行输出与 GCC 和独立模型一致，实际快路中两／三／四条赋值的数量和顺序均被检查。重复语句、两个布局及完整程序上下文也通过，见 [多语句证明链](../../docs/memory-multiple-statement-tiling.md)。

独立检查器的 JSON 输入经 `scripts/memory_validator_input.py` 转为有大小上限的输入格式；`affine` 执行双向仿射检查，`tiling` 执行实际 `checked_tiling_validate_poly`，验证新增 tile 坐标与域对应，`tiling-equivalence` 还执行建立进展所需的双向调度检查。历史的 `AffineValidator.validate_tiling` 只处理同一已有点空间上的调度，不能代替结构检查。独立 IR 接受不构成某个 C 源程序的编译保证。

验证报告为 `build/native-memory-validator/report.json`（35 组提案、1309 组独立执行比较，含两／三语句依赖及条件域的二维 tiling 进展检查）与 `build/native-memory-compiler/report.json`（225 个纯写、345 个读改写、225 个行内依赖正矩形；19 个实际命中 guard 的函数；完整数组及 iterator 出口与 GCC 和独立模型一致）。后者还实际编译、执行资源耗尽与错误证书下保留源循环的程序。

## 构建与假设

已有锁定 optimizer proof profile 时：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_guard_memory.py
```

完整依赖重编译的目标：

```sh
make guard-memory-proof POLCERT_SOURCE=/home/hugh/research/polyhedral/polcert/work/verified-compilation-v10-driver
```

详细报告为 `build/guard-memory-proof-report.json`，构建和假设日志位于 `build/guard-memory-assumptions/`。当前脚本重编译 293 个适配模块、七个 lowering 模块和两个抽象有状态核心模块；直接调用脚本复用此前的 92 文件 PolCert optimizer proof profile，没有重新编译整个 profile。抽象核心及物理数组 nonalias 均没有全局公理；指令桥继承 7 项假设，具体 validator 与 tiling 进展端点继承其原有 12 项，完整编译器继承 CompCert 与 validator 的并集 42 项。审计要求完整编译器的集合精确等于该并集，没有新增全局公理。默认 C→Asm 编译器的 35 项集合不能直接套到这条路径上。

## 正在接通的边界

当前统一入口已支持限定的动态矩形和非矩形源族、多个实际数组对象、跨数组同单元读取及复制、组合仿射坐标映射和二维分块。不同布局的混合操作列表、转置／缩放／散布访问、有源基址证据覆盖的非负邻居偏移，以及多读取整数计算已接入。[内层宽度条件搜索](../../docs/memory-inner-width-conditioning.md)随后接入复制链的实际分裂与安全回退。[三重 C 循环](../../docs/memory-three-level-loops.md)已接入矩阵乘法、非恒等调度和外层二维分块；[递归规范 C 源循环](../../docs/memory-recursive-source-loops.md)进一步接入任意有限维矩形源、相同依赖检查、调度生成及外层二维分块。[真实指针缓冲区](../../docs/memory-pointer-buffers.md)进一步接入一个稳定指针、非零基址、有限范围条件搜索和同一完整程序端点。稳定 RHS 标量、signed 仿射地址及多个不同指针的活动访问分离随后也已接通；当前边界见下方对应记录。更一般的深层仿射域、参数化访问及更宽的别名条件继续推进。OpenScop export 与 scheduler callbacks 当前安全拒绝；没有一般 C 源覆盖或性能结果。各早期入口的证据按下述文档分别记录。

`make native-memory-operations` 构建同数组混合读写列表的完整 C 分块入口，`build/native-memory-operations/report.json` 记录五组块大小、5325 个正动态矩形、10 个实际快路函数与五条拒绝路线；每组 1564 行完整数组及公开 iterator 输出与 GCC 和独立模型一致。证明与当前源语法范围见 [混合列表证明链](../../docs/memory-mixed-statement-tiling.md)。

[一般 Loop 与外部候选](../../docs/memory-general-loop-candidates.md) 已接通任意成功提取的仿射 Loop/Seq/Guard 执行对应和不受信任的结构候选编译入口。`make native-memory-loop-ir` 验证一般 IR；`make native-memory-proposed` 验证实际 C→Asm 的候选接受与回退。当前 C 源识别仍是单数组矩形混合列表。候选检查消费运行时 guard 中已经证明的数组范围前提；域约束排序有整个多面体程序的表示等价证明。

[外部候选的点坐标对应](../../docs/memory-point-coordinate-correspondence.md) 已证明任意相邻 iterator 交换的组合及其真实提取接入，保护参数前缀，并继续核对候选内存依赖。

[语义域等价与统一入口](../../docs/memory-semantic-domain-alignment.md) 用现有空域证书核对不同约束写法的整数点域，并证明候选域表示转换保留整个执行。`make native-memory-unified` 提取同一个完整 C 编译入口，接受外部仿射 Loop 或 `(tile rows columns)`；两条路径共用 guard、回退与完整程序宿主。

[多个实际数组对象](../../docs/memory-multiple-array-objects.md)已有源执行、候选后端、安全基址检查与完整程序定理。`make native-memory-multiarray` 使用统一编译器验证两／三数组、全局与外层循环、候选接受和源回退；当前 C 源包括同布局对象的三类矩形操作、跨数组同单元读取、只读输入和[直接数组复制](../../docs/memory-direct-array-copy.md)。

[仿射 iterator 对应](../../docs/memory-affine-iterator-maps.md)提供候选坐标的交换、平移、剪切及其组合；它们已进入同一完整编译器证明。`make native-memory-affine-maps` 检查实际 C 程序中的候选接受、依赖拒绝及机器边界拒绝。

[非矩形 C 源循环](../../docs/memory-nonrectangular-source.md)支持实际 `K=i+M; j<K` 的循环边界，证明宽度前提的安全编码和 `i/j/K` 的源出口对应，并接通实际二维分块；生成代码以除法向上取整计算块数，空迭代裁剪有执行等价证明。`make native-memory-ragged` 运行统一完整程序入口；当前完整审计覆盖 118 个内存适配模块和 7 个 lowering 模块。


[源调度到实际代码生成](../../docs/memory-schedule-generation.md)接入相同统一编译器：不受信任的候选只提交每条源指令的仿射调度，源域、指令和访问来自实际提取；生成出的 Loop 再经独立域与依赖检查。`make native-memory-schedules` 验证矩形和非矩形两类源的各 13 组配置，分别逐组比较 4,022 和 1,385 行完整程序输出。交换、分裂、平移和剪切的实际快路，以及错误映射、资源耗尽和错误证书下的源回退均通过。

[参数化仿射 C 上界](../../docs/memory-parametric-affine-bounds.md)使用实际源表达式读取构造参数环境，证明数学编码、端点范围检查、短路求值安全、真实源执行及候选出口修复。统一入口支持 `2*i+M-P`、`M-2*i+P` 等边界和不限于两个的稳定参数。源访问仍沿用同布局数组的已证明形式；[不同数组布局](../../docs/memory-different-array-layouts.md)的一条复制已接入，支持各自的固定长度和步长；[不同布局的混合操作列表](../../docs/memory-layout-operation-lists.md)随后已接入，更广访问仍需扩展。

[同一数组的布局重映射](../../docs/memory-same-array-layouts.md) 使用一个实际对象登记两个不同步长的访问函数，使真实跨迭代依赖进入相同验证器，并接入完整程序端点。

[候选条件搜索](../../docs/memory-candidate-conditioning.md)由真实源循环体语义模型支撑：默认参数域验证失败后，对同一候选重新核对较小的外层次数区间，证明检查编码、分支安全和完整程序正确性。同布局混合列表与独立读写布局复制均为实际实例。

[不同布局操作序列](../../docs/memory-layout-operation-lists.md)证明每条操作的源执行、实际对象登记和指令对应，再顺序组合为通用源体模型。`make native-memory-layout-sequence` 使用同一完整 C 编译器验证复制链、更新、全局数组、外围重复循环和同数组重映射。

[真实仿射 C 下标](../../docs/memory-affine-source-accesses.md)已将加减和嵌套常数乘法构成的两变量访问编码为实际读写足迹。`make native-memory-affine-access` 在统一完整程序入口验证转置、缩放、散布、混合复制链和同数组依赖，以及未支持的 `while` 结构回退。

[源证据与邻居偏移](../../docs/memory-anchored-offset-accesses.md)将一个对象的零地址访问证据用于该对象的不同偏移访问。`make native-memory-offset-access` 验证邻居读写、跨操作证据、调度与分块及依赖拒绝。

[多个仿射读取与整数计算](../../docs/memory-affine-computations.md)已接入相同完整程序入口，源体包括有限多读取、加减乘、两个循环变量及非线性标量计算。`make native-memory-affine-compute` 验证 14 组汇编配置和五组分支诊断。

[三重 C 循环与矩阵乘法](../../docs/memory-three-level-loops.md)从实际三层 Clight AST 解码为三维 Loop，证明条件式的边界读取定义性、零点内存证据、短路 guard、候选执行与三个公开计数器出口。`make native-memory-triple` 验证 13 组汇编配置、每组 2811 行输出和七组分支诊断。

[递归 C 源循环](../../docs/memory-recursive-source-loops.md)的全量证明审计为 192 个适配模块与七个 lowering 模块。`make native-memory-recursive` 验证 17 组完整汇编配置，每组 2250 行输出，并通过 11 组／458 次调用的分支诊断；完整编译器仍为原有 42 项假设。

[真实指针缓冲区](../../docs/memory-pointer-buffers.md)的统一全量审计为 211 个适配模块与七个 lowering 模块，完整编译器仍为原有 42 项假设。`make native-memory-pointer` 验证 15 组完整汇编配置，每组 227 行调用方完整缓冲区及公开计数器输出，并通过 10 组／390 次调用的分支诊断；包含一元素实际分配的快路及空指针零次循环。这一指针阶段的报告在加入 RHS 标量之前，多个不同指针和外部 RHS 标量安全拒绝。

[稳定 RHS 标量参数](../../docs/memory-stable-scalar-parameters.md)随后接入指针与局部／全局固定数组。零列补齐的语义证明保持地址与 N+E 实参的一致，实际源执行提供标量类型，guard 不提前读取标量。当前全量审计为 240 个适配模块与七个 lowering 模块，完整编译器仍继承原有 42 项假设。两类各 16 组完整汇编配置通过，每组分别核对 196／672 行完整输出；各 10 组分支诊断分别核对 2626／2602 次调用，包含不同轴长度、负数及极值标量和未初始化标量的零次循环。旧指针路径 15 组完整配置及 10 组／586 次分支回归也通过。多个不同指针的重叠条件与更一般深层源域继续推进。

Signed affine source accesses now use a proved lower and upper box check. The 241-module audit retains the existing 42 whole-compiler assumptions. Thirteen assembly configurations and ten branch diagnostics (5463 calls) passed; see [the signed access record](../../docs/memory-signed-affine-access.md) for the compiler hash and the distinction between assembly checks and instrumented Clight diagnostics. Multiple pointer inputs still require a new source and backend instance.

[多指针源与动态分离检查](../../docs/memory-multiple-pointer-guards.md)接入多个稳定 `int *` 参数、各自的实际读写访问、活动访问权限与对齐证明、受限视图中的依赖验证、真实候选 lowering 及同一完整程序定理。全量审计为 269 个适配模块和七个 lowering 模块；完整编译器仍为 42 项原有假设。11 组完整汇编配置及九组／5256 次调用的分支诊断通过，`make native-memory-multi-pointer` 可复现。

[候选源元数据](../../docs/memory-source-metadata.md)由各源包提供实际维数和完整参数前缀，便利坐标调度不再从访问系数反推 ABI。269 个适配模块及七个 lowering 模块的全量审计、九组／828 次完整汇编调用和六组／72 次分支调用通过，编译器保持原有 42 项假设。

[私有状态与循环式 alias guard](../../docs/memory-loop-alias-guards.md)通过 `memory_projected_private_rule` 和检查执行接口证明公共临时变量及内存保持不变，接受时在检查后的状态建立候选前提。实际源足迹的双指针扫描接入同一完整程序端点。随后加入[坐标反射](../../docs/memory-coordinate-reflection.md)：280 个适配模块和七个 lowering 模块的全量审计、十二组／1200 次完整汇编调用和六组／600 次分支调用通过；完整编译器仍为原有 42 项假设。当前支持一轴逐元素访问，guard cap 为 1024，O(n²) 扫描，显式映射的一维反向候选可接受。

[一般一维仿射地址扫描](../../docs/memory-affine-alias-scans.md)随后将这条路径推广到 signed 仿射下标、多指针和多赋值，至多构造 32 条原始访问的交叉检查。实际 CompCert 源访问提供地址有效性及对齐，接受后建立活动足迹的 NonAlias，再消费独立的调度依赖检查。新的语言无关 `StatefulGuard` 核心通过具体 Clight 实例和 `projected_region_contract` 接入同一 Csem→Asm 端点。293 个适配模块、七个 lowering 模块和两个核心模块全量审计通过，2696 次完整汇编调用及 1366 次分支诊断通过。当前检查为 O(A²n²)，多轴和带地址参数的扫描仍待扩展。
