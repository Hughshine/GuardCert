# 带入口起点的片段

本阶段把指针循环片段的根起点从 `0` 扩展为片段入口时的实际游标值。内层循环仍由已认证的源 AST 重置为零。统一完整程序入口及其任意不受信任提案器参数保持不变。

```text
检查入口起点、各轴上界和地址参数范围
  拒绝 → 原片段
  接受 → 只扫描本片段实际访问的坐标对
            拒绝 → 原片段
            接受 → 经依赖验证的候选 → 恢复源片段公共出口
```

扫描域为 `[start, upper)`，内层为原有各轴域。不能扫描源没有访问的 `[0, start)`：源正常执行只提供实际访问点的权限，不能保证这些额外指针检查可以执行。

## 接口与证明

`memory_started_pointer_package` 绑定已检查的实际源 AST、根游标、上界、循环体和内层形状。`make_memory_started_pointer_package` 从原参数化源包构造它；无需信任新的 AST 识别器。

`memory_started_pointer_context` 在原上下文末尾加入入口根游标，作为稳定循环下界参数。源指令仍接收原坐标和地址／RHS 参数，不把这个下界槽加入指令参数。私有 guard 与候选计数器保持该公共游标，候选结束后使用已有 `memory_recursive_restore` 恢复源出口。

`memory_started_pointer_source_header_domain` 从真实源执行推出短路检查所需的整数类型。根和上界由源入口比较提供；内层上界按实际执行逐层提供，地址参数由实际首次叶执行提供。空域可以在读取未定义内层参数前拒绝。

`memory_started_pointer_source_under_ranges` 将真实 Clight 源执行对应到 `memory_started_pointer_loop`。`memory_started_pointer_source_runtime_domain` 推出实际足迹的地址能力；`memory_started_pointer_footprint_member` 证明该足迹精确枚举实际坐标和原访问。

`memory_started_axis_access_pairs_execution` 证明实际检查代码执行得到枚举结果且保持公共状态和内存；`memory_started_axis_pointer_pairs_separation` 将检查通过转为受限源足迹上的 NonAlias。`memory_started_axis_pointer_guard_execution` 合成实际 guard 编码。

`memory_bounded_source_certificate` 与 `checked_memory_bounded_source_candidate` 接收任意已对应到源执行的循环 IR，复用原 mapped-domain 验证。`checked_memory_bounded_source_tiling` 同样接收实际源和候选，通过已有分块 witness 验证器检查。实例先检查仿射边界的分块表示，再由 `memory_started_scalar_tile_trimming` 证明缩短空尾块后执行不变。块内检查跳过 `start` 之前的点；外层块计数从零开始，可能经过起点之前的空块。

`memory_started_pointer_projected_candidate_rule` 把源对应、受限内存、依赖验证、机器 lowering 和公共出口恢复组合为实际片段规则。三个候选服务和 `check_memory_started_axis_unified_region_sound` 接到原 `compile_memory_unified_regions_correct` 的 `Csem → Asm` 端点。抽象核心继续只消费定义域、前提、检查编码和观察保持性质。

## 使用与范围

```text
(started (per-axis (schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))))
(started (per-axis (tile 2 3)))
```

`request_source_loop` 向不受信任提案器提供实际循环 IR。原生提案器可据此适配直接矩形候选的根下界；验证器仍检查结果。原普通、逐轴、版本族和前缀入口使用 `None`，保留各自路线。

完成提取构建后，可以通过候选文件使用这个入口：

```sh
printf '%s\n' '(started (per-axis (tile 2 3)))' > /tmp/guard-started-candidate.sexp
GUARDCERT_LOOP_CANDIDATE=/tmp/guard-started-candidate.sexp \
  build/compcert-memory-unified/ccomp \
  -conf build/compcert-memory-unified/compcert.ini \
  -stdlib build/compcert-memory-unified/runtime \
  -dclight -S -o /tmp/guard-started.s examples/native_memory_started_regions.c
```

当前快速域要求非负入口根且小于正的已检查上界，地址参数非负并在所选范围内，RHS 标量允许完整 signed 范围。负根、空域和范围外输入执行源片段。入口根取值不要求是零。

源地址语法检查仍使用原从零开始的静态坐标 box。因此，仅靠非零下界才能使负偏移访问合法的源尚不能由该实例接受。运行时扫描暂用完整访问点对，未接入已有边界扫描或运行时版本族。该阶段不保证最弱条件、检查成本下降或运行时间改善。

## 验证

31 个新增模块及统一入口已通过全量证明编译、假设审计和提取构建：407 个适配模块、七个 lowering 模块、三个抽象核心及 557 个证明源码哈希。实际指令、一般 validator 和完整编译器分别保持既有 7、12、42 项假设，没有新增公理。编译器 SHA256 为 `12533dfe59319e7fcd02e5f2b0d175000b8292b1ae04f4310fdf57cfeaca5685`。执行脚本核对编译器、全部证明源码和原生源码哈希。

八个参数化数组内核提供 791 个唯一输入。13 种配置全部通过，共 10283 次完整 CompCert 汇编调用：一、二、三维直接候选，二维／三维交换，自动恒等／交换／分裂调度，`2×3`／`17×13` 分块，以及错误坐标、资源耗尽和故障证书的安全拒绝。所有配置核对完整缓冲区和公共游标，而非仅结果摘要。

十种带 guard 的配置另通过 5340 次源函数调用的实际分支与查询计数诊断；1816 次调用进入候选、3524 次回退，共 4444 个候选片段入口，其中 369 个具有非零片段根起点。271 个负根入口回退，64 个地址参数未定义的入口均未执行地址查询。该诊断使用 GCC 执行插桩 Clight；完整汇编结果由前述独立套件验证。报告分别为 `build/native-memory-started-regions/report.json` 和 `branch-report.json`。

自动调度生成器只携带循环次数约束，独立验证器和机器 lowerer 仍检查完整参数范围。完整 signed32 区间不是可直接注入机器表达式的约束模板；这种分工避免生成超出机器范围的边界常量，同时保留候选验证义务。

七类旧普通／单方案入口的完整输出及实际分支回归均已通过，新旧报告除编译器哈希外逐字段一致。原有多方案及检查前缀各四种定向配置已经完成完整输出和独立分支检查；与上一已验证版本的对应报告逐字段一致，仅排除编译器哈希。这些回归不算新入口的覆盖扩展。

GCC 源程序输出与独立机器字模型一致。上一已验证编译器也执行全部 791 个源输入，完整数组和公共游标与模型一致；它不识别新模板，没有插入本次变换。该源基线单独记录在 `build/native-memory-started-regions/previous-source-baseline/report.json`。

通过 `make native-memory-started-regions` 可复现完整证明／编译构建与两层执行检查。该入口尚未支持负根快路、负地址参数快路、更一般深层仿射域、边界扫描组合及版本族组合，不能据此声称已完成全部多面体能力对齐。
