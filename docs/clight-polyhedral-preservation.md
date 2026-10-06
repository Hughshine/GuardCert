# 真实仿射／分块使用者与主接口

2026-10-06。本文面向要接入一个优化器的规则作者：说明其需要提交的局部证书、可复用的语言设施，以及当前真实编译入口的边界。整体方向遵循 [paper narrative](topdown/paper-narrative.md) 和 [三方责任](framework-responsibilities.md)。

第一项迁移是 named canonical rectangle 使用者。它消费旧路线中真实的仿射域／依赖核对器和多语句 tiling 核对器，接到主只读 condition、公共 direct/shared realization、private-region 宿主及 Csem→Asm。它不是给一个未验证候选加外围 if，也不把旧统一编译器的其余能力算作已经迁移。

## 输入与实际变换

源是动态 signed32 行列界、静态数组布局的规范两层循环。非空 body 可含普通写、原地更新、行首读取、跨数组加法和复制，实际读取／写入可涉及多个数组对象。例如：

```c
int a[120], b[120], i = 0, j = 99;
for (; i < n; ++i)
  for (j = 0; j < m; ++j) {
    a[i * 10 + j] = i * 37 + j + 7;
    b[i * 10 + j] = a[i * 10 + j] + (i * 11 + j + 19);
  }
```

使用者提出一个实际 `Loop.stmt` 和坐标映射步骤，或一个二维 tile 尺寸。候选可以改变遍历、分离语句列表、平移／剪切／反转坐标及组合这些映射。核对器验证源与候选的域、指令与参数对应，以及需要保持的依赖顺序；Clight 生成器另检查机器表达、私有计数器与资源范围。输入候选生产器在完整程序定理中是任意参数。

对于 interchange，当前入口条件保守要求 `i==0`、`0<n<=12`、`0<m<=10` 和注册数组的实际对象分离。它覆盖索引、控制与建模需要的机器范围，不声称所有数据运算都必须不回绕。实际 alias 检查是有定义的地址比较；逻辑 spec 中的 block 编号不成为运行时代码可读取的 metadata。

范围检查失败立即进入原循环。别名检查仅在范围通过后执行，此时实际源执行可提供所需数组基址的绑定与有效性。空外层不会为检查而读取源没有读取的内层 bound。此次固定数组实例不提供指针切片 alias 的原生负例；旧指针路线和已有 loaded-bound 规则仍有各自独立的证据。

## 局部证书的方向

[readonly_preserving_clight_rule](../prototype/interface/ClightReadonlyPreservation.v) 与双向规则并存。其局部义务为：

```text
在实际 program.globalenv 下：
  source 的作用域属于 live
  source 从入口正常执行，trace=E0，得到 (after, final)
  D(entry) 且 P(entry)
    ⇒ candidate 从同一入口正常执行
    ⇒ 保持全部 live temps 和 memory_equivalent(final, candidate_memory)
```

使用者还提供 source temp 写界、readonly condition 和“实际源正常执行 ⇒ D”。实际宿主提供独立 source progress、合法 placement、fresh private pool 和外围 continuation 运输。当前 `live` 保护全部原程序 temps；引入的私有计数器与 shared Boolean 不成为公开出口。

旧 [encoded_private_rule](../theories/ClightPrivateRule.v) 正好交付这种 source-to-candidate 保持，且量化实际 program 的 globalenv。`encoded_private_as_preserving` 原样保留其候选、domain、premise、formula 和局部证明，并用现有 loaded-tree 合成定理获得安全的 readonly condition。迁移没有要求优化作者补一个旧核对器未证明的反方向，也没有将保持证明改名为双向等价。

[realized_projected_selection_contract](../prototype/interface/ClightReadonlyProjectedCompiler.v) 只消费“逻辑检查选中的实际分支存在保持公开出口的执行”这一见证。双向规则和保持规则分别产生见证；后续 source temp 运输、actual realization、小步到达正常出口和 private-region 契约共用同一证明。语言无关 condition 证书及其安全性要求保持。

## 四张证书在这一例子中的来源

| 责任／证书 | 优化方与 domain library 提供 | 框架／语言设施复用 |
| --- | --- | --- |
| `C_opt` | `checked_named_mapped_candidate_correct` 或 `checked_named_tiled_candidate_correct`；实际候选与源依赖保持 | 已有 PolCert/VPL 核对器，不信任候选搜索或未经核对的 oracle 结果 |
| `C_derive` | 静态 layout 证书、入口范围与注册数组分离足以覆盖整个模型执行；`memory_named_array_candidate_local` 连接源解码、NonAlias 模型和候选编码 | 旧 rectangle 参数范围／机器表示、注册数组 backend、真实 load/store 与公开出口恢复定理 |
| `C_guard` | `memory_named_source_domain` 从实际源执行取得 D；旧命名数组原语证明范围／基址检查 | `synthesized_loaded_tree_condition` 从原公式原语产生可达测试安全、可用性、只读状态及接受性质 |
| `C_host` | 本次 source syntax 和候选生成成功证据；shared 的 quiet/freshness 检查 | `direct_normal_realization`／`shared_normal_realization`、公共安装证明、private pool／scope／progress 宿主、CompCert backend |

这里的 `C_derive` 是已有矩形领域证明的复用。它把保守入口范围、静态布局和数组分离与整段模型执行连接起来；没有新增通用 Presburger projection 或任意 S/T 的条件发现算法。hard obligation 仍在实际源访问和机器模型的全实例对应，而非增加一个 implication 字段。

源码分别是 [语言保持接口](../prototype/interface/ClightReadonlyPreservation.v)、[named 使用者与实际候选核对](../prototype/interface/ClightPolyhedralPreservation.v) 和 [真实完整编译入口](../prototype/interface/ClightPolyhedralCompiler.v)。前两者桥接旧模型证书；编译入口先核对实际候选，再产生实际 AST table。table 的每一项消费主接口得到的区域契约，不能跳过候选／guard 证明直接安装。

## 运行与审计

在已有锁定工具链中执行：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-polyhedral-native
```

这是可选的多面体使用者入口，不重新初始化工具链。它依次审计实际依赖闭包、提取 `ClightPolyhedralCompiler.compile_preserving_polyhedral`，并运行真实多数组及连续替换程序。候选文件使用 `GUARDCERT_LOOP_CANDIDATE`；`GUARDCERT_GUARD_LOWERING=direct|shared` 选择两个已证明的 realization，默认 shared。shared 为 Boolean 保留一个槽，其余槽提供配对私有迭代器；资源不足或检查拒绝保留源片段。

证明报告在 `build/interface-polyhedral/report.json`，提取 stamp 在 `build/compcert-readonly-polyhedral/.guard-build.json`。审计逐项记录旧 mapped／tiling 端点的继承假设，与主 CompCert-only 审计分开；当前 11 个端点、260 项使用者依赖、42 个继承假设名，无新增全局公理。相对 CompCert 的额外七项来自已有 PolCert/VPL 基线，不能写成“只有 CompCert 的 35 项假设”。

原生报告分别在 `build/interface-polyhedral-native/report.json` 和 `build/interface-polyhedral-context-native/report.json`。它们核对当前 proof／compiler stamp，比较 GCC、独立源模型和实际编译的汇编，并检查生成的候选／guard AST。真实程序包括多数组、全局数组、外围循环、行前缀依赖、两个连续 region、外围 goto 和空外层未初始化内层参数。最终结果以 [10 月 6 日阶段记录](research-checkpoint-2026-10-06.md) 为准；没有测量性能。

## 当前边界与下一项难点

此次迁移覆盖实际矩形源和真实仿射／分块候选；任意候选并不表示任意 C body。源语法、静态布局、原子 RHS 和合法控制仍须匹配已有 named 证书。shared 实现确实只有一份候选和一份 source fallback；其生成本身不是新的优化算法。

安装使用完成执行的宏宿主，需要 source 独立 progress。它不把可能无限的源回退纳入新的多面体入口；既有 unsigned 完整循环的小步宿主是另外一个已实现的用户。一般 affine 源、ragged 域、参数化下标、真实指针切片和 stateful footprint 检查尚未迁移到本入口，也没有复用一次入口事实跨不同 region。

下一阶段应扩大实际源／模型对应，并选择一个受限符号化条件／足迹算法：证明入口 B 覆盖整个候选需要的 A，再复用编码与安装设施。至少需要真实非空接受域、机器安全、保守拒绝与完整程序执行；不能把新接口文件的数量算成关闭这些难点。
