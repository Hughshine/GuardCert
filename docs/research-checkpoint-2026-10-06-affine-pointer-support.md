# 2026-10-06：非矩形 pointer 的局部证明支持

这是一个证明支持阶段。新的 `j<U(i,parameters)` pointer source matcher、完整安全域 D、guard／local-rule package 与程序安装尚未完成；现有可运行 pointer compiler 的源域仍是矩形。完整研究目标保持 active。

## 实现和责任

| 提供者 | 本阶段实际交付 | 使用者仍须证明／提供 |
| --- | --- | --- |
| framework | 核心保持，新的条件证书沿用 `readonly_condition` | 不从 source／candidate 自动提取任意前提 |
| 语言实例 | 原 counted-loop decoder 增加稳定入口 frame；实际 first-body 到达；原 restore 服务被新的候选运输消费 | source 的控制形状、合法 placement／scope 和活动路径证据由实例证书绑定 |
| optimizer/domain | `[i;j]++entry_context` 的真实 affine-inner Loop 模型；实际 pointer body／源对应；实际 ragged footprint、capability、盒状覆盖和 non-alias 条件；原 mapped-domain checker 的显式 source 接口；候选 Clight 执行与公开出口保持 | 源／候选 AST、坐标和参数范围、typed view、source width、地址／RHS 参数使用证书、pointer receipt、候选验证证书 |

语言服务只把已有 `temp_agree stable base current` 交给 point decoder，不解释 pointer、alias 或 schedule。旧 row／source theorem 保留包装，只有一份循环控制证明。新的实际 body 解码不假定 non-alias；non-alias 在条件接受后用于旧 candidate checker 的数学依赖证明。

Loop 指令接收两个坐标以及原始入口参数。内层上界在 `i::entry_context` 求值，源足迹只枚举 `0<=i<N && 0<=j<U(i,context)`。RHS 标量可参与计算，但不会被错误地追加为地址几何或强制非负。

包络 pair compiler 与物理分离证明从旧矩形模块提为共享服务，旧 qualified 名称保留为兼容别名。新 readonly 条件证书证明：在调用者给出的 D 中，实际检查安全、可完成、保持入口，并且接受建立实际源足迹上的 non-alias。D 的类型／范围／receipt 义务显式列出，没有包含待检查的 non-alias。三角域 `U(i)=i+1` 提供一个具体实例；其盒为 `[N;N]`，三个参数观察可引用同一个 n，不引入虚构 temp 或独立内层 count。

source first-body 服务要求实际两个 header active。body-only 参数的类型来自这个实际 body 的地址／值求值，并沿稳定 frame 回到入口；header-only 参数来自原 source-word theorem。这关闭了这些局部类型运输证明，尚未关闭新 selector 的完整 D 生产与短路安排。不能据此在空域入口提前读取所有 body 参数。

候选运输在实际源 footprint 上 restrict，消费原 checker 的 certificate，再 unrestrict 并调用既有 pointer backend。候选产生相同完整 CompCert memory；公开 row／column／inner-bound 按源最后 `U(N-1)` 恢复。源解码、表示范围和源公开出口是明确输入；这些服务还未由新 package 自动组装。

关键源码与剩余验收见 [活动设计](affine-pointer-domain-next.md)。

## 证明验证

`scripts/audit_affine_pointer_domain.py` 编译当前所选依赖 closure，并审计局部证明与现有完整 compiler theorem：36 个局部端点（5 个语言端点）、515 个实际依赖、860 份源摘要；CompCert 基线 35 个、继承 PolCert/VPL 的 7 个假设，新增全局公理为空。

这是受影响 closure 的增量重编译和当前对象摘要绑定，未做全 CompCert 工具链 clean rebuild。原冻结基线里发生变化的三个文件在当前 closure 中重新验证：`GuardMemoryParametricSourceClight.v`、`GuardMemoryParametricInstructionChecker.v`、`GuardMemoryParamAxisFootprint.v`；不改写旧 baseline manifest。closure 编译结束再检查源／依赖时间，避免把构建期间改动的文件绑定到旧对象。

现有矩形 pointer compiler 另有当前审计：81 个端点、506 项实际依赖、852 份源摘要，原 `compile_realized_observed_pointer_correct` 继续给出 Csem→Asm backward simulation。这个端点是兼容性回归，不能描述成新的非矩形 compiler 端点。

## 提取和原生回归

在独立目录重新提取原 `compile_realized_observed_pointer`。direct／shared 各新编译一个 `direct-interchange-2` 配置，均覆盖原完整 376 组源调用，共 752 次配置内调用。完整 buffers、公开 i/j/k、prefix 结果与外围 effect 均与独立模型和 GCC reference 一致。

两模式的 proposal、Clight 输出、选择／复制计数及程序输出与冻结 `f144d45` 元数据一致。汇编除记录构建路径的 `# Command line:` 注释外逐字节一致；原汇编与新汇编分别核对自己的完整摘要，再做该单行归一化比较。原／新 linked binary 都分别绑定自己的摘要，不声称 binary SHA 一致。

本次没有重新执行十五配置完整矩阵，没有新的机器路径探针、运行计时或新非矩形 C 执行。`f144d45` 的原完整矩阵与二十个机器探针保留为历史证据，原报告／compiler／native 目录未覆盖；其元数据归档于 `build/history/f144d45-pointer-realization/`。

| 当前产物 | SHA256 |
| --- | --- |
| `build/affine-pointer-domain/proof/report.json` | `2da918d755e88a5f601b0c6a2ba2e8481e758e069d14206fab8d102170708f77` |
| `build/affine-pointer-domain/compiler-proof/report.json` | `ab977f28d8d6ff4d36ab39cb55bb841dec4ef2a514980930c2bb55ebb93accea` |
| `build/affine-pointer-domain/compiler/.guard-build.json` | `8ae5645e3ee9fc025eb66810aeccfbecd938f40a31e8480ec163509dbbf1ae14` |
| `build/affine-pointer-domain/compiler/ccomp` | `4e1fd9d6ce8a0816731a95117f745eb7044f536cfbf9fddb28434ae003e6f913` |
| `build/affine-pointer-domain/native-shared/smoke-report.json` | `131a3c662ba62d8eb11343ab8361ad4b8e4b27f4483c6ae7f8f48c168096ce41` |
| `build/affine-pointer-domain/native-direct/smoke-report.json` | `7616cafead8dc2f94522819424849bc915e117d587827bade6f9e4364fa2a9b4` |
| `build/affine-pointer-domain/validation.json` | `8b8a32542f657f049f83194780e6c1a8df9efedd478f41399bf757e5eac32e4f` |

## 复现与下一步

在项目 Rocq/OCaml 环境中，`make affine-pointer-domain-proof` 验证局部支持与现有完整程序 theorem；`make affine-pointer-domain-regression` 再独立审计、提取并跑两个旧路径配置。冻结旧产物仍在时，可额外执行：

```sh
python3 scripts/validate_affine_pointer_domain.py \
  --baseline-dir build/history/f144d45-pointer-realization \
  --baseline-artifacts-dir build/native-interface-pointer-realization
```

下一步按 [当前计划](current-work-plan.md) 绑定新的 normalized source package：先取得 row／bound 与实际 header 参数类型，再由 active-first-width 允许 body-only 参数观察，随后完成机器范围、实际读取 receipt、候选 certificate 与 restore 的单一入口连接，接序列 host 和完整 compiler。之后验收非空符号接受、n=3 的真实 alias 回退、空／机器边界／破坏 receipt／非法候选和完整 buffer／公开出口。矩形包络只推导充分条件，不授权扫描额外点。

本次再次 fetch 后，三个评审分支仍为 `f7936299fa6272fbf50db6b94a1bd0333808ea09`、`9673381676e18ed0afbc6114e0a62bea9c48002c` 和 `3e9f0080def8c029cceedbd35184b4de7b8b96bc`。topdown 的三方边界和难点继续落实到上述义务；证明端点数量不是 novelty 或作者负担改善的证据。依赖 preload、一般深度 affine pointer 源、性能和同例 proof-burden 比较仍开放。
