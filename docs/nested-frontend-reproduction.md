# Nested compiler：独立源码树复现

入口位于 `scripts/reproduce_nested_frontend.py`。它导出当前已提交的 HEAD，在
独立源码树中恢复锁定依赖，重建当前 compiler，并运行既有实际 C 输入矩阵。
此入口不读取此前各阶段的 proof report，也不复制编译对象。

## 使用方法与构建边界

先准备 `toolchain.lock.json` 指定的工具：OCaml 4.14.1、Rocq／Stdlib 9.2、
Menhir 20260209，以及项目已有的 OCaml 依赖。当前复现复用已安装工具链，
不声称重新安装了 opam packages。常用调用为：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/reproduce_nested_frontend.py \
    --destination /tmp/guard-nested-fresh \
    --polcert-source /path/to/pinned-polcert-git-repository \
    --machine-probes
```

`--destination` 必须是新目录；省略时自动创建 `/tmp/guard-nested-source-*`。
复现脚本本身、standalone audit、fetch 脚本和 Makefile 须先提交，使导出的
版本与运行的入口一致。其他 dirty files 不会进入 `git archive HEAD`。

`--polcert-source` 是 Git object cache：恢复器使用 `git show <pinned-commit>:<file>`
和已锁定的 source／compatibility patches，不读取该目录的工作树或 `.vo`。
省略时按现有恢复器克隆锁文件指定的 upstream。CompCert 从 checksum-pinned
release archive 恢复；`--compcert-archive /path/to/archive.tar.gz` 可以使用本地
发布包，仍核对同一个 SHA-256。没有匹配 source pin 的 vendor 目录不会被复用。

`--machine-probes` 运行本地 GDB 子进程探测，需要环境允许 ptrace；省略时仍跑
实际 assembly、Clight 分支和更窄 profile 的矩阵，不宣称新的 machine-path probes。

## 执行链与证明责任

复现器首先绑定 Git revision、源码 archive 与全部导出文件，确认初始没有
`build/`、`vendor/` 或编译对象，然后执行：

1. 恢复 CompCert，configure x86_64-linux／clightgen，完成该目标的 `make proof`。
2. 恢复 optimizer profile 的锁定 PolCert 源码和补丁。
3. 编译当前 GuardCert／PolCert 依赖闭包，并直接查询定理 assumptions。
4. 使用既有 `build_nested_frontend.py` 提取和编译真实 compiler driver。
5. 重跑 adapted source、七类 BODY／contexts、Clight branches 和 one-column profile。
6. 可选重跑已有 assembly-path probes；核对新树中的所有报告与产物绑定。

Standalone audit 使用当前 CompCert、memory、fragment 及 mapped／tiling checker
端点作为独立基线，不读取旧报告。当前 compiler 定理的 assumptions 必须等于
这些基线的并集，其他查询端点不得增加 assumptions；kernel 必须闭合。它将
实际源码、编译对象、工具版本、查询日志和 audit helpers 写入新树中的
`build/nested-frontend/proof/report.json`，供原提取／native scripts 消费。

这里没有新的 compiler correctness 定理。结论仍来自
`ClightGuardedNestedFrontendCompiler.compile_ncs_frontend_regions_correct`：
成功返回目标程序时，取得 Csem→Asm backward simulation。复现建立的是从
锁定源码到这些证明／实际编译行为的可重建性；它不增加支持的 source class，
也不把测试数变成语义定理或 profitability 证据。

新树可直接使用 `make nested-frontend-from-source POLCERT_SOURCE=/path/to/cache`。
Standalone audit 会拒绝覆盖历史类型的 proof report，因此建议使用导出入口。
已有阶段的 proof、native、Clight 与 GDB reports 保持不变。

## 结果与核对

完整复现已通过，源码版本为 `1d3acc0cb8a38341ba105ba321e745e9b3a0704b`，独立树为
`/tmp/guard-clean-nested-20261007-r2`。1,853 个导出文件开始时没有 generated artifacts。
实际编译当前目标的 CompCert proof 与 585 个 GuardCert／PolCert 依赖；独立报告
绑定 884 个 source digests、767 个 objects，查询 20 个端点，compiler 的基线并集
仍是同一 42 项，kernel 闭合，零新增 global axiom。复用已安装工具链。

新树重跑 48 adapted-source、714 BODY／context、238 one-column profile calls，
以及 path harness 的 27 calls，共 1,027 successful full assembly calls；另两个
错误无 guard 变体作 dependence counterexamples。Clight 的 16＋357＋238＝611
calls 与 6＋10＝16 machine probes 单列。Probes 只观察指定 stores，不能称作
全部 store trace。全数组、public counters、headers 和 context markers 的核对
与原矩阵一致；这些结果是可重建性证据，不代表 source class 扩展或收益测量。

最初 `beea7d4` 的空树已暴露 audit 的未编译基线 query 依赖；加入两个 baseline
checker roots 后，完成查询预检查，并从修复版本重新导出第二棵空树重跑。
没有将修补后的第一棵树称为完整 source-only reproduction。Failure wrapper
记录另存为 `build/nested-frontend/reproduction/first-failure-wrapper.log`／
`first-failure.json`。旧阶段报告没有覆盖。

外层 `build/nested-frontend/reproduction/report.json` 绑定源码 export、14 个成功
步骤的命令／logs／退出码、工具版本、compiler 与全部内部 reports。报告 SHA：
`e7e7b1422f84825f7731c72f59551e835d5e62d3940e553a923eaa92587d4afa`。
新 compiler SHA：`dbe2035ef71cff5ca1030eeb536b965db273a19b2cec2268f61791ad58a66a79`。
Standalone proof report SHA：
`65e5a4492b762aa629da81628ba2ea9d857c641f3ee168402418678fae6f4284`。
各内部 report 继续绑定实际 inputs／outputs／probes；该报告不是 bit-for-bit binary
reproducibility 声明。记录的构建耗时只描述一次复现，不作为优化成本测量。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/reproduce_nested_frontend.py --validate
```

`--validate` 只读已有 reproduction artifacts；它不重建、不下载、不启动 GDB。
下一个实现使用者是 [constant-word observation](constant-word-observation.md) 的
actual guard producer；该库已证明 BODY effect，但尚未安装 runtime shortcut。
主要研究待办仍是 compact sufficient conditions、guard／完整运行成本、
实用接受域、作者证据工作，以及更广 affine/polyhedral source 和动态布局。
