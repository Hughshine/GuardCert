# 双 loaded axes：真实标注 C、Pluto/codegen 与 CompCert 安装

2026-10-08。本阶段把 [loaded candidate/host 证明](word-nested-store-affine-compiler.md)
接到实际 C 驱动。提取的 compiler 自动提出 source/model metadata，导出真实
两轴多数组模型，调用 Pluto，验证调度和 tiling transition，调用 prepared
codegen，并由完整候选 checker 重检实际生成的 Loop，最后安装到 CompCert。
没有添加虚拟第三轴、手写候选或源码使用者的语义 callback。

## 使用方式与当前源族

支持族的源码作者给普通 C 和标注。例如：

```c
void loaded_pair(int *a, int *b, int *h, int *k, int alpha, int ld) {
    int i = 0, j = 77;
#pragma scop
    for (; i < *h + 0; i++)
        for (j = 0; j < *k + 0; j++) {
            a[i * ld + j] = b[i * ld + j] + alpha;
            b[i * ld + j] = a[i * ld + j] + alpha;
        }
#pragma endscop
    /* The continuation may observe both arrays and iterator exits. */
}
```

`+0` 对应当前 loaded-header frontend 接受的显式 word-offset 语法，并非
语义前提。普通 `*h` 的便利适配尚未加入此 proposer。边界、非别名等不作为
pragma 的承诺：header 检查拒绝、模型 setup/alias 检查拒绝分别在运行时回退。
两条 store 的同 cell flow dependence 保留，由真实模型验证，不能将它们
当作相互独立的赋值。

当前描述者识别两个 strict signed counted axes，内层 reset 为零，header
为 `*pointer + constant`，body 为赋值列表。物理下标采用二维 Horner 形式，
stride 是正的常量或 int32 temp；坐标可使用已支持的仿射表达式，值表达式可
使用常量、scalar、loads、加减乘。描述和静态 checker 的接受族仍受到 layout、
shape、scalar 与完整候选服务限制。此次运行矩阵覆盖矩形域、行/列布局、
常量 16 和参数 `ld`，不覆盖任意参数化仿射域。

运行入口为：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python scripts/native_word_nested_store_affine.py --validate
```

原 native checkpoint 已保留。重现运行需要新的 `--work` 路径；编译器构建
同样使用新的路径，避免覆盖已绑定的成功文件。独立编译实际 C 时，给
`build/multi-word-nested-native/compiler-v3/ccomp` 设置
`GUARDCERT_TENSOR_MODE=pipeline`、`GUARDCERT_POLYHEDRAL_MODE=tile`、
`GUARDCERT_TILE_SIZES=2,3`，并将 `GUARDCERT_PLUTO` 设为 Pluto 的绝对路径。
标注只选择尝试位置；未标注源码正常编译。

## 新增语言适配及其证明

实际 C frontend 在 for/body 中保留 administrative skips，导致直接使用前一
source checker 时安全静态拒绝。新增
`check_word_nested_store_frontend_affine_region` 对实际 frontend source 使用
既有、已证明等价的 `trim_loop_skips`，再调用前一完整 loaded checker。

`trim_loop_skips_temps` 证明所有被引用 temps 的列表保持。
`word_nested_store_frontend_contract` 把 normalized-source 的 projected guarantee
运输到实际 frontend source；有限 checked table 逐项获得这个 guarantee。
表达式和内存操作不改变。因而目标中的 loaded fallback 是 administrative
normalization 后的 AST，与原 source 有已证明的执行对应，不宣称字节相同。

`compile_selected_word_nested_store_frontend_affine_regions` 仍由既有 expression
host 检查**原 frontend AST** 的 progress、scope、occurrence placement、fresh
typed declarations 和支持的出口，再调用 CompCert tail。其 correctness
endpoint 给出 Csem→Asm backward simulation，并量化三种数据 proposer 和
资源容量。这里没有用 cached progress 代替原源 progress。

新审计查询两个模块的 7 个端点：2 个闭合，最多使用旧 42-global compiler
baseline，没有新增公理，绑定 1,374 个可达文件。审计核对冻结 parent 的
1,380 个绑定。闭包数量较少源于新入口不依赖 parent 的 example 模块，
不是删除其证明。报告：

`build/multi-word-nested-frontend/proof-v1/report.json`

SHA256：`a75699c71cb295c28332c879926568929ce202874f229c75591106554f5a407a`。

## 真实编译流水线

```text
marked C
  -> parser marker labels -> SimplExpr -> SimplLocals
  -> original selected frontend source
  -> proved administrative normalization
  -> ordinary loaded description -> checked header package/cached AST
  -> ordinary access/value/dimension/profile description -> checked model
  -> two-axis source Loop -> ExtractorFrontend -> OpenScop
  -> Pluto scheduling/tiling -> affine + tiling validation
  -> prepared codegen for each actual statement
  -> distributed/completed/rebound Loop proposal
  -> full source/candidate checker
  -> complete header + setup/alias guarded Clight target
  -> selected language-host installation -> CompCert tail -> assembly
```

`GuardWordNestedStoreAffineCandidate` 只提出普通数据。全部 source/body/model
提案由提取的已证明 checker 对实际 AST 重检。`GuardRankedMultiTensorPipelineCandidate`
以 source rank 参数化；本实例传 2。每个 phase 保存 source rank、source Loop、
OpenScop、Pluto 命令/输出、witness、验证结果和实际 codegen 输出。

普通 tiling 运行 identity scheduling 加 tiling，关闭 intratile/diamond 变换；
独立 schedule 配置没有 `--identity`，实际执行 Pluto 调度。单位 tile 的
coordinate completion/reindex、statement distribution 和 bound 调整都是
不受信任提案，必须经过最终完整 checker。Phase receipt 中
`whole-candidate-check=pending` 如实表示 producer 阶段；最终 Clight 安装及
量化 compiler theorem 才覆盖这个 gate，不能拿 receipt 单独声称接受。

提案池容量为 100 个 typed private temps。Header package 使用 7 个，alias
scan 使用 5 个，剩余 88 个可供 counter-pair allocator；前一 99-slot checkpoint
在这一阶段静态拒绝。容量已被正确性定理量化，不需要新增语义假定。

## 动态检查及真实路径

外层检查按 source 的条件读取顺序捕获 header，用原源许可的只读地址扫描
证明写入不改变捕获值。接受后，实际 header-guard 出口提供 cached execution。
Root 空域直接绕开内层参数准备；否则进入完整 numeric/layout/box/profile
和 cross-array alias checks。拒绝分别运行 loaded/cached source；接受运行
实际生成的候选，并恢复公开 iterator exits。

十组配置各运行五种函数 × 二十组输入，共 1,000 次未插桩 CompCert 汇编
调用。另一组 1,000 次 GCC 执行插桩后的 Clight pretty-print，用于检查分支；
不把这些 counters 称为汇编插桩证据。两个检查都比较完整 1,024-word arena
及公开/首次 iterator exits，并与独立 Python 的逐次实际 header 读取和
32-bit word 运算模型比对。原 C 的 GCC `-fwrapv` 结果也独立检查。

| 配置 | header 接受 | 候选执行 | cached 回退 | loaded 路径 | outer 空域 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 行，tile 2×3 | 44 | 20 | 20 | 75 | 4 |
| 行，tile 1×3 | 44 | 20 | 20 | 75 | 4 |
| 行，tile 1×1 | 44 | 20 | 20 | 75 | 4 |
| 列，tile 2×3 | 44 | 16 | 24 | 75 | 4 |
| 行，参数 stride | 44 | 12 | 28 | 75 | 4 |
| 列，参数 stride | 44 | 8 | 32 | 75 | 4 |
| 行，独立 schedule | 44 | 20 | 20 | 75 | 4 |
| 未标注 | 0 | 0 | 0 | 119 | 0 |
| 关闭优化 | 0 | 0 | 0 | 119 | 0 |
| 调度器失败 | 0 | 0 | 0 | 119 | 0 |

每组是 100 次函数调用；重复 region 增加 dispatch 次数，context bypass
减少次数。Header 接受包括候选/cached/empty，不与其后三列相加。Loaded
路径包括动态拒绝和未优化 region，不全部属于 guard refusal。成功配置
每组安装四个实际 sites，分布为 `[1,0,2,1,0]`；包含一个未标注同族函数、
一个 XOR-body 静态 refusal。调度器失败配置保存四个 refusal phase，不安装
候选；关闭/未标注配置不调用 scheduler。

输入包含两数组同址/错一 word、root/child header alias、共享 header、
有副作用的 continuation、两次标注、非零/负起点、profile 外 counts、零/负
stride、RHS word wrap，以及 outer/child 空域时的 NULL child/array pointers。
NULL native 用例检验未发生不合法读取；前阶段 Rocq 的 `None`-cache/array
fixture另行覆盖空域中未定义私有状态，不用 native NULL 代替那项证明。

运行报告：`build/multi-word-nested-native/native-v1/report.json`。
SHA256：`4677113b7e6451a2e7b13bbaaaee39dc3fc27e171fd4d2ae21d957269103a33e`。
报告绑定提取 compiler、proof closure、proposers、helpers 和全部运行文件。
早期安全 refusal/checkpoint 与失败原因仍保留在同目录树，成功文件不覆盖。

## Narrative 的责任与后续验收

已 fetch 全部 branch heads；可见 narrative 仍为
`12419c1e1e3da450bf378742a2fb4e204e51e060`，其两正文与 main 一致。
其澄清对应本阶段的实际分工：

| 责任 | 本阶段的实现 |
| --- | --- |
| Framework kernel | 局部证书/guarded choice 组合；未改 |
| Language/IR | administrative equivalence、safe conditional reads、private/frame/出口运输、原源 progress、selected installation、backend 接线 |
| Domain/optimizer | loaded/header 稳定性与 entry 条件推导、source/model/candidate 对应、真实调度/codegen 提案和其验证、region guarantee |
| Site evidence | marker selection、合法 placement、public scope 与 typed freshness 由已证明 host 检查 |
| 源码用户 | 标注 C 和策略/容量选项，无 execution/simulation callback |

Guarantee/requirement clause algebra 仍是开放设计。本阶段只是消费已有
projected/expression host，不把 local 正确性自动宣称为任意 context closure。
新语言或新 domain 仍需要提供其语义证明；支持族源码作者不补这些证明。

最难的下一项是把已闭合源族的条件变为实用基础设施：从逐点条件构造紧凑
充分 entry condition，证明语言中的安全求值及 actual-exit 运输，复用现有
候选/host 定理，并分别验证接受域、guard 工作、代码尺寸、完整成本和收益。
当前默认 cap 8、header 逐点 scan、cross-array point-pair scan 和复制 fallback
是保守实现，不能据这份功能矩阵声称高性能或完整 OLO 2017 能力。
一般参数化 affine source、scalar/source 扩展和作者负担比较仍在 active goal。
