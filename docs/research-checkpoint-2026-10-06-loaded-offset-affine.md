# 2026-10-06：loaded＋offset 根的完整编译链

此阶段把上一轮 [expression-header 服务](research-checkpoint-2026-10-06-expression-headers.md)
接到真实 recursive affine guard、候选／factory、语言 host 和新 Csem→Asm 入口，并提取运行。
遵循 narrative `226ba94` 的澄清：功能链先闭合；扫描是中间实现，成本／条件生成仍是验收。
[接口与证明顺序](loaded-offset-affine.md)说明三方责任以及原观察与计算结果的区别。

## 已接通的功能

真实 C 的根 header 为 `i < *limit + signed_constant`；支持稳定 temp 的任意有限层 canonical
仿射 children、实际 Mint32 数组读写、原地更新、多数组、交换与基本分块。实际源码选择器
提出 pointer／delta，checked site 核对原 AST，原源 header 在回退路径保持。

原 load 为 2、cache 为 3 而 body 写中 limit 的 fixture，证明 guard 拒绝且原源两轮后停止。
同 block 的不相交 offsets 可接受并导出 cached-source 执行。真实机器路径确认交换和分块
各有不同写入顺序，同函数两次改写各执行候选；不同位置写中 bound 的源保留 row 2 的实际
出口。短数组源的地址检查只观察 indices `[0,1]`，拒绝后没有比较未来 index 2。

## 验证结果

| 证据 | 本次结果 |
| --- | --- |
| 新 Rocq 端点 | 56：1 language host、42 domain／factory／compiler、13 fixtures |
| 实际依赖／绑定源码 | 567／1,047；17 个新 Rocq 模块 |
| Compiler 全局假设 | 42；没有超出现有 CompCert／PolCert compiler 基线的新假设；kernel 保持闭合 |
| 提取入口 | `ClightGuardedLoadedOffsetAffineMultiCompiler.compile_offset_affine_multi_regions` |
| 完整汇编 | 六配置 × 118 调用 = 708；完整数组与 public exits 对独立机器整数模型和 GCC `-fwrapv` 参照 |
| Clight 分支诊断 | 两配置 × 118 调用 = 236；每配置 41 fast、76 fallback 分派，另有未安装的源调用 |
| 未修改汇编机器探针 | 21；交换／分块、重复 regions、同 block 切片、alias 回退、bound 改变与短路地址检查 |
| 实际 guard 工作量 | 74 个源点；accum3 为 74 次、multi3 为 `74 + 3×74² = 16,502` 次 pointer comparisons |

六配置是 disabled、interchange、tile-2-3、wrong-reindex、invalid-domain 和 FM 资源耗尽。
错误候选／资源耗尽保留原源；实际 loop-carried dependence 的交换被拒绝。新增负根和
`INT_MAX + 1` 机器回绕空域，data pointers 为 null 时保持 body 未执行；child 的未到达参数
也不会因 guard 被额外读取。成功安装从 emitted Clight 验证，实际分支／写序另外观察。
这些是固定样例的功能证据，41 fast 不是 benchmark 接受率。

报告位置和 SHA-256：

| 文件 | SHA-256 |
| --- | --- |
| `build/loaded-offset-affine/proof/report.json` | `29199aada7e687155fc9dc7dbc2f242f5fb9f89a065cba6cc141bfdf5ea36bbc` |
| `build/loaded-offset-affine/compiler/.guard-build.json` | `80671a972e026d24907e24947d0529718459628ecc62ac168da3297f11ed852b` |
| `build/loaded-offset-affine/native/report.json` | `d978140ecb350ac1bb1d74e134b0c5ca43ffddee476eede6639ad96996b3dfd2` |
| `build/loaded-offset-affine/native/path-report.json` | `1c47775bf69d4e0ab2ad7a2ead2e62f86bcadcf180a44d24bca46306940ada08` |
| `build/loaded-offset-affine/guard-work/report.json` | `01ddbbef28343d46ea3d3ae45dc2979dec1fd5311aa0d081030fa18246d952e0` |

编译器 hash 为 `f4d8763fc5e6a972ba7cd706ccb4b1fbce506fd01c3c047d2c25ccbd217aa9b8`。
工具链仍为 pinned CompCert 3.18、Rocq／Stdlib 9.2。新报告继承并复核原 expression-header
报告；旧 reduced compiler、624 native／208 Clight／21 machine、Figure 2 coverage 和 guard
work 绑定也复核通过，未重跑旧矩阵。没有覆盖或重写历史报告。

## 重现与未完成项

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-offset-affine-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-offset-affine-native
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-offset-affine-validate
```

前两项要求已验证的 `build/expression-headers/proof/report.json` 及其 inherited dependencies；
没有验收空 build 目录的独立 bootstrap。native 路径／工作量探针的 GDB 需要本地调试权限。
新 validator 核对 proof、object、extraction、native helper、输出和探针日志的摘要。

本阶段消除 Figure 2 的根 loaded-expression 接入缺口，但没有支持其第二 loaded child，
[原 coverage](olo-figure2-coverage.md)仍为 `not-supported`。没有完整 BT kernel、一般
projection、guard 最小化、独立计时或 profitability 结论。16,502 次比较的例子显示还需减少
实际扫描工作，不能因提取链或打印代码通过就认为满足高效条件生成。

后续继续层次源前缀／conditional child capture 和安全 compact sufficient conditions。
过去 stores 对新 observation 的影响、inner cached-source 不能预先假设这两个难点已加入
[当前计划](current-work-plan.md)。每实例人工证明／metadata 负担和 CGO 同例对照继续评估。
完整主目标保持 active。
