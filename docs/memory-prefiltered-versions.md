# 检查前缀与提前回退

`3a15b79` 的多方案实例增加了接受范围，但多个方案可能对同一个足迹重复查询。此阶段将廉价检查前缀从已认证的完整检查中识别出来，并改变失败后的控制路径。

```text
前缀拒绝 → 尝试下一方案
前缀接受 → 执行该方案原来的完整检查
              完整检查接受 → 候选
              完整检查拒绝 → 原片段
```

原来的完整检查仍有自己的源回退。前缀接受后，这个已验证命令可以直接作为外层方案的候选，因此外层只需保证前缀安全、状态效果合规。这种结构的正确性不要求框架知道“失败”的具体语义，也不需要证明失败等同于前提为假。

## 暴露的接口和证明

`GuardMemoryCheckPrefix.memory_check_tree_parse` 识别由 Clight `if`、`Sskip` 和 `Sbreak` 构成的前缀。`memory_check_tree_parse_sound` 把识别结果绑定到实际 AST；`memory_check_tree_decode` 从实际执行得到条件树结果、相同 temporary、相同内存和静默 trace。完整检查在定义域内可执行时，`memory_projected_tree_prefix` 推出这个前缀也可安全执行。

这里没有额外假设前缀表达式必定定义：定义性由原检查的真实执行证明提供。不支持的前缀保持原有组件。

`GuardMemoryPrefilterVersions.memory_verified_guarded_rule` 将一个已认证的 `(check,candidate)` 与源回退组合成正确命令；它消费语义无关的 `stateful_versions_preservation`。`GuardMemoryPrefilterComponents.memory_prefilter_components_valid` 证明实际组件转换有效；列表转换保持长度和所有组件有效性，`memory_prefilter_component_list_sound` 给出实际 `projected_region_contract`。

`GuardMemoryPrefilterGroups` 复用原有源包、profile 搜索、候选验证和组件提取。统一完整程序端点仍对任意不受信任提案器成立；`request_guard_prefilter` 只是提案元数据，不能绕过验证。

## 入口与范围

```text
(prefilter (versions (per-axis (schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0))))))
(prefilter (versions (per-axis (tile 2 3))))
```

原有普通、单方案和完整多方案入口保留各自路线。这个实例的前缀是根游标、次数和稳定地址参数范围；它不包含实际地址扫描。前缀通过后执行原完整检查，所以范围判断可能重复，但后续方案的地址扫描可以被省去。原片段也可能在生成代码中出现多次，文件大小不一定减少。

通用证明保证源观察保持，不保证任意组件列表的接受范围保持。不同方案可能使用不同性质，提前回退会跳过它们。本实例使用同一源足迹的分离条件；完整同源逐入口对照已验证这批输入的实际选择相同，并分别测量查询与代码大小。不能由结构正确性推出最弱条件、最优选择或运行时间加速。

## 当前证据

四个新语言模块和统一编译器已增量编译通过；主入口全量审计重编译了 376 个适配模块、七个 lowering 模块及三个抽象核心模块，526 个证明源码哈希一致。三个抽象核心均无全局公理，完整程序端点精确保留原有 42 项继承假设。新编译器已提取并原生构建，SHA-256 为 `5c52045dc038b830d1a4a4991ce1e99ea98644b9c6ea5946873b87730b783cf7`。

测试复用相同的八个循环内核及 637 组输入，Source SHA-256 为 `651feed91d241915346445729b6238285ae7e85c75e519fd033d2890ed464ad0`。固定完整多方案基线位于 `/tmp/guard-parameter-versions-verified`。

前后版本各通过 **8281 次完整汇编调用**，全部缓冲区和公共循环变量与独立源模型及 GCC 一致；新版本另完成 **4288 次 Clight/GCC 分支诊断**。逐入口的外层坐标、定义／未定义地址参数、选择的版本、候选执行与回退次数精确相同：1810 次函数调用进入候选，4330 个片段入口进入候选。49 个空片段入口上的未定义地址参数仍在读参数或查询地址之前回退。

实际地址查询由 **735722 降为 653276**，减少 **82446（约 11.2%）**；260 次函数调用减少查询，每个函数调用的查询均未增加。新旧方案元数据相同，新记录的尝试列表是旧记录的相同前缀；提前终止位置满足范围通过、地址检查拒绝。

直接二维配置的 Clight 文本 `355263 → 468900 B`、汇编文本 `410017 → 434279 B`。这里只测量源码／文本文件大小和插桩检查次数，没有测量运行时间，查询减少不能直接推出速度更快。详见 `build/native-memory-prefilter-versions/comparison-report.json`。

五组普通路线（12922 次汇编调用、10321 次诊断）和两组单方案路线（14511 次汇编调用、7887 次诊断）完成完整回归；native／branch 报告与上一版逐项相同，仅编译器哈希不同。原完整多方案入口的一、二、三维和错误证书做了定向回归，全部逐配置字段相同；没有将定向回归称为完整旧多方案配置回归。各对照报告位于 `build/prefilter-*-comparison-report.json`。

复现新入口为 `make native-memory-prefilter-versions`。保留固定旧编译器和报告时，可运行：

```sh
python3 scripts/compare_memory_prefilter_versions.py --baseline /tmp/guard-parameter-versions-verified
```
