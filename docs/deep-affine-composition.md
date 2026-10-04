`affine_candidate_evidence` 支持递归组合。外部优化器可以提出中间 Loop IR 和各段证据；已证明的检查器核对每一段，最后返回原源片段到最终候选的证书。

```text
AffineChainEvidence middle first second
AffineDomainEvidence conditions nested
AffinePartitionTargetEvidence conditions base nested
```

`checked_affine_candidate_correct` 对证据结构归纳。链式证据先检查 `source → middle`；只有接受后才检查 `middle → candidate`。两段证书都使用同一参数环境、范围前提和初始逻辑内存，且保持同一最终内存，因此可以传递组合。中间片段并非依次执行的额外运行阶段。

域证据使用 `affine_partitioned_sources_execution` 将原源执行转换成完整分区的执行，再应用嵌套候选证书。分区仍在每个原迭代点内按源顺序展开。分区与分块组合并不自动把各分区移到独立循环；这种重排仍需要相应候选和依赖检查。

目标分区证据先验证 `source → base`，再用可计算的完整 AST 相等检查核对 `candidate = affine_partitioned_sources conditions base`。相等检查覆盖所有表达式、测试、具体指令及参数；不匹配即拒绝。已证明的完整分区等价随后建立 `base → candidate`，避免把复制站点的这一步重新交给通用依赖验证器。它不允许任意分区重排或修改叶子。

最终证书保持原有 `memory_bounded_source_certificate` 接口。因此原源派生的数值、真实数组地址与别名检查、最终候选的机器 lowering、公开出口恢复，以及完整 Csem→Asm 定理均复用原有路线。只有最终候选进入生成的快路径；拒绝任一段即保留源片段。

外部数据可以描述以下组合：

```text
(chain
  (map-index ((shift 0 -1)) shifted-source)
  (tile-box 2 3 ((-3 9) (0 16))))

(partition
  ((le (var 1) (constant 0)))
  (tile-box 2 3))

(partition-target
  ((le (var 1) (constant 0)) (le (var 0) (constant 1)))
  (tile-box 2 3))
```

第一个例子先提议 `i'=i+1`，再对中间片段分块。`shifted-source` 必须是完整具体 Loop IR，包含所有修正的子循环头和指令参数。恢复映射和分块 witness 都是待验证的数据。

`tile-box` 可显式提议各轴的有限整数盒范围；省略时使用源请求的范围。产生器保留中间循环的域测试和叶子代码，将它们放入盒中，然后提出分块候选。检查器必须证明盒没有遗漏中间源的迭代点，且最终候选保持依赖。盒范围和分块大小不具有可信地位。

`scripts/affine_composed_candidate.py` 提供直接分块、单／双切面加分块，以及平移加分块的数据模式。错误模式分别提出未证明的第一段、错误分块 witness、未按证据展开的最终 AST 和缺少源点的盒。运行 `make native-affine-nest-composition`，在实际 CompCert 汇编上比较完整数组和公开出口，再对发出的 Clight 单独观察快路径与回退。

该递归数学接口不固定组合层数。当前 native 语法限制每次分区最多两个切面，沿用有限源轮廓及私有变量池限制。各段共用一个运行时前提；没有为每段独立合成条件，也没有证明完整的前提搜索或最弱前提。

验证成本的已知限制：四个二层／三层函数上的双切面加 `2×3` 分块，经源展开后交给通用验证器，在默认 oracle 预算（每查询 4,000 行、100,000 次操作）下触发 600 秒编译超时，未得到汇编结果。失败配置和日志保存于 `/tmp/guard-domain-tile-two-cuts-timeout-20261004`。这不是候选被静态拒绝的证据。保序 `1×1` 的同一路线也触发 600 秒编译超时，记录保存于 `/tmp/guard-domain-tile-two-cuts-unit-timeout-20261004`。新增目标分区证据处理完整展开这一步，原有源展开路线仍保留；其余域变换的验证成本仍须逐项测量。

目标分区入口已完成九组、合计 **4,428 次实际 CompCert 汇编调用**。直接 `2×3` 分块、源单切面加分块、目标双切面完整展开、索引平移加分块均接受两个独立函数和逐点依赖函数，拒绝未来迭代读取函数。错误第一段、错误分块 witness、缺片目标、遗漏中间源点的盒，以及 oracle 资源限制均不安装候选。每次比较所有三个数组和全部公开控制出口；独立模型分别记录危险分块与缺片的行为反例。

目标双切面加 `2×3` 的上述实际运行在同一 600 秒测试限制内完成。此前通用源展开路线的两个超时实验另行保存，不能合计为通过调用。这里没有严谨的编译时间基准，也没有运行时加速结论。

另外四种合法配置共完成 **1,476 次 Clight 分支诊断**，各观察到 60 次快路径和 309 次回退，合计 240／1,236。它们使用单独保存的诊断源与输出；实际汇编测试保持未插桩。
