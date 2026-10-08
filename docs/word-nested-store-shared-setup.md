# 双 loaded 源族：共享 setup 分派与配对代码尺寸

2026-10-08。本阶段在 [实际 C/polyhedral compiler](word-nested-store-native-pipeline.md)
上复用已有 Clight check-plan lowering。Numeric/layout/box/profile 的语义条件、
实际 alias scan、候选 checker 和外层 header guard 均保持；setup 失败改为
一次 flag 分派到共享 cached fallback。新的 Csem→Asm 入口、提取 compiler
及同一真实 C 矩阵已通过。Kernel 和 host contract 没有改动。

## 已证明的改变

此前内层版本将 `tree_statement setup alias_versioned cached_source` 直接
展开，许多拒绝叶子各有一份完整 cached source。新的版本是：

```text
check_plan_code (tree_check_plan setup) setup_flag
if setup_flag then
    原 alias scan + candidate/cached-source 分派
else
    cached_source
```

`tree_check_plan_spec` 保持原 decision tree。每条完成的 check-plan 路径写入
Boolean result 后才读取它；不要求这个私有 temp 在入口已定义。条件中的
短路读取、安全求值和接受充分性来自前一 setup 定理，不因 lowering 改变。

`multi_tensor_shared_setup_flag` 在实际候选 checker 接受后，遍历 typed int32
pool 并检查 `check_plan_resources`。它选择一个不被 condition、alias/candidate
statement、fallback 或公开 live set 引用的名字。`find_some` 和既有 typed
allocator 定律证明结果属于 typed pool，frameable/fresh 条件由布尔检查生产。
找不到资源时静态拒绝，不请求源码作者提供 flag、frame 或 execution callback。

`multi_tensor_shared_setup_execution` 取得原 source 执行许可的 setup decision。
接受时复用原 alias/candidate 执行定理，拒绝时使用 source 执行，再消费
`check_plan_guarded_normal_execution`：新 flag 对分支不可见，运输实际执行，
保持原 final memory 和请求的 public temps。这里复用原 `C_opt`、condition
正确性和语言运输服务，不重证 polyhedral transformation。

`check_multi_tensor_shared_setup_full` 保留原 scan allocation、counter pool
和最终 candidate gate。随后 `nwspp_shared_setup_execution` 将同一服务接到
实际 header-guard 出口。Root 空域仍跳过整个内层准备；header refusal 仍执行
与原 frontend 对应的 loaded source，内层 refusal 执行 cached source。
Domain producer 导出既有 projected guarantee，administrative adapter 运输到
原 frontend AST，既有 expression host 检查原源 progress/placement/freshness。
`compile_selected_word_nested_store_shared_regions_correct` 给出 Csem→Asm
backward simulation，并量化普通 proposers 及资源容量。

## 接口与责任

源码使用方式仍是标注 C 和策略选项。新入口：

`ClightSelectedWordNestedStoreSharedCompiler.compile_selected_word_nested_store_shared_regions`

三个 proposer、selection 和 typed-pool count 与前一入口相同。原 native
metadata、真实 rank-2 Pluto、affine/tiling validators、prepared codegen 和
最终 generated-candidate checker 全部复用；默认 pool 仍为 100。

| 责任 | 本阶段承担的工作 |
| --- | --- |
| Framework kernel | 消费局部证书/guarded choice；未改 |
| Language library | 原 check-plan lowering、result 初始化、执行/公开 temp 运输、安全条件读取、selected installation/backend |
| Domain/compiler factory | 原条件/source/model/candidate 证据的组合；自动 checked flag 选择；region guarantee |
| Site/source user | 原标注 C 和策略数据；不增加语义 callback |

共享 lowering 是已有语言服务的复用证据，不宣称这个控制表示本身新颖。
Guarantee/requirement clause algebra 仍保持 narrative 中的开放设计状态。

## 证明和功能验收

三个新模块查询 11 个端点：1 个闭合，其余在前一 42-global baseline 内，
无新增公理；报告绑定 1,376 个可达文件，检查冻结 parent 的 1,374 个绑定。
成功 proof objects、提取 compiler 和运行文件均保留；失败尝试只增加新的
日志，没有覆盖成功输入。

- Proof：`build/multi-word-nested-shared/proof-v1/report.json`，SHA256
  `cd4677b6ea4729cbb855eab0689868fb7b23ed01bfaee2520a7f7f9e9293d98f`。
- Native：`build/multi-word-nested-shared/native-v1/report.json`，SHA256
  `1b87c8f3b3f6af1c9fd6e32a45352d48225bcbb230b4e118b4f7271eed918431`。

十组相同的真实 C 配置各运行 100 次函数调用：1,000 次未插桩 CompCert
汇编和独立 1,000 次插桩 Clight 调用通过，比较完整 arena/public exits、
独立逐次 header/word 模型和原 C GCC reference。每组 source、outputs 和
观察到的 header/candidate/cached/loaded/empty 路径与前一 compiler 相同。
成功配置仍安装 `[1,0,2,1,0]` 四 sites；root/child/header alias、条件空域、
参数 stride、单位 tile、真实 schedule、重复标注、continuation 和 scheduler
失败保持原检查。Clight counters 不称为汇编插桩证据。

## 配对尺寸结果

`measure_word_nested_store_shared_size.py` 核对两份报告的全部 digest bindings，
比较相同 C/input/策略，保存 `nm -S` 原始输出并计数 emitted Clight 中的
root-source loops。以下是单 region 的 `loaded_pair` 链接后函数字节数：

| 配置 | 前一版本 bytes | Shared setup bytes | Root-source 副本，前→后 |
| --- | ---: | ---: | ---: |
| 行，tile 2×3 | 2,750 | 1,442 | 36→4 |
| 行，tile 1×3 | 2,698 | 1,332 | 36→4 |
| 行，tile 1×1 | 2,469 | 1,181 | 36→4 |
| 列，tile 2×3 | 2,850 | 1,426 | 36→4 |
| 行，参数 stride | 3,195 | 1,594 | 40→4 |
| 列，参数 stride | 3,200 | 1,596 | 40→4 |
| 行，独立 schedule | 2,469 | 1,181 | 36→4 |
| 未标注/关闭/调度器失败 | 113 | 113 | 1→1 |

四份分别是 header refusal、outer empty、setup refusal 和 alias refusal。
重复 region 有八份。该计数是静态表示尺寸，不是运行次数。未标注/unsupported
函数、case driver 和 main 的字节数/副本数在每组配置中保持一致。普通
2×3 配置减少 47.56% 函数字节数；这不是 source 的速度提升，也不等于
消除了 guard 的动态工作。

尺寸报告：`build/multi-word-nested-shared/size-v1/report.json`，SHA256
`1f7713031a3cdc0347f453a5b6aee506652a3be3aa39a97f66d062270d83fd93`。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python scripts/audit_word_nested_store_shared.py --validate
python scripts/native_word_nested_store_shared.py --validate
python scripts/measure_word_nested_store_shared_size.py --validate
```

完整重建/运行使用各 helper 的新 `--work` 路径，不覆盖这些 checkpoints。
这里没有新增 CPU timing、完整 guard 工作量或盈利性结论。

## 区间条件的实际语义边界与下一项

调查发现，现有 observed affine envelopes 要求运行时共同基址；它们不能
直接替代任意两数组的 point-pair scan。CompCert 3.18 的
`Val.cmpu_bool`/`Val.cmplu_bool` 对不同 block 的 pointer ordering 经
`cmp_different_blocks` 返回 `None`（eq/ne 另有定义性要求）。因此直接生成
`a_last < b_first || b_last < a_first` 不能普遍证明安全。Pointer cast 也不
自动给出具有跨 block 顺序语义的整数地址。相关实现见
`vendor/CompCert/common/Values.v` 的上述定义及 `Cop.cmp_ptr`。

这是一项语言实例的表达能力约束：可提供共同对象证据、已有共同基址的
数值区间条件、另行证明的 check primitive，或其他可安全编码的充分条件。
不能把区间图形看起来不相交就当成实际 Clight check 的定义性证明，更不能
暗中让源码作者补 same-block 假定。基于共同基址的已验证 envelope 服务保留。

下一项继续处理已闭合源族中的重复 probe/静态事实 residualization，验证
安全、接受域及实际 guard 工作，再做完整配对成本。Header 逐点 scan、
cross-array point-pair scan、cap 8、一般参数化 affine domains 与 OLO 完整
功能/可用性、作者负担比较仍在 active goal；本阶段没有把它们标记完成。
