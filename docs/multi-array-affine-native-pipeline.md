# 多数组 affine：从标注 C 到实际 guard、候选和汇编

日期：2026-10-08。前置为 `e89794c` 的
[完整 factory 与 selected compiler 定理](multi-array-affine-versioned-compiler.md)。
本阶段把同一数据接口接到实际 C frontend、自动 source metadata、真实
Pluto／prepared codegen，以及原样汇编执行。没有修改 kernel、host contract、
已成功证明或旧报告；新的 native producer 由既有量化编译器定理覆盖。

## 源码用户如何使用

用户提供带 `#pragma scop`／`#pragma endscop` 的 C 和 phase／tile 选项。
例如本次实际输入中的两条顺序赋值：

```c
#pragma scop
for (i = start; i < n; i++)
  for (j = 0; j < m; j++)
    for (k = 0; k < c; k++) {
      a[((i * ld) + j) * 5 + k] =
        b[((i * ld) + j) * 5 + k] + alpha;
      b[((i * ld) + j) * 5 + k] =
        a[((i * ld) + j) * 5 + k] + alpha;
    }
#pragma endscop
```

第二条读取第一条的 store 结果，不能把 RHS 读取都提前到检查入口。
新 guard 只比较访问地址，不读取数组元素值。另一个实际输入使用三个数组：
`A[i,j+1,k] = B[i,j+q,k] + q + alpha; D[i,j,k] = A[i,j+1,k] + alpha`。
两种布局分别使用 `(i*ld+j)*5+k` 和 `(j*ld+i)*5+k`。

Native metadata producer 从实际规范化 AST 提出 iterator、bound、scalar、
各条 assignment 的 write/read 和 word-value 表达式。Factory 重检这些数据
与实际 AST 的对应，生产原源模型、完整条件和 region guarantee。
用户不用填写 source/model、NonAlias、guard-safety 或 simulation callback，
也不用手写 candidate Loop。

当前 native 识别三个 temporary-bound axes、共享三维 Horner layout 和常数
component extent；支持 affine coordinates、constant shifts、parameter coordinates
及 RHS 的常量／temp／load／加减乘。描述与 checker 的 identifiers 和 assignment
list 没有固定名称或两条长度限制，但本次 C 验收使用两条 assignment。
Coordinate-only scalar 的既有 source-capability gate 仍保守拒绝；例中的 `q`
也出现在 RHS。默认 count cap 为 8、stride profile 为 `[1,1000)`，component
box 在本例进一步要求 `c <= 5`；这些是明确的保守策略，不是推断出的最弱前提。

## 实际流水线及证书

```text
marked C -> selected normalized Clight source
  -> proposed source data -> checked actual source package
  -> Loop extraction -> OpenScop -> Pluto
  -> checked affine import / affine validation
  -> checked point-space import / tiling validation
  -> prepared codegen per statement
  -> composed Loop proposal / unit completion / affine bound adaptation
  -> final complete source/candidate check
  -> numeric/layout/box/profile guard -> actual-address pair scan
  -> checked candidate + public restore, or original AST
  -> selected Clight host -> verified CompCert backend -> Asm
```

Per-statement codegen 是一个 proposal strategy。Statement distribution、unit
completion 和 bound adaptation 都不受信任；最终 checker 重检实际完整 Loop。
Phase receipt 的 `whole-candidate-check=pending` 只记录 proposer 返回前的状态；
实际 Clight 中安装的完整 guard 和 candidate，另验最终 factory 接受。
因此不能单凭 scheduler／codegen 成功宣称安装成功。

自动调度配置真实调用 Pluto，未传 `--identity`；tiling 配置沿已有 identity
pretransform 后运行实际分块。每次保留 `source.loop`、`before.scop`、mid／after
OpenScop、command／scheduler log、validator outcomes、各 statement 的 raw codegen、
raw/completed/adapted Loop 及 receipt。没有把非恒等调度、最优性或收益归给 Pluto。

完整语句的两层拒绝都执行原 AST：setup 拒绝跳过地址扫描；alias 拒绝从实际
scan exit 回退。接受从该出口执行 checked candidate 并恢复公开 iterators。
源执行许可地址比较；不以入口 NonAlias 假设许可检查自身。Compiler endpoint 是
`ClightSelectedMultiTensorAffineCompiler.compile_selected_multi_tensor_affine_regions`，
其 `_correct` 定理给出完整 `Csem -> Asm` backward simulation。该定理在前一阶段
已独立审计，本次没有新增 Rocq 端点或公理。

## Narrative 的责任边界

再次 fetch 并读取 `origin/topdown/research-positioning`，当前为
`12419c1e1e3da450bf378742a2fb4e204e51e060`；两份 narrative／context 正文与 main
一致，没有待吸收的新差异。本阶段按其实际 compiler 集成要求推进。

| 责任方 | 本阶段复用或提供的工作 |
| --- | --- |
| Framework kernel | 局部 guard／conditional correctness 证书组合；不分析 C、alias 或 schedule |
| Clight language／host | 安全观察／word／pointer 语义、实际 check-exit frame、fresh typed declarations、scope／progress／occurrence placement、context simulation 和 backend 连接 |
| Domain／优化实现者 | source family、充分前提及编码、访问 coverage、source／model 对应、候选完整 checker、data factory 的局部 guarantee；新 native policy 只提出数据 |
| 源码使用者 | 标注 C 与配置；无需补上述语义证明 |

Kernel 止于 local guarded correctness。具体全程序定理由语言 host 消费局部
guarantee 后建立；不是 generic kernel 对任意 context 的闭包结论。Host 条款
拆分保持开放，不为本次接线改 API。后续替换 guard 要复用适用的 candidate／
host 证书，同时单独证明安全、接受充分性和实际出口的状态运输。

## 验收证据

[native-v4/report.json](../build/multi-tensor-affine-native/native-v4/report.json)
SHA-256：`104a4906a58e2fd4d32f959defda711734d4adc14b7265926b730b2960846a2a`，
绑定 891 个文件。Compiler SHA-256 为
`dfaae0545b614358e42a90394a7859db838b5f1b0229594ae4be3613f90153cb`，
绑定前一 proof report `5e599ede01148f0c6718aa4dd5b50d198b05f2b7a52624cfa06ef7d2a001ce79`。

| 配置 | phase 调用 | 实际安装 sites | Asm／独立 Clight 调用 |
| --- | ---: | ---: | ---: |
| row `[2,3,2]` | 5 | 5 | 96／96 |
| row `[1,3,2]` | 5 | 5 | 96／96 |
| row `[1,1,1]` | 5 | 5 | 96／96 |
| column `[2,3,2]` | 5 | 5 | 96／96 |
| row automatic schedule | 5 | 5 | 96／96 |
| 全部未标注 | 0 | 0 | 96／96 |
| disabled | 0 | 0 | 96／96 |
| scheduler failure | 5 | 0 | 96／96 |

每配置六个 functions、十六组输入，共 768 次未插桩 Asm 调用。完整 1,024 个
array words 和公开／首个 region 的 iterator 出口，均与独立 Python word model
及 GCC `-O0 -fwrapv` 原 C 参考一致。输入覆盖共享 backing allocation 的不相交
views、同址与部分 overlap、稀疏 footprints、空 outer/null pointers、空 child、
非零 start、cap／stride／component／coordinate 拒绝及 wrapping RHS。

独立 GCC Clight derivative 的另 768 次调用记录实际分支，并重新核对完整输出。
每个正常配置出现 27 次 candidate region 执行和 84 次 original region 执行，
其中 11 次 original 来自 alias 拒绝；两 marked regions、未标注同族、不支持
XOR、周围 memory effects 和 conditionally skipped region 均检查。分支计数按
region 执行计，不能与输入调用数相加；不把插桩 Clight 分支宣称为 Asm 路径证明。

首组 96 次 Asm 已在 native-v1 成功，后因检测 regex 不接受 PrintClight 换行而
未完成报告；native-v4 复用该成功编译和输出，记录来源及 hashes。中间 relative
path 和原 loop 检测失败均保留；未重建成功 compiler、proof objects 或旧实验。

## 复现与仍需完成的工作

以下假定已完成 README 的工具链、proof checkpoints 和 scheduler 准备：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/build_multi_tensor_affine_compiler.py
python3 scripts/native_multi_tensor_affine.py
# 已有 checkpoint 只读核对：
python3 scripts/native_multi_tensor_affine.py --validate
```

Builder 只用于空的新 compiler checkpoint；已有成功 binary 不覆盖。
测试 C 来自 [multi_tensor_affine_fixtures.py](../scripts/multi_tensor_affine_fixtures.py)，
自动数据／candidate policies 分别在
[GuardMultiTensorAffineRegionCandidate.ml](../prototype/interface/native/GuardMultiTensorAffineRegionCandidate.ml)
和 [GuardAffineMultiTensorPipelineCandidate.ml](../prototype/interface/native/GuardAffineMultiTensorPipelineCandidate.ml)。

此族 actual C integration 已完成，但完整 active goal 没有完成。下一困难语义
位置是同族 loaded 两-store 原源的逐步 header 值保持与下一次读取许可，不能
先假设完整 cached rectangle 执行。一般 affine domains、coordinate-only scalar
receipts、紧凑条件、三类 guard 指标（code size／runtime work／接受域）、完整
成本和 OLO selected-source 比较继续推进；本次没有新的成本或收益结论。
