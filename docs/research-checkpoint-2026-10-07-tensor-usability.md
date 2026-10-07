# Checkpoint：tensor 检查、完整成本和证明归属

后继于 `494f6c3`。本轮没有修改 compiler、guard、candidate checker、kernel或
语言host，原181端点和216 assembly／108 Clight calls的报告保持。
针对同一实际source family补齐独立成本实验和可核对的作者责任清单。

## 实测与证据

[成本报告](tensor-region-cost.md)记录30轮、8输入、4版本，共960 fresh-process
CPU batches；正式计时使用未插桩CompCert汇编，不与build重叠。完整RMW结果
按真实重复次数独立生成，核对6,144 words和公开出口／外围markers。
数组初始化、warmup和完整核对均在计时外；每次调用没有数组reset。

实际Clight prefix诊断中，三个接受域的30／1,125／4,805迭代点均执行39次
条件判断，无loop扫描或input-array loads；identity／interchange／tile逐项相同。
拒绝路径为1到31次判断，具体失败位置单列。它们不是机器操作数。

当前source按行连续访问。三个接受输入的interchange完整配对成本约为source
的1.14–1.22倍，tile约1.06–1.25倍；没有净收益。回退路径也存在更快／更慢的
布局结果，不能把source与guarded差值当作纯guard成本。所有raw batches、
IQR、校准和配对比值保留，未选择性删除slowdown。

Cost report SHA256：
`80459c66b80689c1b348677a17330d46d2c4453558765d5e2e629a2c3ba9bc49`。
Raw samples：
`4b6445566d331685af2261940470f226713fd2a07a43aa26f7b17072560ea4b9`。

[证明归属清单](tensor-proof-ownership.md)将39新增查询端点分为10个语言服务、
14个tensor factory／rule、5个compiler接线和10个fixtures；审计保留此前142
tensor queries，实际证明复用既有source／guard／candidate和语言host。已有family的一次使用只提交
九字段metadata和candidate/witness，无新增SOURCE／BOX／bindings等语义callback。
新source grammar／domain和首次语言host仍有明确的对应、条件、状态和安装证明。
物理LOC不是作者工时，也不是其他framework同例工作量的比较结论。

Ownership report SHA256：
`18d37a4d81d17f4ef46569baddd66401d1e937a50cb3d50aca3f5509c103fe2a`。

## OLO 对照与下一项

[功能／算法核对](olo-tensor-comparison.md)重新对照作者PDF的Figures1–2／§§5–7。
当前tensor支持实际Horner地址和动态stride，但本例没有两个grid loads／+1和
第三层literal bound。之前固定布局loaded实例的能力不能与本例相加冒充完整BT。
OLO仍是功能、自动条件处理和usability的验收参照。

下一项优先用已证明的parametric coordinate factory接入原先按列访问、交换后
按行访问的真实源，检查数据提案能否直接复用此证明链，并测量有利重排场景。
随后继续literal-bound transport、loaded-bound与动态layout的实际组合、更多
body／跨tensor alias／affine domains。没有新的泛化kernel或任意contract algebra。

本轮没有OLO／Polly benchmark对跑、真实workload接受频率、原BT性能或其他
verified framework作者工时结果。完整目标继续active。论文正文与evidence map
同步当前实测和这些边界。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_region_usability.mk validate
```
