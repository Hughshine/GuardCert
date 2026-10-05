# 内存上界与实际二维循环交换

2026-10-05。本例把此前分开的稳定 memory-bound 读取和二维调度连接到同一次 guarded rewrite。它消费主只读接口，局部证明连接完整 Csem→Asm 端点；当前接受尺寸为 2×2，不能视作一般 memory-bound 多面体编译已经完成。

## 源、候选与条件

使用者提交实际 Clight source、candidate 和如下模板的语法／类型证书：

```c
int i = start, j = 99;
for (; i < *rows; ++i) {
  for (j = 0; j < columns; ++j)
    cells[i*2+j] = i*10+j+1;
}
```

`cells` 是类型已核对的四元素 signed32 数组；`rows` 是普通 signed32 指针，`columns` 是 signed32 temp。接受检查为 `i==0`、入口 `*rows==2`、`columns==2`，以及 `rows` 与 `cells+0` 至 `cells+3` 这四个实际对齐 word 地址不同。条件按此顺序短路，不写 temp／memory，不产生事件。

候选读取 `*rows` 到新鲜私有 temp，改成 `j` 外层／`i` 内层，保持同一个实际地址和机器 RHS。局部调度确实从 `0,1,2,3` 变为 `0,2,1,3`。候选只在自己的执行里写 snapshot；guard 不用 scratch。源 fallback 保留逐头部 memory-bound 读取，公开出口 `i`、`j`、原程序其他 temps、完整内存和控制 outcome 都受保护。

## 检查安全没有预设矩形完整有效

入口域包含实际源 header 的求值依据，以及宿主提供的正常源完成执行；没有包含 non-alias、上界稳定或完整四 word 写足迹。运行时不查询这份 ghost 完成证书。当前宏片段宿主仍需要独立源进展，不能凭局部正常执行等价覆盖选中循环的发散路径。

[ClightLoadedMatrixSyntax.v](../prototype/interface/ClightLoadedMatrixSyntax.v) 的 `loaded_matrix_row_step` 从一个实际活动外层迭代，提取当前行的两次 CompCert store 及源 tail。inner bound 已核对为 2，因此这行的两次 store 不依赖外层 `rows` 在行内是否被改变。该提取没有稳定性前提。

[ClightLoadedMatrixGuard.v](../prototype/interface/ClightLoadedMatrixGuard.v) 的 `loaded_matrix_alias_run` 在入口内存中执行所有测试。证明先从真实第一行得到前两个地址的权限；只有两次比较均 non-alias，才用两个实际 store 的 load 不变性证明下一次外层头部仍读取 2，进而提取第二行。后两个地址的入口权限再由实际 store 的权限保持倒推得到。任一比较 alias 时立即拒绝，不要求后续地址安全。

这里不能先假定整个入口 bound 对应的二维 footprint 安全，然后以这份 footprint 证明 guard 或稳定性。源可能在第一行改变 bound 并提前结束；这个合法源应原样回退。

## 可复用的源进展设施

[ClightNestedStrictProgress.v](../prototype/interface/ClightNestedStrictProgress.v) 的 `strict_framed_progress` 接受：

- 实际头部为真蕴含 outer iterator 小于 signed32 最大值的定理；
- inner body 的既有 `framed_progress` 证书，保护 outer iterator；
- 自增及实际 header 的语言语义。

body 可以含已有证书支持的循环和 temp 更新，也可以改变 bound 所指内存。外层 rank 使用机器最大值至 iterator 的距离，body 的 rank 来自自己的协议；不用入口 `*rows`、non-alias 或 guard 接受事实。协议排除被选源内部无限静默推进，允许无定义的访问 stuck，不是内存安全分析或所有输入必定正常终止的定理。

`loaded_nested_supported_sound` 把实际 `<*bound` source 形状和结构化 body frame 核对接到该设施。框架的语言无关核没有因此增加机器整数或内存语义；这是 Clight 提供的宿主能力。

## 局部到完整程序

[ClightLoadedMatrixLoop.v](../prototype/interface/ClightLoadedMatrixLoop.v) 的 `loaded_matrix_cached` 逐个真实活动 body 保持当前 iterator 范围、两次实际写入后 bound load 不变、columns 和 cache temp。已有活动头部运输定理将源转成真正的 cached-bound 循环执行。

`loaded_matrix_forward` 再用已证明的源行序解码、真实 CompCert store 交换和候选编码，保持同一完整内存。新鲜 temp 的入口运输和公开出口观察允许私有值不同；源完成性与候选确定性补足条件性等价的反方向。检查域、安全、范围、稳定性、调度与公共出口分别有证书，不能用脱离源程序的列表重排替代它们。

[ClightLoadedMatrixCompiler.v](../prototype/interface/ClightLoadedMatrixCompiler.v) 核对完整 source AST、inner body、reset／increment、变量隔离和 cache freshness，返回 `readonly_projected_clight_rule`。`compile_loaded_matrices_correct` 为 Csem→Asm backward simulation。统一入口也已加入这个使用者规则及新的进展分类器；多个位置各自执行实际入口检查。

## 执行记录与边界

复现目标为 `make interface-loaded-matrix-native`、`make interface-common-native`。199 个完整编译接口端点编译／假设审计通过，没有新增全局公理；纯接口 43 个闭合端点、原 Clight 57 个端点不变。独立入口与统一入口各通过 668 次实际 C 调用／673 行输出、七处真实 guarded loop regions。十五种提取配置重建回归通过，21 份既有源码／Clight 摘要相同。新 [C fixture](../prototype/interface/tests/loaded_matrix.c) 的独立定义源模型包含 668 次变换函数调用／673 行输出：648 网格、六个空路径的后行单元 alias、六个 signed 极值空头部、三个活动依赖的未初始化 inner bound，以及五次两阶段调用。

活动第一行 alias 可以提前退出或增大上界。`rows=&cells[0]`、入口 2 时，第一次 store 改为 1，源只写第一行；未 guarded 的 cached 2×2 候选会多写第二行。`rows=&cells[1]`、入口 1 时，第二次 store 改为 2，源执行额外一行；回退不能仍使用入口 1。脚本逐单元与完整 iterator 出口核对两种现象。

本 fixture 的活动第二行 bound alias 会将 bound 写成 11 或 12，随后源访问四元素数组之外，因此不作为合法原生输入执行；第二行地址比较的安全由机械证明覆盖，并检查其实际生成代码。明确无限外围只编译／检查，没有运行它。

一般运行时尺寸、参数 stride、多个依赖 preload、RMW 或一般 affine／tiling 仍未由本模板支持。当前只读决策树有七个拒绝出口，各保留完整 source 的代码副本；代码大小和检查成本尚未优化，没有性能测量。这个实例解决一项此前缺少的组合，仍不满足 [Optimistic Loop Optimization 验收账本](optimistic-loop-acceptance.md) 的全部主线要求。

报告分别位于 `build/interface-loaded-matrix-native/`、`build/interface-common-loaded-matrix-native/`，绑定当前 source、Clight、汇编、提取编译器和 199 端点审计报告摘要。原生候选次数未额外插桩；实际候选与 fallback 的语法、读取位置、四地址比较顺序和私有声明由 dump 核对，结果与 GCC 和独立源模型逐行一致。
