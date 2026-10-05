# 两个内存上界下的实际数组循环交换

这个使用者实例将两个 loaded bounds 接到真正的数组调度。接受域固定为 `i=0, *rows=*columns=2`，数组为四个 signed32 单元；两个普通整数指针可共享同一只读单元。候选按列优先写入，与源的行优先顺序不同。本实例补充 [一次迭代消除](clight-dual-loaded-unit-case.md)，仍不提供一般两个动态内存维度的矩形编译。

## 使用者提交什么

源片段为：

```c
for (; i < *rows; ++i)
  for (j = 0; j < *columns; ++j)
    cells[i*2+j] = i*10+j+1;
```

使用者给出候选、条件与源语法证书。示例选择器先提出结构描述，再核对完整 source AST、两个 loaded loop 头、初始化与增量、四单元数组类型及完整 store 表达式。改变 RHS、volatile bound、不同增量或内层初始化均不能获得本模板的证书。发现和选择仍是使用者 pass 的职责。

实际只读条件按下面的顺序短路：

1. `i==0`；
2. `*rows==2`；
3. `*columns==2`；
4. 对 `p=0,1,2,3`，依次核对 `cells+p != rows` 与 `cells+p != columns`。

条件表达式不改变入口状态。它的接受蕴含入口 counter、两个读取值及八项实际 word 分离性质；拒绝仅意味着没有获得候选所需的证据。它不是把任意逻辑断言直接转成 C。

全部检查通过后，候选使用一个新鲜 cache：

```c
cache = *rows;
for (j = 0; j < cache; ++j)
  for (i = 0; i < cache; ++i)
    cells[i*2+j] = i*10+j+1;
```

两个上界分别已经证明为 2，因此一个 cache 可以供两层头部使用。候选的实际 store 次序为 `[0,2,1,3]`，源为 `[0,1,2,3]`；所有原程序 temps、内存、trace 和控制出口得到保持。cache 以及共享适配层的 Boolean 均为宿主声明并证明新鲜的私有变量。

## 局部证明怎样推进

入口域包含源的实际正常完成见证，而不预设两个 bound 稳定。源进展由 `ClightMixedLoadedProgress` 单独证明：signed 单位增量的最大值 rank 保护 counter，body 可以改变内存上界。这个 ghost 完成见证不在提取后的 guard 中执行或查询。

[ClightDualLoadedMatrixPrefix.v](../prototype/interface/ClightDualLoadedMatrixPrefix.v) 保存两层真实续执行。`dual_matrix_open_row` 从当前外层活动解码初始化和内层执行，同时保留该行之后的外层增量／tail；`dual_matrix_inner_step` 只解码当前一个 store 和它之后的内层 tail。第一笔写入可能改变 `*columns`，因此不能在完成这一笔的两项 alias 检查之前假定整行都有两次迭代。

[ClightDualLoadedMatrixGuard.v](../prototype/interface/ClightDualLoadedMatrixGuard.v) 在每点分别完成两个比较，再用两项分离性质证明两个 load 在该 store 后仍为 2。只有这些事实成立，才推进到下一点。跨行时 `dual_matrix_close_row` 用真实的内层退出及保存的外层尾到达下一行。实际 store 给出的写权限、load 给出的读权限，以及 CompCert 的存储权限运输，证明当前与后续地址比较在入口 memory 中有定义；数组类型和逻辑尺寸本身不能代替权限证据。

[ClightActiveLoopTransport.v](../prototype/interface/ClightActiveLoopTransport.v) 区分循环头 invariant 与活动 body invariant。在头部允许 counter 为 2；活动 body 只允许 0 或 1，自增后回到头部 invariant。它要求语言实例提供测试运输、实际 body 对应及增量运输。[ClightDualLoadedMatrixLoop.v](../prototype/interface/ClightDualLoadedMatrixLoop.v) 用此协议同时冻结两个 loaded 头，并运输整个源循环的真实 store 行为。

[ClightDualLoadedMatrixForward.v](../prototype/interface/ClightDualLoadedMatrixForward.v) 随后消费既有实际内存调度交换证明，构造完整候选执行。freshness／temp frame 将 cache 的私有变化与公开出口分开；保留 `i=2,j=2` 和全部数组单元。源完成性、候选静默与确定性补足观察等价的反方向，没有将一个单向局部模拟冒充双向等价。

## 怎样接回完整程序

[ClightDualLoadedMatrixCompiler.v](../prototype/interface/ClightDualLoadedMatrixCompiler.v) 的 `dual_matrix_rule` 返回绑定实际 source 的 `readonly_projected_clight_rule`。框架已有的只读宏片段宿主负责入口域、检查安全、候选／源分派、公开观察和 continuation 运输。

独立入口 `compile_dual_matrices` 使用共享出口适配：每处候选和源回退各生成一份。抽象 condition 仍只读，实际生成的私有 Boolean 写入由共享适配层的 freshness／scope 定理处理。完整端点 `compile_dual_matrices_correct` 是 `Csem.semantics p` 到 `Asm.semantics target` 的 backward simulation。

综合入口 `compile_common_rewrites` 先尝试这个模板，再尝试单 memory-bound 模板和其他规则。它复用原来一个候选 cache 的 pool，且使用原来的直接检查树适配，因此每处有一份候选和十一份回退。现有宏片段 pass 与逐步比较 pass 的完整程序证明继续组合；选择顺序本身不属于通用核。

两个例子说明回退的重要性：入口 `cells={2,8,9,10}`、两个尺寸都为 2，若 `rows=&cells[0]` 而 columns 分离，源第一行将 rows 改成 1，结果为 `{1,2,9,10}`、`i=1,j=2`。若 rows、columns 都指向 cells[0]，第一笔写入使两者变成 1，结果为 `{1,8,9,10}`、`i=1,j=1`。无检查的缓存交换会写满四个单元。已安装的 rewrite 在第零单元比较处回退，执行原两层读取。

## 复现与边界

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-dual-matrix-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-common-native
```

独立与综合入口各通过 22,303 次实际 C 调用／22,303 行输出，六个函数有七处实际 guarded region。结果同时与 GCC、GCC UBSan（无诊断）和独立逐头读取模型一致；生成 Clight 核对十一项条件的顺序、一个 cache、两层缓存头及完整原循环回退。

22,266 次有效网格调用中，输入／模型分类 42 次入口接受，其中 36 次两个 bound 共享单元；20,814 次 alias 调用包含 666 次外层 bound 改变和 618 次内层 bound 改变。10,134 个候选网格调用因源越界或超出有限测试预算而未执行。额外 37 次调用覆盖空域、共享只读 bound、顺序替换和机器边界。这里没有把输入分类报告为实际 candidate 分支次数。

全量 Rocq 审计通过 317 个编译接口端点；FRAGMENT=6、MEMORY=1、REGION=6、PROJECTED_REGION=8、STEPWISE=8、COMPILER=35 的既有基线外没有新增全局公理。纯接口 54 个闭合端点和 Clight 59 个端点保持。全部 21 种提取配置重建／回归通过，33 份原生报告绑定当前证明报告与实际编译器；834 份证明源码摘要核对一致。相对 `2181c5f`，31 份已有 source／生成 Clight 摘要相同。

运行 fixture 覆盖两个 bound 的独立／共享地址、同一数组的各个单元、空外层的 null／未初始化内层指针、共享只读 bound、连续两次 rewrite、外围循环与 goto，以及 `INT_MAX` bound 被第一笔 alias 写入缩小后的合法执行。源越界、溢出或超出有限测试预算的输入在调用前排除；明确无限的外围函数只编译并检查。入口分类统计与实际运行时分支计数不同，没有性能测量。

本阶段仅接受固定 2×2、单个静态四单元数组和一个特定纯写 body。一般动态 rows／columns、多个依赖 preload、参数 stride 的同次双 loaded 组合、复杂 body，以及旧 affine／tiling 到主只读接口的迁移仍待完成。

后续的 [双动态尺寸矩形](clight-dual-dynamic-rectangle-case.md)已在独立共享入口扩展到两个不同 runtime memory bounds 和两个独立缓存；本页固定 2×2 的接受域、综合入口代码及本阶段历史验证数字保持原有含义。
