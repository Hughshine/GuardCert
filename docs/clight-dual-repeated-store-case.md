# 两个动态内存上界下的幂等写入循环化简

这个实例覆盖一个有实际运行时前提的循环化简。源在两层 memory-bound 循环中反复向同一个普通 signed32 单元写入 0：

```c
for (; i < *rows; ++i)
  for (j = 0; j < *columns; ++j)
    *out = 0;
```

接受条件为 `i==0 && 0<*rows && 0<*columns && out!=rows && out!=columns`，按此顺序短路。上界可以是 signed32 范围内任意正值，也可以共享一个只读单元。候选为：

```c
*out = 0;
j = *columns;
i = *rows;
```

候选仅写一次输出单元，再保留两个真实出口。使用者选择源、候选和位置，框架安装条件与原循环回退；这个例子没有私有 cache，也不需要在 guard 中计算或遍历 `rows*columns`。它不提供数组调度，和 [固定 2×2 的双 loaded 数组交换](clight-dual-loaded-matrix-case.md)是两种局部证明。

## 规则作者提供的事实

[ClightStoreIdempotence.v](../prototype/interface/ClightStoreIdempotence.v) 提供语言事实 `store_result_fixed`：一次实际 `Mem.store chunk before block offset value = Some after` 之后，同一写入在 after 上得到 after。本定理对任意 chunk/value 成立，分别证明字节覆盖、权限和 nextblock 的保持；实际 memory 记录相等使用既有 CompCert proof irrelevance。`storev_result_fixed` 接到机器指针表示。

示例规则的源语法核对限制为一个普通 signed32 常量 0 写入、两个严格 signed 自增 loaded 头，以及内层 reset 为 0。其接口没有从任意 body 自动发现幂等性；改换常量或 body 需要相应的语法／实际执行证书。volatile 输出或上界、不同步长和 reset 不属于这个模板。

[ClightDualRepeatedGuard.v](../prototype/interface/ClightDualRepeatedGuard.v) 注册 `loaded_positive`、真实有符号比较及安全域。外层 bound 正且入口 i 为 0 才能获得源外层活动，从真实 reset／内层头证明第二个 load 有定义。两个 bound 都正时，真实第一笔 store 给出输出 pointer 的定义性与写权限；两个读取分别给出 bound pointer 的读权限，才证明地址比较安全。条件接受分别蕴含两项 non-alias；检查自身不写状态。

[ClightDualRepeatedLoops.v](../prototype/interface/ClightDualRepeatedLoops.v) 构造任意有限 signed 上界的两层实际执行。第一次写入后内存保持为那个实际 store 的结果；两个读取靠分离事实保持不变，内层每次 reset／退出和外层增量都有真实执行。源活动计数器严格小于其 signed 上界，因而单位自增不会超过 signed 最大值；这一事实也在构造中交付，没有计算一个可能溢出的维度乘积。

[ClightDualRepeatedForward.v](../prototype/interface/ClightDualRepeatedForward.v) 先用真实源前缀获得第一笔 store，构造具有相同内存与 `i=*rows,j=*columns` 出口的已知源执行和候选执行，再用静默确定性与任意实际源结果对应。源完成性与候选确定性补足精确片段等价的反方向。任意正尺寸的自然数归纳是 ghost 证明，不在提取后的 guard 中运行源循环。

框架仍只消费条件、局部等价和上下文证书。幂等性、整数上界、load 稳定性和源进展均由 Clight 实例证明；语义无关核不解释这些性质。

## 回退和完整程序

写入可能改变任意一个 bound。例如入口 rows、columns 均为 1，但 out 指向 rows：源第一笔写入将 rows 改为 0，但已进入的迭代仍完成自增，最终 i 为 1。若 out 指向 columns，最终 j 为 1；若两个 bound 与 out 同址，两个 counter 都为 1。未经检查，当前候选将把对应 counter 直接设置为更新后的 0，给出错误出口。当前候选在检查全部通过后才写输出，且非别名事实证明它随后读取的两个上界等于源中保持的值；alias 输入执行原两层 loaded 头。

[ClightDualRepeatedCompiler.v](../prototype/interface/ClightDualRepeatedCompiler.v) 返回精确 `readonly_clight_rule`，独立入口为 `compile_dual_repeats`，完整端点 `compile_dual_repeats_correct` 是 Csem→Asm backward simulation。综合 pass 也选择该规则，经既有精确规则嵌入进入 projected host。源进展复用 `ClightMixedLoadedProgress`，允许回退路径改变两个上界；不借用检查接受后的稳定性。

## 复现与当前证据

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-dual-repeat-native
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-common-native
```

独立与综合入口各通过 3,035 次实际 C 调用／行输出；六个函数有七处实际 guarded region。生成 Clight 核对五项条件的顺序、单个输出 store、两项 counter 恢复及原双 loaded 头部回退。程序与 GCC、无诊断的 GCC UBSan 和逐头读取的独立源模型一致。

3,000 次网格调用中，输入／模型分类 144 次入口接受，其中 90 次两个 bound 共享单元；1,800 次 alias 调用包含 432 次外层 bound 改变和 450 次内层 bound 改变。数字是输入与源行为统计，没有测量实际分支次数。额外 35 次调用包含共享只读 bound、空域、连续替换和 signed 边界。

全量 Rocq 审计通过 333 个编译接口端点，既有 FRAGMENT=6、MEMORY=1、REGION=6、PROJECTED_REGION=8、STEPWISE=8、COMPILER=35 基线外没有新增全局公理。纯接口 54 个闭合端点与 Clight 59 个端点保持；840 份证明源码摘要一致。全部 22 种提取配置重建／回归通过，35 份原生报告绑定当前证明报告和编译器；相对 `c711ed9`，33 份已有源码／生成 Clight 摘要相同。

fixture 覆盖正、零和负上界、非零初始 counter、两个 bound 与输出的三种别名、共享只读 bound、未初始化／null 内层指针的空外层、空内层的 null 输出、连续两次 rewrite，以及 `INT_MAX` 上界被 alias 写入缩小后合法结束。明确无限的外围函数只编译并检查。极大的非别名正维度由证明覆盖，未在原生 fixture 中执行其漫长源循环；没有性能结果或运行时分支计数。

本例的普通常量单元写入、入口 counter 0 和正常两层循环是明确限制。一般数组 footprint／调度、多个依赖 preload、复杂 body 以及旧 affine／tiling 主接口迁移仍在 [Optimistic Loop Optimization 验收账本](optimistic-loop-acceptance.md)中。
