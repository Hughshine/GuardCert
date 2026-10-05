# 两个变化内存上界：单次迭代消除

这个实例检验同一 guarded rewrite 中两个普通内存读取的定义性、延迟读取和稳定性。它先接通双上界协议与完整编译链；接受域限制为一次迭代，不代表两维动态数组调度已经完成。

## 实际源、条件和候选

源是前端生成的完整两层循环：

```c
for (; i < *rows; ++i)
  for (j = 0; j < *columns; ++j)
    *out = 2;
```

使用者规则产生下列短路检查，失败时执行原片段：

```c
i == 0 && *rows == 1 && *columns == 1 &&
out != rows && out != columns
```

候选是 `*out = 2; j = 1; i = 1;`。顺序与原执行的计数器出口一致，完整内存和所有原程序 temps 都保留。两个上界指针可以指向同一只读单元；只要求写入不影响上界。当前模板是普通 signed32 load／store、严格 `<`、单位自增和 `j=0`，完整 AST 与类型重新核对，volatile、其他增量、其他写入值或 reset 均不选中。

值 2 给出直接反例：`i=0,*rows=*columns=1` 时，如果 out 指向 rows，真实源执行第二行，出口为 `(i,j)=(2,1)`；如果 out 指向 columns，源执行第二列，出口为 `(1,2)`；三个指针相同时出口为 `(2,2)`。无条件消除会全部得到 `(1,1)`。这些路径必须拒绝并保留变化上界的原循环。

## 使用者交付什么证明

`ClightDualLoadedUnitGuard.v` 交付实际条件语法和 `readonly_condition`。其语义域 `dual_unit_domain` 是一个 ghost 原执行完成见证：在同一入口存在安静的正常出口。编译器从源执行导出它，源进展协议另外证明不存在无限的片段内部执行。运行时既不查询这个见证，也不模拟源循环。

检查域按此前接受的性质逐步建立：

1. 真实外层头部给出 i 的整数值、rows 指针与普通读取定义性。
2. `i=0` 且 `*rows=1` 证明外层实际活动。原执行经过 `j=0` 并读取内层头部，由此才得到 columns 的定义性。外层空时 columns 可以未初始化或为 null，条件不会读取它。
3. 再确认 `*columns=1`，原执行的第一笔 store 给出 out 的指针与写权限。两个 bound 只需读权限；对齐 Mint32 的比较和非相交性质由具体语言的内存设施提供。
4. 两个 non-alias 检查通过后，`mint32_load_survives_apart_store` 分别证明写入后两个 bound 仍为 1。

`dual_unit_condition` 实际消费通用的顺序只读条件代数。`loaded_one_condition` 和 `address_apart_condition` 都返回同一种证书，允许规则作者复用它们；后续检查的域使用前面接受的证据。接受意味着提交的前提成立，拒绝不要求前提为假。

`ClightDualLoadedUnitForward.v` 交付实际局部执行证明。它先用真实源前缀取得第一笔合法 store，再构造原两层循环的一次迭代及两个退出头部，最后用安静执行确定性与候选对应。证明保持事件、完整 CompCert memory 和全部 temps，无私有缓存或弱化的出口关系。这个构造消费原 store，不能从一个 detached schedule 推出程序正确。

`dual_unit_rule` 将上述证书放入既有 `readonly_clight_rule`：用户选择源／候选／位置，框架安装条件与原片段回退并提升局部结果。单次替换和多次替换的上下文正确性直接复用，不新增全局证明形式。

## 独立源进展与完整程序

`ClightMixedLoadedProgress.v` 提供可复用的嵌套协议：memory-bound 循环仅保护自身计数器，body 可以改变任意内存上界。严格 signed32 头部活动意味着计数器低于机器最大值，单位自增减少到最大值的距离；内层 framed 协议保护外层计数器。这个 rank 与 guard 接受、读取稳定性和上界初值独立。寄存器上界循环继续使用既有稳定 temp 协议，有限语句和顺序组合共享同一分类器。

`ClightDualLoadedUnitCompiler.compile_dual_units_correct` 将新规则接到完整 `Csem.semantics → Asm.semantics` backward simulation。`ClightCommonRewriteCompiler` 同时选择它并消费新源进展分类器；一般外围 goto、顺序片段、有限／无限外围循环由已有宿主处理。选中片段自身仍须有进展协议；这个实例没有解决任意可能发散的整段版本化。

复现入口是 `make interface-dual-unit-native`。综合入口使用 `python3 scripts/native_interface_dual_unit.py --common`，需先构建 `--common` 编译器。原生脚本核对当前证明报告、编译器和全部证明源摘要，并比较汇编程序、GCC 与每次头部重新读取的独立源模型。明确无限外围函数只编译和检查。

独立与综合入口各通过 3,035 次调用／3,035 行输出，六个函数有七处实际 guarded region。3,000 次网格调用中，入口条件 oracle 分类 36 次接受，其中 30 次两个 bound 共享一个单元；1,800 次 alias 调用包含 306 次外层 bound 改变、300 次内层 bound 改变。统计来自输入／源模型，没有运行时分支计数或性能结果。额外用例包含真正的共享只读单元、空域的 null／未初始化指针、连续两次 rewrite、signed 边界，以及三个 `INT_MAX` bound 被第一笔 alias 写入缩小后合法退出的输入。

全量 Rocq 审计通过 297 个编译接口端点，没有超过既有分层假设基线；纯接口 54 个闭合端点和 Clight 59 个端点保持。二十种提取配置全部重建／回归通过，31 份原生报告核对当前编译器／证明摘要；相对 `2485d94`，29 份原有 source／Clight 摘要相同。加入共享只读及最大 bound 用例后，两入口定向重跑通过，无需重建证明或其他编译配置。

## 两维数组调度还需要什么

这个单元模板的写地址固定，真实第一笔 store 足以建立两个指针比较的安全性。数组调度会遇到更严格的问题：第一笔 store 就可能改变 columns，不能在检查之前把整行假定为入口列数次执行。

后续数组实例需要逐点 ghost cursor，同时保存当前实际内层 tail、当前行完成后的外层 tail、两次 preload 的稳定证据及当前写权限。每个点从真实下一次 store 建立比较安全，分别检查它与 rows／columns 的分离，二者都通过后才推进。换行时重新读取真实头部并 reset 内层计数器。全部检查成功后才能把两个动态头部运输到缓存模型并消费调度证明。

这里不能用数组类型替代整个 footprint 的 CompCert 权限，也不能仅凭入口的维度乘积预设未来地址可访问。通用前缀扫描接口应复用；实际尾执行、读写权限和头部运输继续由 Clight 实例交付。双内存维度的数组交换、多个依赖 preload、大布局及复杂 body 仍列在 [验收账本](optimistic-loop-acceptance.md) 中。
