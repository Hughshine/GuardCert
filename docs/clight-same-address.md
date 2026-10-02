# 同地址读取的实际端到端实例

`ClightSameAddress.v` 添加一个依赖内存有效性的性质维度，并复用现有通用条件编译器与完整程序宿主。在两个普通 unsigned32 load 的地址相同时，插件将 `*p + *q` 改成 `*p + *p`。后端据此消除重复读取。

生成的实际 Clight 条件树是：

```c
if (p == q) {
  if (1) return *p + *p;
  else return *p + *q;
} else return *p + *q;
```

这里同地址检查提供正证据；地址不同返回 unknown，经框架进入原表达式。此实例没有把不相等的指针当作字节范围不重叠的证据。

## 检查为何可执行

源表达式的一次有定义求值提供两个 load 的证据。它们推出入口 temporaries 含有效指针，内存具有读取权限，因此 CompCert 的指针相等比较有定义。检查本身只读取 temporaries，没有执行额外 load。

当前 CompCert 的 `Mem.loadv` 还检查访问终点处于指针范围。局部证明保留完整 `loadv` 证据：检查接受时两个指针相同，将右侧 load 的证据转给候选的 `p` load，包含权限和范围检查。完整程序宿主在实际插入点从原表达式求值建立入口域，无需全局 alias 或地址有效性假设。

识别器要求两个 pointee、结果和指针类型精确匹配普通 uint32／uint32 pointer；signed 与 volatile 类型不匹配。深层表达式宿主允许嵌套运算、临时赋值、赋值右侧和 return；既有程序 simulation 处理调用、循环、label 和 goto。

## 定理与原生证据

`same_load_rule_correct` 将性质维度、实际 validity/value 表达式、入口域与局部求值证明交给 `encoded_tree_rule_sound`。`select_memory_rewrites_sound` 与既有算术插件组合。实际提取入口 `RegionCompiler.compile_property_regions` 已使用这个组合，正确性终点仍是 `Csem` 到形式化 `Asm` 的 backward simulation。

原生检查包括五个相同地址边界、25 个不同地址输入对、unsigned wraparound、空指针前置分支、signed／volatile 排除，以及赋值目标与输入别名的情况。输出与 GCC 的原程序相同；实际 Clight dump 含四棵生成的条件树与原表达式回退。

锁定的 x86_64 编译结果还显示 `load_pair` 的接受路径读取一次内存，回退路径读取两次，原生脚本核对这一形状。这里没有运行时间收益测量。

```sh
make check-integration
```

原生报告为 `build/native-alias/report.json`；编译器假设对照为 `build/alias-assumptions-report.json`。上游编译器端点与新增组合端点的 35 个假设相同，新增全局公理为空。解析、打印、系统汇编、链接与 libc 仍属于原生执行检查的边界。
