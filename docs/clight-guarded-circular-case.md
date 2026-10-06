# 完整 unsigned 循环：安全检查、bound 缓存与无限 alias 回退

2026-10-05。这个规则把真正可能无限的整段源循环接到新小步宿主和完整 Csem→Asm 编译端点。它检验了框架的一项接口需求：source 的有限性可能来自接受的前提，不能预先要求拒绝分支也满足 source progress。

## 输入和实际 rewrite

使用者选择如下实际 Clight 模板对应的 C 循环：

```c
unsigned i = start;
for (; i != *bound; ++i)
  *out = i + 2U;
return i;
```

生成的控制流对应于：

```c
if (i != *bound) {
  if (out == bound) {
    for (; i != *bound; ++i) *out = i + 2U;
  } else {
    private_bound = *bound;
    for (; i != private_bound; ++i) *out = i + 2U;
  }
} else {
  for (; i != *bound; ++i) *out = i + 2U;
}
```

`private_bound` 是编译器新鲜的 unsigned temporary。guard 的普通读取和指针比较只读；cache 写入属于接受分支的 candidate，不改变 condition 的只读契约。当前 lowering 生成两份完整原循环和一份候选，未做新宿主上的共享回退。

选中空循环时不比较 out，因而允许 out 为 null。活动且地址相同则回退。活动且不同地址的 Mint32 word 在实例已证明的有效地址／对齐域下分离；每次实际写入不改变 bound 的 load。候选保持原有所有 store、i 的 unsigned wrap、完整 memory 和所有原 temps 的出口。

## 前提与 condition 如何定义

[ClightCircularGuard.v](../prototype/interface/ClightCircularGuard.v) 提供：

| 对象 | 定义与证明用途 |
| --- | --- |
| `D = circular_guard_domain` | 实际头部的普通 Mint32 load 有值；头部活动时 out／bound 的指针比较有定义 |
| `P = circular_guard_property` | 头部活动且两个实际单元分离 |
| `circular_guard_accept` | 头部不等且非 same-address 的 Boolean 编码 |
| `circular_dimension`／`circular_primitives` | 将上述正前提注册到已有 readonly loaded-tree 合成接口 |
| `circular_condition` | 生成条件的安全、完成、只读与接受蕴含 P 证书 |
| `circular_guard_synthesized` | 生成的实际决策树等于所插入的头部／alias 树 |
| `circular_domain_from_prefix` | 实际活动头部和首次实际 store 足以建立 D，不用 source completion |

D 没有预先假设 bound 稳定或整个循环终止。比较安全来自有限真实源前缀的 load／store 证据；运行时不执行该 ghost 前缀。bound 的权限不是生成程序可直接读取的布尔原子。

合成覆盖已注册的语义子集，不从任意 `Prop` 自动推断最弱 condition。该例子注册一个组合原子；已有 Boolean 组合、分阶段域和扫描设施仍可复用。

## 局部证明与全局接入

[ClightCircularMachine.v](../prototype/interface/ClightCircularMachine.v) 把规范化 Clight 循环、实际头部、store、单位自增和循环 continuation 分成十七个控制阶段，并证明阶段转移就是实际 Clight 小步。`++i` 在真实 frontend 中采用 signed `1` 常量与 unsigned iterator 的运算；规则匹配这一 AST，不能将源码外观相近的另一个 AST 当成已经选中。

[ClightCircularSimulation.v](../prototype/interface/ClightCircularSimulation.v) 的局部关系有三个阶段：有限源前缀、相同原循环回退、loaded／cached 循环对应。前缀中允许目标留在入口，但索引每次下降；首次 store 后目标 guard 与所选分支追上源。之后每个源步都有一个目标步，不需要 guard-independent source rank。接受后的 load 稳定性由 [运输库](../prototype/interface/ClightCircularTransport.v) 的实际 store 定理保持。

规则作者交付 `guarded_circular_contract`，选择器证明 `choose_guarded_circular_sound`。通用 [open-region 编译适配](../prototype/interface/ClightOpenRegionCompiler.v) 负责整程序 temps／freshness、遍历、结构 continuation、globals 和公开出口。最终：

```rocq
compile_guarded_circular p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target)
```

[ClightGuardedCircularCompiler.v](../prototype/interface/ClightGuardedCircularCompiler.v) 先运行已有 `transform_common_regions`，再运行新整段规则；两次实际 Clight forward simulation 组合后进入 CompCert backend。新规则与旧 load-hoisting 在同一函数中交替执行，每次 guard 使用当时的实际 bound／parameter。

语言无关核无需新增“unsigned”或“bound”字段；新能力位于具体语言的上下文宿主。另一个语言若支持相同模式，需提供自己的只读选择、状态关系、零步下降和上下文插入定理。

## 发散不是通过跑超时推断的

当 out 和 bound 是同一个可写 word，且入口值不等于 i，首次 store 写 `i+2U`，接着 i 变为 `i+1U`。下一次头部仍不等。每轮保留 word 的读写权限，unsigned wrap 不改变这一事实。

[ClightCircularDivergence.v](../prototype/interface/ClightCircularDivergence.v) 构造整个源循环的真实 `forever_silent`，并证明 guard 走原循环回退后的目标也有真实 `forever_silent`。输入范围不限于 start=0、bound=2。这两个定理与小步协议都已编译；没有执行原生无限循环来替代证明。

[ClightCircularProgress.v](../prototype/interface/ClightCircularProgress.v) 另证明缓存候选以 unsigned 模距离有限到达固定 bound。该定理没有被要求作为原循环的无条件进展证书，也没有进入新的宿主记录。

## 复现与验证范围

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-guarded-circular-native
```

输入程序为 [guarded_circular.c](../prototype/interface/tests/guarded_circular.c)，检查脚本为 [native_interface_guarded_circular.py](../scripts/native_interface_guarded_circular.py)。脚本核对当前 proof report、全部证明源码和提取 stamp，比较实际编译器输出、GCC 与独立 unsigned 源模型，并检查真实 Clight 中的候选、两份原回退与 alias 测试位置。

540 次有限 kernel 调用／540 行输出通过；五个函数中六处完整循环替换已检查，36 次混合函数调用交替执行两处新循环与两处旧 payload preload。有限输入覆盖 UINT_MAX 附近 wrap、非 alias 活动循环、空 alias、null out 空路径、只读 bound、跳转前驱、嵌套外围和改变参数后的当前入口。volatile bound、步长 2 和不同 body 被精确 AST 选择器拒绝。非空 alias 用实际无限执行定理和所生成回退覆盖，不原生执行。当前整体报告数值见 [研究记录](research-checkpoint-2026-10-05.md)。

当前模板不是任意循环 body、signed overflow、任意内部调用／return 或一般多面体调度。全程序端点是 CompCert backward simulation；不称作 C 与汇编的双向等价，也没有运行性能结论。
