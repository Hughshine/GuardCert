# 一次实际 guarded load 提升的使用者证明

2026-10-05。这是新只读接口的循环实例，参照 [Optimistic Loop Optimization](https://compilers.cs.uni-saarland.de/papers/doerfert_cgo17.pdf) 的稳定读取需求。它证明普通参数 load 的循环提升；循环上界来自内存的情况仍待接入。

## 使用者选择实际片段

源片段是：

```c
for (; i < n; ++i)
  *out = *parameter + (unsigned)i + 1U;
```

候选片段是：

```c
private_snapshot = *parameter;
for (; i < n; ++i)
  *out = private_snapshot + (unsigned)i + 1U;
```

使用者的选择器从实际 Clight 提出循环形状，再核对完整循环协议、body AST、类型、操作符、常数及标识隔离。这里允许 frontend 在 body 中留下 `Sskip`／sequence，但每次实际执行都必须对应唯一的上述赋值。候选增加的 temp 来自新鲜 pool，并声明在目标函数中；其结果不属于原程序可见状态。

使用者提交的前提为 `i=0`、源循环头接受，以及两个指针的单元分离。实际检查先测试 `i==0`，再测试 `i<n`，最后比较 `out==parameter`，相等回退，不等进入候选。条件本身只读取入口。`stable_load_guard_primitives` 将这一检查作为有证书的原子，Boolean 合成核生成实际 Clight 树及其接受可靠性证书；没有自动发现任意两段程序的充分条件。

## 域与前提分别证明

入口域包含计数器和上界的机器整数定义性。只有在 `i=0` 且源循环会进入 body 时，才要求参数 load 有定义，两个指针可进行比较。域由实际源执行的循环头及第一次 body 导出：源必须读取参数并写出结果，前者给出可读能力，后者给出可写能力和对齐。参数不需要可写。

这些是 ghost 证据。检查代码不读取 CompCert 的 block、权限或 footprint。活动路径的指针比较安全，但空路径不要求指针有效，也不执行候选的 preload。这个域尚未断言 load 在循环里不变；不变性是在 non-alias 前提接受之后证明的，避免将它作为自身的依据。

比较的对象是两个普通对齐的 Mint32 单元。同一 block 中的不同对齐单元，以及不同 block 的有效单元，都可以分离。不同指针值不能推广为任意宽度／不对齐访问的区间分离。这个实例的循环只反复写一个单元；数组访问的动态足迹还需要更一般的区间证书。

## 使用者如何证明局部等价

证明由以下可复用设施连接：

1. [ClightCountedLocalization.v](../prototype/interface/ClightCountedLocalization.v) 把实际计数循环解码为逐次实际 body 执行，并提供反向编码。局部入口保留原入口的其他 temps，只设置当前机器计数器。body 必须证明 temps 写界；这里 body 只写内存，实际循环次数仍在运行时决定。
2. [ClightStableLoadBody.v](../prototype/interface/ClightStableLoadBody.v) 从实际 load／store 推导对齐和访问定义性；`mint32_load_survives_apart_store` 证明每次分离写入后，参数 load 保持原值。数据仍使用机器 unsigned 加法，允许回绕。
3. [ClightStableLoadLoop.v](../prototype/interface/ClightStableLoadLoop.v) 在每一个执行前缀中保持参数读取值，将实际 body 的 load 替换成私有缓存值，再编码候选循环。完整内存和公开循环出口保持；只有私有 temp 可以不同。
4. [ClightReadonlyProjectedLoopRule.v](../prototype/interface/ClightReadonlyProjectedLoopRule.v) 复用单向执行运输。它显式要求源完成性、候选原始执行确定性及观察运输，建立条件性局部等价；完成性来自实际源执行和源进展宿主，运行时不能查询它。

循环上界是 signed 32-bit temp。接受时 `i=0<n≤Int.max_signed`，所有需要执行的增量都在上界之前；计数器不回绕。这个事实不能替代一般初始化表达式／地址表达式的 overflow 前提。数据 RHS 的回绕则被原样保留，不要求它满足整数模型的加法。

## 嵌回完整程序

[ClightStableLoadCompiler.v](../prototype/interface/ClightStableLoadCompiler.v) 是这个实例的使用者 pass。它返回 `readonly_projected_clight_rule`，提交检查、局部等价、源入口域及源 temps 写界。框架复用 `PrivateRegion` 宿主：收集所有原程序 temps，检查 pool 的 freshness，追加目标函数声明，再运输外围语句、函数入口和 continuation。被替换的计数循环提交进展证明；外围程序可以有调用、goto 或无限循环。

完整端点是 `compile_stable_loads_correct` 的 Csem→Asm backward simulation。它使用已证明的投影 Clight forward simulation 和 CompCert 编译链，没有声称完整 Clight 双向行为等价。当前公共集合保护所有原程序 temps，不使用自动 liveness 分析来忽略已有变量。

## 可执行验收

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-stable-load-native
```

这条命令先编译并审计证明，提取 `ClightStableLoadCompiler.compile_stable_loads`，再编译实际 C fixture。验证包括 guard 确实插入、snapshot 确实被候选 loop 使用、源 body 在回退中保留，以及逐单元和 iterator 出口的 GCC／独立期望比较。报告位于 `build/interface-stable-load-native/`。

实际结果为 727 次调用、727 行输出通过，包括 360 个别名矩阵输入、360 个同 block 分离输入、三个空循环 null 调用及四个只读参数调用。四处 Clight 中确认 guard、实际快照和使用缓存的候选循环。

具体别名反例是 `i=0,n=2,out=parameter,初值=0`：原程序最终写入 3，省略 guard 的缓存候选会写入 2。该输入必须保留原循环。空循环 null 指针、只读全局参数、数据回绕、goto、外围循环以及未支持 body 的拒绝分别检查。无限外围循环只编译和检查，未执行。没有性能测量，也没有将本例算作稳定内存上界、一般数组区间 alias 或论文的全部验收。
