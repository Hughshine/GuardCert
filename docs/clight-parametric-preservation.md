# 参数化仿射源如何使用公共接口

本文面向实现一个 guarded loop pass 的使用者。当前可运行入口是 [compile_preserving_parametric](../prototype/interface/ClightParametricCompiler.v)。它处理外层 `i < n`、内层 `j < U(i,parameters)` 的源循环，其中 U 是已支持的有符号仿射表达。源 body 可以使用已有 named、不同布局、仿射偏移及多读取／计算模型。一般嵌套 polyhedron、指针切片和循环式运行时检查仍有独立工作。

## 一次实际替换

[原有 C fixture](../examples/native_memory_parametric.c) 中有这样的循环：

```c
for (; i < n; ++i) {
  k = 2*i + m - p;
  for (j = 0; j < k; ++j)
    a[i*20+j] = i*37+j+7;
}
```

使用者提出 interchange。外部文件可以写：

```text
(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))
```

候选生产器收到核对过的 body instructions、坐标数量和参数 context 长度。这些数据用于构造调度，未携带候选正确性。编译器从实际源 package 构造带参数域的 Loop，运行已有调度生成器，再对生成的实际 Loop 核对 mapped-domain 与依赖。参数数量变化时 `coordinate` 会按实际 context 实例化，避免把固定系数长度当成语言接口。

通过核对后才生成实际候选 Clight，附上 i/j/k 的公开出口恢复。相同的源、候选和条件可选择 direct 或 shared realization；shared 只写私有 Boolean，保持公开状态与 memory。实际替换 table 经过已验证的作用域、进展和上下文安装，再进入 CompCert 后端。`compile_preserving_parametric_correct` 对任意 proposer、lowering 和资源预算给出完整 Csem→Asm backward simulation。

## 三方分别交付什么

| 责任方 | 当前实际交付 | 新规则使用者需要补的内容 |
| --- | --- | --- |
| 语言无关框架 | 消费条件／局部保持证书；组合只读条件；在语言定律下提升并组合 rewrite | 不承担源识别或调度搜索；不从任意 S/T 自动发现假设 |
| Clight 语言库 | 原子观察与安全 lowering、真实分派与私有 temp 运输、公开出口／frame、host 和后端连接；新的 `choose_preserving_dispatch_sound` 共用既有 normal realization | 若 guard 是循环扫描，需要另提供真实检查后状态关系；单 Boolean 入口函数还不够 |
| 优化／domain 库 | 核对源语法和 body 对应、仿射参数编码、端点覆盖、实际候选与依赖核对、参数范围选择 | 新 source/body 的模型对应、有效观察从何取得、入口条件为何覆盖所有实例；不能只提交一个未经证明的 oracle 答案 |

局部证书沿用 source-to-candidate 保持，量化实际 program 的 globalenv。新 [使用者](../prototype/interface/ClightParametricPreservation.v) 通过 `encoded_private_as_preserving` 消费 `memory_parametric_body_candidate_rule`，再调用公共分派／安装。它没有要求旧 checker 提供任意 globalenv 上的反方向等价。

## 最难的一步：入口 B 覆盖所有迭代的 A

对上面的 U，新 [符号包络算法](affine-box-condition-derivation.md) 根据行系数符号，生成 `lower=m-p`、`upper=2*(n-1)+m-p`，实际检查首行非空、`lower>=0`、`upper<=stride`。`compile_parametric_envelope_width_correct` 将盒内全点覆盖接到实际源，推出每个 `0 ≤ i < n` 的宽度界，不在运行时枚举 i。首行非空用于从实际源执行取得数组观察的安全性。不能取得这项证据的入口走源回退。

包络覆盖是 `C_derive` 的一部分。Clight 编码另外证明 modular 仿射求值及最终 signed 比较范围，支持负参数与负系数，这属于 `C_guard`，不能由整数不等式代替。新条件接受推出旧条件接受，保留候选和局部证书；实际程序不再执行旧宽度树。静态编码拒绝时保留旧树，旧 `lower_test` 成功仍是 selector 与旧局部证书的条件。检查次序为源 header、参数范围、新宽度、真实数组基址；后续观察只在已有结果允许时执行。D 从正常源执行获得，未预放 no-alias 或参数范围结论。

当前选择器先尝试默认范围，再尝试外层上界 8/4/3/2/1；还复用已有 width=1 的受限源证书作为候补。这是有限的保守 profile 搜索，并非最弱条件或完整 QE。每个实际返回的候选都有独立证书；profile 搜索只组合成功结果。源运行超出所选范围时保留原循环。

地址与控制的数学对应需要范围证据。数据计算则保留 CompCert 的实际 word 运算，包含回绕；不能把所有数据操作都描述成 no-overflow 优化。多读取、布局和偏移的 body 模型另证明物理执行与 memory instructions 一致，依赖核对不能只依赖逻辑数组名字。

## 运行与边界

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-parametric-native
```

工具链沿用 Rocq/Stdlib 9.2 和 CompCert v3.18。`GUARDCERT_LOOP_CANDIDATE` 指定不受信任候选文件；`GUARDCERT_GUARD_LOWERING=direct|shared` 指定实际 guard 实现，默认 shared。编译器位于 `build/compcert-readonly-parametric/ccomp`。

原生测试复用六份 C 程序和各自独立模型，检查实际候选选择、公开出口、完整数组结果与 GCC。参数数量、重复／零倍参数、同一函数中的连续替换、空外层、非零起点、范围回退、不同 layout、偏移、多个读取与机器数据回绕均有覆盖。GCC 对照使用 `-fwrapv`，以匹配这些数据 fixture 的 word 语义。迁移时的历史证据见 [原阶段记录](research-checkpoint-2026-10-06-parametric.md)，条件推导的当前证据另记在 [符号包络阶段](research-checkpoint-2026-10-06-envelope.md)。

134 个 direct/shared 编译配置已经通过。候选的接受集合取决于具体调度：例如 offset fixture 中 `offset_anchor_chain` 与 `offset_global_chain` 的 fission 被依赖核对器拒绝，其他候选仍可接受这些源。测试采用原有独立回归的拒绝策略，不将成功识别 source 等同于任意 schedule 均有效。

可选 `make interface-parametric-runtime-order` 在 x86-64/GDB 中观察两个实际数组写入，不修改源或汇编。同一 `affine_growing` interchange 二进制在 `(i,n,m,p)=(0,2,2,0)` 下先写 `a[20]` 再写 `a[1]`；非零起点 `(2,4,5,1)` 下回退，先写 `a[41]` 再写 `a[60]`。新探针另外覆盖首行空回退、负行系数／负参数接受及末行负宽度回退，两种 lowering 共十个探针。二进制／汇编摘要绑定完整回归报告；完成状态见当前阶段记录。它们是实际分支的功能见证，没有测量性能。

当前只安装正常有限 region，继续要求独立 source progress。未覆盖任意无限 polyhedral 源回退、shared whole-loop、一般深度源、非仿射访问或动态 pointer footprint。对第一行为空的有定义源会回退；这些限制不能隐藏在 D 中。此次交付证明和运行的是已有仿射领域设施通过公共接口的复用，未声称新增通用入口条件推导算法或证明负担／性能收益。
