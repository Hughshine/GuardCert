# 下一项：实际非矩形 pointer 源域

这是下一阶段的设计与验收，不是已实现能力。当前 [observed pointer compiler](clight-observed-pointer-compiler.md) 的源模型是稳定寄存器 counts 的矩形，另一 [parametric compiler](clight-parametric-preservation.md) 支持 named-array 的 `j<U(i,parameters)`；二者不能合并计作已有非矩形 pointer 支持。共享 fallback 只改变最终控制实现，没有扩大这个域。

## 一个确定的切口

先选两层、register-valued 仿射内层上界、普通 int32 pointer 访问；不同时扩展 loaded bounds 和任意控制出口。以下是拟实现的实际源／候选形状，具体 frontend matcher 仍需绑定 normalized AST：

```c
/* 保留源普通读取，提供 raw-base comparison receipt。 */
rp = p[0]; rq = q[0];
for (i = 0; i < n; ++i) {
    k = i + 1;
    for (j = 0; j < k; ++j)
        p[32 + 64*i + j] = q[4096 + 64*i + j];
}
```

拟提案在 `0<n<=64` 时交换遍历：`0<=j<n`，`j<=i<n`；实际点集是 `0<=i<n && 0<=j<i+1`。候选仍从不受信任 Loop／schedule 取得并重新核对，不由 guard 证明调度矩阵自动正确。最终恢复源公开 i／j／k；例如源最后 k 为 n，这项公开出口不能因候选不计算 k 而消失。n<=0 的源可以保留原空路径，不能只在候选中把 j 重置为零。

一个设计层的实际 alias 反例是：同一 buffer 初始每个单元为其下标，n=3，p 指向第 4500 单元、q 指向第 499 单元。源给 p[65] 写 4660；无条件交换后会写 4723，因为列优先先改写了随后读取的单元。该逐点模型反例已核算；它尚未由新 Clight compiler 编译／验证，不能计入当前原生矩阵。源普通 p[0]／q[0] 读取和这六个迭代点均在 buffer 内，回退的必要性不依赖未定义源行为。

这个例子用于检验实际非矩形域、alias-sensitive body、候选对应与出口。它不是任意维 Presburger 源，也不代表已经取得收益或接受率。

## 三方工作与四张证书

| 方／证书 | 下一阶段实际义务 | 已有可复用部分 |
| --- | --- | --- |
| kernel | 消费证书；不识别三角域／pointer／schedule | conditional preservation、条件组合、有限 rewrite 组合 |
| optimizer/domain：C_opt | 实际 Clight 源在机器范围事实下解码为真实三角 Loop；候选独立 reification 与依赖／域核对；编译候选及公开游标恢复 | 原 mapped／schedule checker、pointer body 操作对应、candidate lowering 和 temp frame |
| optimizer/domain：C_derive | 实际全部源访问包含于静态计算的 affine 包络；接受条件建立旧优化模型需要的范围与物理非 alias；不要求最弱条件 | 盒状 affine envelope 可以保守覆盖三角域，但必须另证实际点包含于盒，以及点 footprint 到真实源的对应 |
| language + domain：C_guard | 实际机器检查安全；整数 range 后才计算需要 no-wrap 的值；源 load receipt 提供比较许可；拒绝策略及空路径有定义 | readonly tree、signed／modular arithmetic 原语、source receipt 与 shared realization；domain 提供该实例 D 和覆盖 |
| language + rule witness：C_host | 真实 prefix＋loop＋suffix 的 scope／进展、公开出口／内存运输，最终 Csem→Asm | sequence contracts／framed progress／private pool；需核对新的 affine-bound源进展，不能假定旧 register rectangle classifier 已支持 |

语言库可以运输 statement 执行，不替优化方证明三角点集或依赖保持。反之，domain 证明了足迹包含，也不能自动获得新的循环头表达式执行和源进展。模型／body 适配器属于 optimizer/domain；可供多种 affine 循环复用的机器表达式、控制和 temp 定律属于语言实例。

## 源码证据指向的第一个语言服务

现有 [ParametricSourceClight](../adapters/compcert-memory/GuardMemoryParametricSourceClight.v) 的 `memory_parametric_source_decode` 已接受任意 point relation，并证明真实两层循环与公开 settle；不应为 pointer body 重写整个循环控制证明。但其 DECODE 要求对所有 body-entry temps 成立，未把已有 `temp_agree stable base` 交给 point decoder。内层 `frontend_parametric_decode` 当前只保护 `[row]`。这对由 ge／locals 注册的 named arrays 足够，对依赖 entry pointer／parameter bindings 的 body 则不足。

下一步是一个 framed 的语言服务：把 inner protected temps 扩为 row 与 stable，向 point decoder 显式提供 `temp_agree stable base current`；外层沿既有 writes/frame／settle 运输。point relation 仍由使用者提交，语言服务不解释地址和 alias。随后 optimizer/domain 的 pointer body 消费已有 [multi-pointer sequence inverse／point correspondence](../adapters/compcert-memory/GuardMemoryMultiPointerSequence.v)，在坐标和参数范围、实际 binding 下解码；源 footprint capability 再从真实 Loop trace 导出。

已有 [instruction candidate checker](../adapters/compcert-memory/GuardMemoryParametricInstructionChecker.v) 使用 `memory_parametric_sequence` 的真正非矩形源，不必另造调度验证器；但它当前以 rectangle_shape／width-model 参数组织假设，pointer 接入仍需核对 context／index representation、source／candidate lowering 与范围证书。上述路径是源码支持的复用计划。framed variant 的临时 Rocq 草案已验证 row／source transport，并且假设名不超出既有语言基线；它尚未成为公开模块或被 pointer model／compiler 消费，不计入本阶段 proof audit、提取或运行能力。pointer 模型、真实源定位、条件与候选闭合仍未实现，不能因找到或试证一个可复用 theorem 就计作这些证明已关闭。

## 不能把包络当成安全扫描域

允许用矩形包络保守推导一个充分条件：所有三角点都在盒中，所以盒上的地址范围分离蕴含实际源访问分离。这个推导只操作已经有定义的参数／地址观察，不必读取盒中所有单元。

但不能把原 scan 改成枚举这个矩形：盒里存在源不访问的点，真实源执行不提供它们的读／写权限，源 footprint 的 capability 定理也不覆盖它们。当前 [runtime domain](../adapters/compcert-memory/GuardMemoryParamPointerProjectedCandidate.v) 把 capable 绑定实际 `memory_loop_trace`，当前 [footprint theorem](../adapters/compcert-memory/GuardMemoryParamPointerFootprint.v) 则明确依赖 `memory_rectangular_points`。两处都要由真实非矩形模型替换或推广。

第一版可以在符号条件不接受时直接回原源；这一保守拒绝仍须有非空接受域和实际变换。若随后保留扫描作为较强的第二次机会，扫描必须枚举真实非矩形域，并证明访问安全、检查终止、所有完成执行的接受 sound 和 private cursor／result 的入口运输。这是独立验收，不能因已有矩形 scan 就宣称完成。

不同 base 的物理分离继续需要更强条件或实际点扫描；`p!=q` 不蕴含 byte footprint 分离。raw p 的比较许可也不从 `p+offset` 有效推出，仍消费保留的源读取证据。

## 完成标准与后继难点

交付标准是实际完整 C，真实不同迭代域的候选，公开出口／完整 buffer／外围 effect 对照，非空接受与真实 alias 回退，原 candidate checker 拒绝不合法域／映射，以及实际 Csem→Asm、提取和 linked-machine 顺序探针。source、condition、candidate、checker 和报告分别绑定；单个一般化 lemma 或二维数学模型不计完成。

然后才接 loaded／依赖参数：后项读取可能只有在源活动及前项 non-alias 成功后安全，缓存候选必须同时证明参数稳定；不能在 guard 开始就读取所有 bounds，或将稳定性放进 D。`B⇒全部局部A`、真实模型／候选对应和 guard 自身安全仍是主要难点。是否能由同一库处理多种域、是否降低作者证明负担，分别记录义务复用和新增专属证明，再与已有工作做同例比较。
