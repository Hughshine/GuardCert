# 深层仿射源循环原型

这是独立的深层仿射编译器原型。正式 signed 单／多指针矩形路线见
[有符号多指针文档](../../docs/memory-signed-multiple-pointers.md)。本目录已有单指针候选与完整程序定理，
已经提取和运行独立原生编译器，尚未改变正式统一编译器的接受范围。

目标源形状是有限深度的 signed32 规范循环。片段根保留实际入口游标；子循环先求值仿射上界，
再把其游标重置为零。子上界可以读取此前的外层游标和稳定参数，例如：

```c
for (; i < n; ++i) {
  K = i + m;
  for (j = 0; j < K; ++j) {
    L = j + p;
    for (k = 0; k < L; ++k) {
      a[16*i + 4*j + k] = alpha;
    }
  }
}
```

独立检查器检查完整源 AST、所有辅助变量的新鲜性、每层上界的读取依赖，以及稳定参数不被辅助变量修改。
它拒绝尚未引入的内层坐标、错误的上界赋值目标和错误登记的稳定参数。

已编译的端点包括：

| 端点 | 保证 |
| --- | --- |
| `check_affine_nest` | 成功识别对应完整源 AST、形状、新鲜性与允许的依赖 |
| `affine_source_first_header_domain` | 从正常源执行推导逐层头部的整数定义性；仅在前面的源循环活动时要求深层读取 |
| `affine_frontend_trace_decode/encode` | 实际源循环与保留每轮 temporary 状态的执行轨迹双向对应 |
| `affine_frontend_trace_last` | 活动循环最后一轮的实际入口、体执行与退出游标 |
| `affine_source_shadow_exit` | 只重放纯控制代码，就能得到与真实源执行完全相同的 temporary 出口；对任意内存保持不变，包括空子循环 |
| `affine_loop_expression_value` | 外层坐标和稳定参数在实际 Loop 环境中的仿射上界值对应 |
| `checked_affine_bound_exact` | 区间检查接受后，机器上界等于数学上界，且不超过认证 cap |
| `check_affine_leaf` | 独立检查实际叶子 AST、地址与数值表达式、寄存器布局和指针覆盖 |
| `affine_leaf_real_memory_decode` | 已检查的真实叶子执行对应实际内存上的指令序列；叶子不修改 temporary |
| `affine_source_used_leaf_word` | 首条完整源活动路径存在时，从实际源执行推导叶子所用稳定参数的整数定义性 |
| `affine_leaf_sequence_semantics` | 源顺序坐标和稳定参数对应实际 Loop 叶子参数；辅助元数据不进入指令载荷 |
| `affine_checked_nest_source_decode` | 完整源 AST 与真实读写叶子证书，在明确整数域前提下组合出任意深度源执行到 Loop 执行的对应，包括空子循环 |
| `checked_affine_profile_domain` | 检查每层仿射表达式、坐标和参数的区间，推出所有实际活动点满足整数域前提 |
| `affine_first_probe_partial_execution` | 实际私有探测代码只执行首条控制路径，避免读取尚未初始化的深层辅助变量 |
| `affine_source_domain_guard_execution` | 从实际正常源执行推出 guard 安全执行、内存不变、公开寄存器不变；接受结果推出完整整数域 |
| `check_affine_guard_package` | 独立检查完整源形状、真实叶子、区间配置、参数用途和私有名字；成功返回上述证明所需证书 |
| `affine_package_guard_execution` | 已检查的数据包提供可执行 Clight guard 及其证明，调用者只需提供实际正常源执行 |
| `affine_package_source_decode` | guard 接受时，从真实源执行得到真实内存上的深层 Loop IR 执行；整数域和参数定义性均由包与 guard 推出 |
| `affine_single_candidate_local` | 已验证的单指针候选经实际 Clight 后端执行，保持最终内存，并恢复相同公开出口 |
| `affine_guarded_region_sound` | 实际 guard、接受候选和失败回退共同提供完整程序框架需要的 `projected_region_contract` |
| `check_affine_static_package` | 进一步检查指针名字、窗口、源 IR、出口作用域及私有变量的实际分配 |
| `check_affine_region_sound` | 不受信任的源描述和候选提议经实际依赖验证与后端检查后提供区域契约 |
| `compile_affine_regions_correct` | 成功输出汇编的深层编译入口满足 `Csem → Asm` backward simulation |

`AffineNestPackageExamples.v` 中的三层例子执行真实数组写入；VM 检查确认合法包被接受，
公开参数被当作结果 scratch、私有名字冲突和私有变量分配缺失均被拒绝。
包的初版把所有稳定整数参数登记在几何布局中，数值表达式也可以读取这些参数。
每个登记参数必须实际出现在根上界、子上界或叶子表达式中，避免无理由地提前读取参数。
私有变量必须由外围函数分配；包检查名字的新鲜性，不负责修改函数的临时变量声明。

guard 先复制已定义的根头部到私有变量，再逐层探测首条源控制路径；只有这条路径真正到达叶子，
才读取全部登记参数并执行 signed 区间检查。首条完整路径为空时保守回退，即使后面的源行可能活动。
这个策略保证正常源执行下检查代码自身安全，不声称条件最弱。

纯控制重放可能执行与源同样多的控制迭代；当前没有成本改善定理。
另一个末轮计算方案 `affine_exit_statement_execution` 只证明生成代码自身的执行，依赖其明确的定义域；
不能把它当作所有源循环的出口对应。通用出口对应由 `affine_source_shadow_exit` 提供。
初版上界区间策略还保守要求中间运算不溢出，不保证最弱条件或全部合法表达式均被接受。

深层源／IR 对应已经编译通过；它要求 `affine_math_domain`，该前提包含每层数学上界的 signed32 范围和实际活动叶子的地址区间。
当前已有可执行且已证明的检查器保证这个前提。单指针路线还使用已验证的窗口非别名性质，
调用实际多面体依赖验证器，生成并证明实际 Clight 候选，再组合到区域和 Csem→Asm。
编译入口为 `AffineNestWholeCompiler.compile_affine_regions`；调用者传入不受信任的源描述器、
不受信任的候选提议器和私有变量数量。它不要求调用者提供源执行／IR 对应证明或信任候选算法。
`affine_default_source_proposal` 从实际片段提议规范嵌套、稳定整数参数、真实数组操作、保守区间和分配池中的私有名字；
其三层实际源 fixture 已通过检查器 VM 验证。它是可替换的不受信任策略，不限制完整程序定理允许的描述器。
独立原生入口已验证实际非矩形调度的接受、拒绝、回退和完整程序执行，见下文。
多指针深层路线仍未接通。本原型不会改变正式统一编译器的候选入口或接受范围。

先完成既有适配器的 `make guard-memory-proof`，然后在项目 Rocq 环境中运行：

```sh
make affine-nest-prototype-proof
make affine-nest-compiler
make native-affine-nest
```

脚本检查既有证明源码哈希，再编译本目录全部 62 个模块并审计假设。报告为
`build/affine-nest-foundation-prototype-report.json`；独立编译记录为
`build/affine-nest-foundation-prototype-audit.log`。语法、表达式编码和结构 frame 没有全局公理；
源与出口端点精确保持已有源定义域端点的六项 CompCert／标准库假设；已检查区域端点和完整程序端点
分别与正式统一编译器的 14 项和 42 项假设比较。

原生提取使用已编译的 611 个既有证明源码和本目录 62 个模块；构建记录绑定全部 673 个源码哈希、
实际提取入口、原生策略代码和编译器二进制。默认源描述器和候选生成器都不受信任，实际检查器独立验证。
候选包括恒等、带源域筛选的 box 枚举、前两轴交换和所有轴反序；坐标变换描述由已证明的点空间检查消费。
候选中的整数严格不等式用 `x <= upper - 1` 编码，以符合提取器的仿射布尔子集。

`examples/native_affine_nest.c` 包含二层／三层三角域、真实依赖、深层未定义参数和递减上界。
十一种配置各完成 283 次完整汇编调用，共 3,113 次。每次比较整个 16,384 单元缓冲区和五个公开控制变量，
同时对应独立 signed32 模型和 GCC `-fwrapv`。合法交换接受四个独立访问函数，拒绝真实依赖例子；
缺失映射、错误域、错误映射、验证资源耗尽及伪造 oracle 证书均不安装候选。
超出坐标范围的交换按既有已证明语义是恒等操作，测试确认其安全接受。

独立的实际 Clight 分支诊断另有 1,018 次函数调用，观察到 328 次快路和 690 次回退，
包含负根和末轮子循环为空的快路；未定义的深层 bound／leaf 参数在 guard 中执行零次读取。
这项诊断由 GCC 执行插桩后的实际 Clight，不与上述未经插桩的 CompCert 汇编证据混同。
报告分别为 `build/native-affine-nest/report.json` 和 `branch-report.json`。
当前深层原型仍只有单指针路线，尚无深层域分块入口或性能收益测量；纯控制重放的成本限制继续适用。
