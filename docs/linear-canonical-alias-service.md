# Loop-linear alias 条件：适用范围和验证责任

2026-10-08，基于 main b18884f。再次 fetch 并核对远端 heads，
topdown/research-positioning 仍为 12419c1，指定 narrative 与 main 一致。
此阶段用实际服务扩展检验 narrative 的分工，保持 kernel 和 language
host；完整目标仍未完成。

## 变化和使用方式

原 canonical 服务要求所有访问模板的完整 affine map 相等。已经运行的
源片段包含 B[i,j+1]，因此原服务使用 point-pair scan：

    int i=start,j=77;
    #pragma scop
    for(;i<*h+0;i++)
      for(j=0;j<*k+0;j++){
        a[i*16+j]=b[i*16+(j+1)]+alpha;
        b[i*16+j]=a[i*16+j]+alpha;
      }
    #pragma endscop

新服务只要求各模板的循环变量系数相同，允许常数及稳定参数系数不同。
例如 a(i)=M*i+u_a(v)、b(j)=M*j+u_b(v)，两地址坐标之差为
M*(i-j)+u_a(v)-u_b(v)。固定参数下，同一 i-j 对应同一坐标差；
offset 差仍在，不能从实际地址检查中删除。

canonical_loop_linear_map 截取循环系数并将其余项置零，**只用于静态
eligibility 判断**。实际 scanner 使用原完整模板，在原 source 许可的
canonical points 上计算真实 CompCert 地址；运行时没有删掉 j+1 或
参数项。不同循环系数，例如 B[i,2*j]，仍使用旧扫描。

源码用户使用提取 compiler 的默认 linear 策略，也可设置
GUARDCERT_ALIAS_SCAN=linear。其余三个已证明策略为 dedup、canonical、
pair。用户只给标注 C 与选项；marker 请求尝试优化，静态拒绝保留 source，
运行时条件拒绝进入原有 fallback。调度／分块与 prepared codegen 仍由真实
流水线生产普通候选数据，再由既有 checker 验证。

## 谁提供什么证明

| 层 | 本次接口和证明 | 沿用的工作 |
| --- | --- | --- |
| Domain：C_derive | GuardMemoryLinearCanonicalAlias.v 证明 loop-coefficient checker、混合模板差值、tensor index／modular pointer comparison、canonical 与原 pair Boolean 精确对应，以及接受推出原 footprint nonalias | 原 canonical difference coverage、source receipts、原 footprint separation |
| Clight：C_guard | ClightCanonicalSourceInputs.v 从实际 source 完成执行、setup、cap 范围和 ports agreement，生产实际安全 scan、公开／ports frame、dimension observation、ranges、source model 和精确 canonical Boolean | 原 checked allocator、machine scanner、source/model decode |
| 服务客户端 | ClightLinearCanonicalScanService.v 连接新域条件与公共执行适配器，生产原 source_licensed_scan 的 accepted entry fact | 原 fallback、template membership 去重、candidate resource pool |
| Factory／language installation | ClightSelectedLinearScanCompiler.v 的 Csem→Asm 专门端点一行实例化原 theorem | Common factory、loaded guarantee、site/progress/continuation/backend |
| Kernel | 无修改 | 局部证书组合及有限 rewrite 组合 |

公共执行适配器不要求模板 eligibility，不决定检查结果是否足够推出
nonalias。不同域客户端可消费精确 Boolean 和模型证据，再提供自己的
充分性证明；这仍是 Clight／tensor 族的库，不是任意 proposition 的通用
condition compiler。

适配器消费 source 的有限、静默、normal 完成执行，不自动生产 source
progress、合法 placement 或 contextual closure。Private flag/cursors
可改变，memory 与公开状态保持；不能称为完整状态不变的 readonly_condition。
Generic context records 中的 lifting 字段仍由 language host 提供。

四模块分别为 220、166、114、21 行，共 521 行，包括 imports、comments、
audit queries。新客户端复用公共执行适配器和 higher-level proofs；这些
行数不代表作者时间，也不证明另一个 host 或 clause algebra 的复用。

## 已完成的验证

Rocq 16 个新端点，9 closed，最多 42 个继承 globals，1,420 个可达绑定；
父阶段 1,414 个绑定按 hash 检查，无新增公理。不重建冻结对象，不重跑旧
transitive audits。新 compiler 已提取并连接实际 selected C→Asm 路径。

| 实际 C 验收 | Asm calls | 独立 Clight calls | scanner 与结果 |
| --- | ---: | ---: | --- |
| 原正常矩阵 | 1,000 | 1,000 | 原 row／column／parameter stride、unit／nonunit、schedule、拒绝及 context |
| 移位访问 | 180 | 180 | marked tile／schedule 安装实际 canonical difference scanner |
| 不同循环系数 | 180 | 180 | marked tile／schedule 安装旧 pair scanner |

完整 arena、public/first iterator exits、重复 regions、continuation 和路径
匹配独立 modular-word source model。两额外矩阵的 tile／schedule paths
均为 [28,8,16,25,4]；unmarked／disabled 为 [0,0,0,53,0]。
实际 Clight dumps 检查 difference-bound 初始化的存在／缺席，确保执行了
所述算法。稳定参数系数的扩展有域定理和 closed computation，本次没有
对应新 native 参数案例。

移位成本准备另验证 81 个 repeated Asm 完整输出和 27 个独立 Clight 诊断。
原 dedup 策略在此源上退到四模板 pair scan，新 linear 使用三模板
canonical scan；比较同时包含适用范围扩展和现有去重，不隔离两者的成本。
Setup 与 dispatch paths 相同。

| 移位输入／尺寸 | 原 dedup | 新 linear |
| --- | ---: | ---: |
| 2×3 guard if evaluations | 722 | 258 |
| 8×8 guard if evaluations | 71,236 | 3,168 |
| linked kernel bytes | 1,451 | 1,527 |

诊断是 Clight if evaluations，不是 CPU instructions。新代码更大。
新的完整调用测量包含 810 batches、30 随机配对 rounds、每模式独立
calibration，fresh processes、CPU 0 affinity、C clock() process CPU time。
最短观测 0.093898 秒；warmup／final 的全部输出校验通过，没有丢弃样本。
平台为 Ryzen 7800X3D／WSL2，计入 reset、完整 guards、candidate／fallback
和 public restore；初始化／打印／校验不计时，没有 core isolation 或置信区间。

| 输入 | 原 dedup／source | 新 linear／source | 新 linear／原 dedup |
| --- | ---: | ---: | ---: |
| 2×3 accepted | 12.259589 | 7.518873 | 0.615694 |
| 8×8 accepted | 201.004219 | 17.008665 | 0.085070 |
| RHS word wrap | 12.906891 | 8.100286 | 0.628155 |
| Array alias refusal | 10.997411 | 6.311080 | 0.575533 |
| Start refusal | 1.031410 | 1.031477 | 1.003531 |
| Header alias refusal | 1.150137 | 1.136866 | 0.994143 |
| Cap refusal | 1.589422 | 1.677455 | 1.058807 |
| Outer empty | 1.278828 | 1.259495 | 0.986631 |
| Child empty | 1.484572 | 1.615902 | 1.085107 |

2×3／8×8 accepted 相对原服务减少 38.43%／91.49%，仍为 source 的
7.52／17.01 倍；全部九个 median 高于 source。保留 cap／child-empty
回归 5.88%／8.51%，start refusal 增加约 0.35%。这些是描述性 paired
medians，不是显著性结论，未实现接受路径盈利。不能将完整调用时间归因到
单个组件，也不能用这组默认 cap 的热输入代表大工作负载收益。

## 保持的差距和下一项

源族仍是当前两个 loaded bounds 的矩形两-store 族；新 eligibility
不扩展源提取 grammar。一般参数化／非矩形 affine source、更多 scalar／
chunk、OLO 实际源对照和更大 locality workloads 仍需实现和验证。
GUARDCERT_TENSOR_CAP 已可配置，8 是本次测试 profile，不是框架的
固定上限。跨 host contract clauses 和作者时间测量尚未交付。

后续条件服务继续分开验收安全求值、充分性、实际入口出口运输、工厂安装、
接受域、代码尺寸和完整调用成本。新客户端满足 service 后复用 candidate／
host proofs；具体 blocked case 暴露新的边界需求时再修改语言接口。

## 冻结报告与复核

| Artifact | SHA-256 |
| --- | --- |
| proof report | 8d4a309bf326bd715ce0e9bcec7e69d8118d26bf35866d3c2038322070d3754d |
| native report | 705bcd79f4dcfe7e09b75f6d66864c404f3544167f61c60b2b6498d1919f307f |
| shifted report | 2f81e90a409d4e7fecebc36f154f231733c9ef73c6757539dc015b210362cbd5 |
| fallback report | 900bbe01c45745e447965a44ff8bba63358474a5ae09ac2c9776763e3c41b81d |
| prepared report | 4e3ec86c68513fb34093eb9d50133494d29a9391973f63c2eae832baab0054ad |
| timing report | ed4e12ab4c1b12e0b2b633a94e6802ef60ae485a2e5ce2b4ebd347602ccbd3e2 |
| plot report | 5571e66c262637dc1ec2384897d59d173050a2cf562525acea19b5588c0a0a06 |
| compiler | 118fc7ce964350d63e7def83a0930a370ee7f6a58fff8d4b8b3d61adf743f490 |

复核命令使用既有 checkpoints，不覆盖成功的对象或报告：

    opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_linear_canonical_scan.py --validate
    python3 scripts/native_linear_canonical_scan.py --validate
    python3 scripts/native_linear_canonical_scan_shifted.py --validate
    python3 scripts/native_linear_canonical_scan_fallback.py --validate
    python3 scripts/prepare_linear_canonical_cost.py --validate
    python3 scripts/measure_linear_canonical_cost.py --validate
    python3 scripts/plot_linear_canonical_cost.py --validate
