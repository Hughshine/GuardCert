# 原 matmul：raw skip-prefix 执行运输

后继已完成实际 raw source 安装与动态路径验收，见[当前结果](original-matmul-raw-installation.md)。下面保留本检查点的历史能力边界。

2026-10-09 后继补上[原 C matcher 诊断](original-matmul-installation.md)中的有限
执行运输。两个模块149行、五个端点／两个 closed、最多六个原 baseline globals，
无新增公理。它证明 raw source 与此前 canonical source 的双向有限执行对应，
也证明保留 raw fallback 的 guarded statement 与旧目标的对应。Raw small-step
progress、selector contract 接线和实际安装仍须交付；没有新 native／成本结果。

[ClightSkipPrefix](../theories/ClightSkipPrefix.v) 是语言服务。其
`skip_prefix_relation actual canonical` 允许在 statement 前插入 `Sskip`，并
支持 sequence、condition 和 loop 的结构组合。执行定理保持相同的 trace、
memory、全部 temporaries 及 normal/break/continue/return 等有限 outcome。
Footprint 定理保持 `statement_temps`，可运输 caller scope。语言实例提供这个
具体语法／执行证明；generic kernel 不知道这些 Clight constructors。

[OriginalMatmulRawEquivalence](../prototype/interface/OriginalMatmulRawEquivalence.v)
对保存的真实 frontend shape 构造上述 relation。它复用旧 source/model、capture、
candidate 和 public-exit 证明的 source 表示，不改变原 IEEE 运算树。
`original_matmul_raw_guarded_execution` 的目标分支保留真正 raw source：

```text
capture;
if flag then candidate; restore
else raw_source
```

这里的运输覆盖有限执行。它不从执行等价推断 raw source 的 rank protocol 或
divergence preservation，也不自动交付 host placement。下一步扩展已有 I64
control protocol，覆盖 header／increment 前的 administrative steps，再把该
source guarantee 接到同一 scoped selected compiler。原 C 上实际 guarded
installation、runtime accept/refuse 与原 benchmark 支持仍是验收项。

[机器摘要](original-matmul-raw-transport.json)绑定274 reachable sources／7,786
files，保留两次成功／五次拒绝证明尝试。三个 execution 端点使用 CompCert
semantics 的六个继承 globals；两个 footprint 端点 closed。两份 source、成功
objects、尝试 snapshots/logs 与假设查询均绑定，旧 compiler/native evidence
保留其零安装结论。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_original_matmul_raw_transport.py --validate
```
