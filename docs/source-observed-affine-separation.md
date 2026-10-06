# 源观察支持的符号化地址分离

本阶段后继于 `cd8c228` 的宽度 guard。它证明一个受限 alias 快捷检查及其实际 Clight 片段 lowering：源已经读取的普通 pointer base 提供合法观察证据，仿射包络覆盖全部真实循环访问；充分条件接受时直接执行原候选，拒绝时运行原 footprint scan。完整编译器选择器、提取和新路径 native 验收继续待接入，旧 pointer compiler 仍执行原扫描。

## 用户需要提供什么

输入由使用者定位为 `Ssequence (source_load_prefix loads) source`。`loads` 是普通 int32 源读取的 `(目标 temp, pointer temp)` 列表；source 是已有的参数化 pointer region package。前缀保留在原位置，目标不会额外插入读取。框架不自动推断某个任意外围 context 已经赋予了地址有效性。

可以从概念上看下面的例子；本轮尚未验证这段 C 的实际 frontend matcher：

```c
rp = *p;
rq = *q;
for (i = 0; i < n; ++i)
  for (j = 0; j < m; ++j)
    p[32 + 16*i + j + t] = q[128 + 16*i + j + t] + 1;
```

优化使用者仍提供 affine／tiling 候选及原依赖 checker 的证书。语言定位证据说明前缀输出不覆盖所观察的 pointer，且每个被快捷检查使用的 pointer 都在源读取中。`source_observations_check` 实际核对这两个有限语法条件，拒绝未覆盖的 pointer 和破坏 pointer binding 的 prefix。

接口 [check_observed_param_pointer_candidate](../prototype/interface/ClightObservedPointerCandidate.v) 输入 live temps、private pool、已核对源 package、loads、候选 Loop 和已有 candidate check。它调用原 checked lowering；从成功 lowering 的 witness 取得绑定实际 AST 的候选局部证明；构造前缀、符号检查、原候选及原扫描回退。其 sound 定理要求调用者证明所提交的 candidate check 接受蕴含原有 `memory_bounded_candidate_certificate`，如同原路径。它不把任意 bool check 当作 verified checker。

一般使用者可直接提交 [private_scan_preserving_rule](../prototype/interface/ClightPrivateScanPreservation.v)。[observed_param_pointer_region_contract](../prototype/interface/ClightObservedPointerPreservation.v) 要求 rule 的 D/P 与实际 package 一致，以及上述 prefix coverage/freshness；从真实 prefix 和 source 执行导出入口观察。该 contract 可以由现有 private-region table host 消费。实际 normalized AST 的匹配、candidate proposal dispatch 和 compiler 注册仍是下一项交付。

## 条件如何得到全部访问的保证

把一个访问写为 `a·coordinates + b·parameters + bias`。对每一 coordinate，按系数符号选择 0 或 count−1，得到在入口 counts／parameters 上计算的上下界。这一步复用无语言依赖的 [AffineBoxEnvelope](../prototype/interface/AffineBoxEnvelope.v)，覆盖任意有限维盒内所有点。

对于不同逻辑 array 的每对访问，快捷条件要求实际 bases 相等，以及 `upper(first)<lower(second)` 或反向分离。所有访问对必须通过。它对 `p!=q` 的情况保守返回 false，随后原扫描仍可能接受候选。它也不把 offset 区间重叠解释成所有实际访问必然 alias。

上例生成：

```text
p offsets: [32+t, 32+16(n-1)+(m-1)+t]
q offsets: [128+t, 128+16(n-1)+(m-1)+t]
```

`n=m=2,t=0` 时两个区间为 [32,49] 和 [128,145]，同 base 路径接受。`n=m=7,t=0` 时区间重叠，快捷检查拒绝。这两个算术结果、相应非空机器编码及实际 guard 的精确 Boolean 解释均有 Rocq 证明。这里没有新增 native 时间或执行路径样本。

生成的实际 Clight 条件先核对原 header，再比较 bases／包络。机器表达式使用 modular int32 求值，静态 checker 证明最终比较值在 signed range 内；intermediate add/mul 可以 wrap。本实例沿用原 pointer package 的非负参数与受限索引模型，尚未扩展其 source selector 至任意 signed affine 或一般 polyhedron。

旧 source footprint 定理把每个真实 cell 还原为一个受支持访问和 coordinate。访问对包络证明因此覆盖全部 footprint。物理单元桥接使用同 base 下的 modular pointer offset：在原 window 的 `4*extent≤Ptrofs.modulus` 条件下，不同合法整数索引对应不同四字节单元，包含地址回绕。它没有使用跨 block 的 pointer ordering、pointer-to-integer cast 或 ghost allocation 查询。

## 三方责任与证书复用

| 责任 | 本阶段新增／复用 |
| --- | --- |
| 语言无关框架 | kernel 未修改；readonly shortcut 和原 stateful scan 均消费 `guardify_preservation`。C_opt 保持同一个实际 candidate，false 路径保持原扫描 |
| Clight 语言库 | [SourceObservation](../prototype/interface/ClightSourceObservation.v) 从真实普通源读取导出 valid-pointer receipt，证明保护 frame 与 prefix 后的 region 安装；[PrivateScanShortcut](../prototype/interface/ClightPrivateScanShortcut.v) 复用候选局部证明与原扫描；[AffinePointerEnvelope](../prototype/interface/ClightAffinePointerEnvelope.v) 证明实际 Boolean 与 modular 物理分离原语 |
| 优化／domain 库 | [ParamPointerEnvelope](../prototype/interface/ClightParamPointerEnvelope.v) 生成访问对条件，证明 header 表示、全源 footprint coverage 和 `accepts⇒P`；[ObservedPointerCandidate](../prototype/interface/ClightObservedPointerCandidate.v) 从原 checked lowering 取得实际 witness，绑定新片段 AST。原模型／依赖 checker 继续负责 C_opt |

最难的两项在此明确相接：**观察许可**来自保留的 source prefix；**B 覆盖所有局部 A**来自实际 footprint membership 与生成包络。D 没有预先假设 no-alias，也没有给普通循环偷偷加上 raw-base valid。某个新源没有可核对的 prefix 时，当前服务不会替它产生这份 placement 证据。

`C_host` 仍使用有限、silent、正常完成的 region contract，并量化实际 Clight program 的 globalenv、public temps 与 continuation；它不是任意无限 prefix／pointer source 的协议。检查前缀的源写入与循环写入按 frame 分开运输；快捷检查本身不写 temps 或 memory，原 scan 的 result／cursor 写入继续由原 host 处理。candidate lowering 对 private counters 的初值没有要求，因此快捷接受不需要先运行扫描初始化。

## 验证与下一项

运行 `opam exec --root=/tmp/guard-opam --switch=guard -- make interface-pointer-envelope-proof`。专用审计绑定实际依赖 closure、源码与 .vo 摘要、CompCert 假设和每个公开端点。报告位于 `build/interface-pointer-envelope/report.json`，明确记录新 compiler entrypoint／提取／native／performance 尚未完成。它不替代前一阶段的 compiler/native 报告。

下一项将此 checked fragment lowering 接到真实 normalized source 的 prefix matcher、mapped／tiling／schedule proposal 路线和 Csem→Asm compiler。随后验收同 base 分离的实际快捷接受、重叠／不同 base 的扫描路径、静态 observations 拒绝、保留的 prefix 值及完整上下文；用实际二进制确认快捷接受未执行足迹扫描。一般 affine pointer 域、多依赖 preload、同版 CompCert 对照和作者负担比较继续留在完整目标中。
