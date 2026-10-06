# 无公开 bound 快照的 affine 源：安全 private capture 与完整编译

本阶段基于 `5d7435b`，关闭[顺序 plan 阶段](research-checkpoint-2026-10-06-affine-planned-loaded.md)的单个 private bound snapshot 缺口。原 C 源不必预先保存 `*bound`；编译器在实际首次 header 的位置插入 fresh private 读取，复用原动态分离 guard 与 mapped／schedule／tiling checker，仍以原片段安装。两类实际 affine 源完成提取和运行验收，完整研究 goal 保持 active。

再次 fetch 后，topdown 仍为 `7d94d810685a691efbf07df734f5fad8abfb4724`，paper narrative 本地与远端正文字节一致。另两个评审分支仍为 `9673381676e18ed0afbc6114e0a62bea9c48002c`、`3e9f0080def8c029cceedbd35184b4de7b8b96bc`，没有新增意见。最小 kernel 的截止保持：局部 guarded correctness 是核心；safe preparation／condition processing 是上层库；scope、进展、片段安装与 backend 属于语言 host。

## 一个使用者例子

[三角源](../examples/native_affine_private_loaded.c)和[第二个 affine 源](../examples/native_affine_private_ragged.c)都保留 body pointers 的实际读取许可，但没有 bound snapshot：

```c
int i=start, j=77, k=91, rp, rq, snapshot=123;
rq=*q; rp=*p;
for (; i<*bound; ++i) {
  k=2*i+1;                    /* 三角版本为 i+1 */
  for (j=0; j<k; ++j)
    p[32+64*i+j]=q[4096+64*i+j]+a;
}
/* 公开 i/j/k/rp/rq/snapshot；保留 suffix stores 与 caller context。 */
```

`snapshot=123` 是公开 marker，不能拿它充当 bound 缓存。旧 planned-loaded 入口要求已有实际 bound load receipt，因此对同一源不安装；新入口保留这些公开行为并分配自己的 cache。概念流程是：

```text
原 source：prefix ; loaded_loop ; suffix
     |
     | 语言证明：实际首次 header 提供合法 Mint32 读取
     v
prepared source：prefix ; private_cache = *bound ; loaded_loop ; suffix
     |
     | 委托既有 source matcher、动态 guard、candidate checker
     v
target：保留 prefix 和 private capture；检查后选择 candidate／loaded fallback
     |
     | 语言桥：prepared 的 [cache]++live 契约投影到原 live
     v
以真正原 source 为 key，交给原语言 host 安装并连接 CompCert backend
```

用户继续提供源选择／候选提案和 profile；这些提案不受信任。原 matcher 和 candidate checker 仍验证实际源模型、仿射域、访问表示和依赖。新增入口只负责准备这一私有观察并复用既有证书链，没有通用假设提取器。

## 新接口与证明责任

| 责任 | 实际接口与保证 |
| --- | --- |
| 最小 semantic kernel | 未修改；原局部条件性候选证书与 guarded correctness 继续使用 |
| 语言 preparation 库 | [ClightLoadedSnapshotInsertion](../prototype/interface/ClightLoadedSnapshotInsertion.v) 提供 `private_source_preparation_contract`：原 source 的实际执行经安全准备成为 prepared source；消费后者的扩展 scope 契约，取得原 public scope 契约。输入仅在公开 temps 上一致，私有初值可以不同 |
| 此种读取的语言实例 | `loaded_header_snapshot_read` 从原 loaded loop 首次真实 header 取得 signed、nonvolatile、`Mint32` load；`loaded_snapshot_insertion_execution` 在 retained prefix 后插入读取，保持 exact memory、E0、正常出口和所有所选公开 temps |
| 源定位／资源证据 | [ClightPrivateLoadedSource](../prototype/interface/ClightPrivateLoadedSource.v) 定位实际 header、验证 structured frameability 和 canonical flattening；`snapshot_site_prepared_contract` 把中间源的契约运输回原 source。fresh cache 不得出现在原片段 temps 或 live 中 |
| Optimizer／domain 接入 | [ClightAffinePrivateLoadedCandidates](../prototype/interface/ClightAffinePrivateLoadedCandidates.v) reserve 一个 cache，将 prepared source 交给原 `check_affine_planned_loaded_source`。条件安全、全部写 coverage、接受后 bound 稳定性、候选／机器 lowering 证明全部委托旧 factory |
| 语言 host 与 backend | [ClightGuardedAffinePrivateLoadedCompiler](../prototype/interface/ClightGuardedAffinePrivateLoadedCompiler.v) 只把真正 `(source,target)` 加入 rewrite table，复用原 scope/private-pool/loaded progress/sequence 安装及 Csem→Asm。host 的进展要求作用于原 source，没有新增“prepared source 必须另行有 progress”的义务 |

准备桥先将原 source 的执行运输到实际 caller entry，只要求 public agreement；随后在这个入口构造 prepared execution，再以自反的扩展 agreement 调用 consumer。这样不会隐含要求 caller 的 private cache 预先定义或与证明中的入口一致。输出再收回原 live，cache 不泄露为公开前置或后置条件。

安全证据来自第一次真正的 header；零次 body 也会求值这个 header，因此同样可读取。它没有假设后续 bound 保持。接受后 bound 稳定性仍由原 source-order guard 证明，拒绝时继续真实 repeated-load fallback，允许写中 bound 后提前结束。新增读取是 nonvolatile、无事件、memory 不变；它会写 private temp，并非语法上“没有任何写”。readonly 的逻辑条件仍与 private-state 的实现分开。

当前语言运输限定于正常、E0、structured 分支；反射 checker 拒绝 calls、labels、returns、switch。它不是新的一般 divergence／任意控制出口协议。只插入 direct signed bound 的一个读取；body pointers 仍需要源已有的 retained receipts。多个依赖 dereference 和通用安全 preload inference 尚未实现。

私有池现在需 18 个 temps：snapshot、plan result、候选使用的 16 个 counter temps。静态资源／源描述／候选检查失败时不安装，原片段保持。七个 [Rocq fixtures](../prototype/interface/ClightPrivateLoadedExamples.v)核对无快照源选择、旧 selector 拒绝、中间源接受、实际 model cache 以及 iterator／pointer／live 冲突拒绝；它们只证明 AST 接入事实，不能替代真实 C 或执行证明。

## 完整 C 与实际机器路径

两个域分别是 `j<i+1` 和 `j<2*i+1`。每个域六配置：mapped、schedule、2×3 tiling、4×1 tiling、默认 64×64 cap 的 mapped、错误域候选。每配置 37 个输入，合计 444 次新编译器调用；每个域另用旧 planned-loaded 编译器运行相同 37 输入，共 74 次旧入口对照。对照不计入 444。

独立 Python 模型先与 GCC 原程序比较完整 arrays、公开出口和 caller context，再与提取编译器的机器输出比较。输入包括零次／负 bound、非零 start、cap 超出、不同 blocks 的 bound、同 block 不同 offsets、第一／第二行写中 bound、body alias、不同 body base 和只够第一行的短数组。公开 marker 全程为 123；实际 Clight 中出现唯一 fresh numeric private bound load，旧入口没有这一加载或安装。

共 28 个 GDB 探针：每域 13 个新入口路径和一个旧入口原顺序对照。mapped／schedule／4×1 tiling／默认 cap 的接受例实际写入顺序为 `p[32],p[160],p[97]`；源回退为 `p[32],p[97],p[160]`。错误域候选不安装。2×3 tiling 有实际安装和完整输出证据，区分重排的 tiling 探针使用 4×1。

mapped cap=4 探针定位所有实际 bound-comparison sites：三角域十处，第二个域十六处。bound=`p[32]` 时只比较 `[32]`；bound=`p[97]` 时比较 `[32,96,97]` 后停止。第二个域拒绝后的公开出口为 i=2、j=k=3，三角域为 i=j=k=2。短数组只有 33 个写单元，未来行非法；guard 只比较首单元并拒绝，后续地址比较指令未执行。不同 blocks 与同 block 的安全 offset 都实际接受。机器脚本按实际 LEA 目标寄存器匹配 CMP，再核对地址与次序，证据限定于这些 x86-64 构建。

当前 body alias 快捷条件仍保守要求相同 base 加 offset 分离，不同 body base 回退。默认 cap 有真实安装和候选运行，但 guard 仍按 cap 展开：三角函数 12,518 个 if／6,062,796 pretty-print 字节，第二域 12,519 个 if／6,352,734 字节。文本包括缩进，不能当作最终机器大小或运行成本。没有性能收益或总 proof burden 下降结论。

## 审计和复现

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-private-loaded-proof
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-private-loaded-native
python3 scripts/validate_affine_private_loaded.py
python3 scripts/validate_affine_private_loaded.py --ragged
```

native target 包含两个矩阵及 GDB ptrace，需要允许 ptrace 的环境。本次依次完成同一 audit/build/native/validate 步骤，两个 domain 使用同一提取编译器。入口为 `ClightGuardedAffinePrivateLoadedCompiler.compile_guarded_affine_private_loaded`；产物独立放在 `build/affine-private-loaded/compiler`，不覆盖旧编译器。

审计 140 个端点，其中 43 个语言端点；592 项选定依赖、936 份 source 摘要。五个新 `.v` 全部实际编译，整个依赖闭包为增量 freshness／摘要核对，未清理重编。没有新增全局公理；五个 compiler 端点继承原 42 项基线。引用 impure candidate factory 的拒绝 fixtures 按 domain 分类，其已有 VPL 公理不归为新增语言基线。audit 仅核对 proof，提取和原生执行分别有独立报告。

| 产物 | SHA-256 |
| --- | --- |
| `build/affine-private-loaded/proof/report.json` | `3fe08e4c4c8e233ad97f32b6ef2c90c31515d67a016a939c298790ff336464b6` |
| `build/affine-private-loaded/compiler/.guard-build.json` | `9cbee8e8db3a38ac3ef6ec2828bf133e339e1761a0fac310c3326e86729b5bea` |
| compiler binary | `fc7c55a7144f4c50e5f1ac6608c45e9c60089f239fbe9f6330531c8a2c9341c1` |
| triangle `native/report.json` | `3601713aa1c218988d473dc8aed296dedf06b70e71cfec2d833bb153c2e9d43f` |
| second domain `native-ragged/report.json` | `cec26495d2430f97017f230aa35d8ace8c29c76224442a3cf6fc82396c1d98c9` |
| `validation.json` | `468b4a2d2b4d3216edb87271a2238fff82dc9cea815baae07cf1f42a90215919` |
| `validation-ragged.json` | `07ec049e8a6f345d6f51189ead766b6187782f07c587b42a023ee91513e9d933` |

旧 planned-loaded／loaded-pointer／cached-inner-pointer 三套 validator 的摘要绑定重新通过，旧 222／1,650／891 调用矩阵未重跑。这里的旧入口 74 次对照使用的是新的无 bound 快照源，不能与旧矩阵混算。

## 后继验收

单个 direct header snapshot 的安全读取和 public-scope 运输已落实。下一项是多个依赖读取的到达顺序、定义性与 byte footprint 稳定性，例如 `i<**pp`：先取得 pointer cell，再取得 bound cell，保持两个观察并沿实际源前缀证明后续读取安全。不能用 pointer 值相等、地址不等或“多加一次 preload”替代大小不同的内存单元分离；源 fallback 必须保留原复合 header。

现有 preparation bridge 可运输安全 capture，但不自动证明依赖 header 的替换或未来观察稳定。优先检验语言读取 receipt、domain byte-separation 和 prefix 库是否足够；实际缺义务时才考虑 kernel。另继续 guard scan 循环化／符号足迹、一般深层 affine 域和复杂 body、不同 body base 的物理 alias 接受、P4 和已有工作同例作者负担比较。
