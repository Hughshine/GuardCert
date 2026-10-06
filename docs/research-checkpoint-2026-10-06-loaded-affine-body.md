# Deep affine＋loaded bound：完整 body 的前缀服务与缓存运输

2026-10-06。继 [numeric producer](research-checkpoint-2026-10-06-loaded-affine-numeric.md)
之后，本阶段已证明不固定 body 维数的语言服务，并接到已有递归 affine
package。远端 narrative 重新 fetch 后仍为 `7d94d81`，正文与主线一致。
最小 kernel 保持不变，完整目标继续 active。

## 实际得到什么

```text
当前 loaded header 的实际 residual source
  → 当前完整 body 的实际执行 receipt
  → 结构化 stores 的权限运输／checked written temps 的 frame
  → domain body check 接受，证明当前观察保持
  → 下一 loaded header 的实际 residual source

完整 fuel 覆盖＋各 body 的观察保持
  → 原 loaded 源的完整缓存源执行，出口 temps／memory 相同
```

这里的 body 可以包含任意有限深度的结构化循环；接口不要求将其解码成
二维的 `counted_iterations`。它仍限制在已有 `writes_only` 支持的代码、
normal／quiet body 和原源有限正常完成上，不提供含 calls／allocation／free
或任意 divergence 的新安装宿主。

实际写允许改变 bound。权限保持与观察值保持是两个不同结论：前者从
CompCert assignment／store 语义取得；后者必须由 domain 的安全检查取得。
`loaded_body_preserved` 量化当前坐标、保护 temps 和当前观察下的实际 body
执行。框架不会从数值域自动推出它，也不会预置后续观察稳定性。

## 三方接口与责任

| 文件 | 已证明的接口 | 仍由调用者提供的事实 |
| --- | --- | --- |
| [StructuredStorePermissions](../prototype/interface/ClightStructuredStorePermissions.v) | actual assignment 的权限向前态运输；由 `writes_only` 推广到任意受支持结构化执行 | 实际源执行和语法 certificate；不需要数值模型或观察稳定性 |
| [LoadedBodyPrefix](../prototype/interface/ClightLoadedBodyPrefix.v) | initial／body receipt／接受后 advance；消费旧只读 prefix library；显式 fuel coverage 下的完整 stability certificate | normal／quiet、written 集与 protected temps 分离；domain 的 `BODY_CHECK` |
| [LoadedBodyTransport](../prototype/interface/ClightLoadedBodyTransport.v) | actual loaded source→actual cached source，保留全部出口 temps／memory，并返回观察 invariant | 当前 private cache／load 一致；各活动坐标的 body preservation；此输入不是缓存源完成 |
| [LoadedAffineBodyPrefix](../prototype/interface/ClightLoadedAffineBodyPrefix.v) | checked affine package 的 body writes／权限；pointer register freshness checker；numeric snapshot 的 initial prefix；完整缓存 affine 源运输 | 对原源、private capture 和 numeric 接受的已有证据；recursive physical body probe 的证明仍待实现 |
| [Examples](../prototype/interface/ClightLoadedBodyPrefixExamples.v) | 三层 names 接受／拒绝；真实 alias 源、前缀、检查拒绝与 lowering；具体 allocation；三层零次缓存源执行 | 证明 fixtures；不是 compiler／assembly 验收 |

语言层统一证明 frame、权限、loaded header、counter increment 与缓存运输。
优化／domain 实现者仍须提供当前 body 的访问／数学对应、安全检查和接受后
的字节分离，才能构造 `BODY_CHECK`。只读 prefix library 将单次证据组合为
扫描证书；其 `fuel=0` 不构成覆盖证明，完整接口显式要求 count≤fuel。

新 `affine_loaded_body_names_check` 拒绝把 loaded pointer 或 body pointer
放进源的 counter 修改集。这是 register freshness，并不要求不同 memory
blocks，也不宣称已经检查了 memory alias。

## 实际 alias 例子

```c
int n = 2;
int *bound = &n;
for (int i = 0; i < *bound; ++i)
  *bound = i + 1;
```

源执行一次，写 `n=1`，以 `i=1` 正常退出。Fixture 证明了这次实际 Clight
执行、首次 body receipt 和观察不保持。检查用实际 reached store 的 Writable
权限及实际 header read，合法比较写地址与 bound 地址，在首次比较处拒绝。
两步扫描不会因此要求第二次 body 的许可；检查本身不执行源 stores。

Fixture 同时证明 `decision_run ... false` 与实际 Clight lowering 的正常
执行、temps／memory 不变。Lowering 的两个 leaves 都是 `Sskip`，此处只验收
检查执行，不冒充 result dispatch、candidate rewrite 或完整编译器。具体
四字节 CompCert allocation、初始化 2 和实际 store 1 见证 domain 非空。

三层零次 fixture 在 child 参数／body pointer 仍缺失时，从实际 loaded
source 导出缓存 source 执行；它不要求 numeric guard 接受零次域。非空递归
physical guard、成功路径与编译器安装尚未交付。

## 验证范围

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make loaded-affine-body-proof
python3 scripts/validate_affine_nest_materialized.py
```

五个新 `.v` 全部以 Rocq 9.2 编译。独立审计含 34 个端点：12 个语言服务、
6 个 domain bridge、16 个 fixtures；绑定 665 个依赖对象和 992 份源摘要。
新端点最多 6 项原 CompCert 假设，无新增全局公理。Kernel 闭合，两个当前
Csem→Asm 回归维持原 42 项假设；numeric／materialized／current cursor
报告绑定的源码和对象摘要全部不变。历史 native validator 通过，本轮没有
重跑其 5,118 调用，也没有新增提取或 native 测试。

报告 `build/loaded-affine-body/proof/report.json` 的 SHA-256：

```text
58d1aa0971a4521dc7d63edc0b74d69354157d46349cb38fe256ad9c323ed25c
```

## 下一项实质工作

实现 recursive physical **body** probe，而不是另造 kernel。原 root body
的完整 receipt 已许可其内部的全部 recursive points：child bounds 是稳定
temps／包围坐标的 affine 表达式，没有再次读取 loaded root bound。因此可
复用旧 child decode／数学点覆盖／physical capability，检查当前完整 body。
即使本 body 改写 bound，它的已完成执行仍提供本 body 中后续访问的许可。

扫描只在当前 body 检查接受后推进到下一 root header；跨 body 的未来访问
不能由缓存数值域直接许可。这比逐个 store 推进更符合当前 canonical IR，
也避免重新要求优化作者证明语言级 temp frame 和权限运输。之后消费本阶段
缓存源桥，复用旧 deep 多指针跨点依赖与 candidate checker，再接 private
pool、原 source key／fallback、progress／scope、全程序 host 和真实 C 提取。

当前最难的 domain 义务仍是：由 actual body completion 和 numeric 接受
生产全部 point permissions，证明检查代码确实覆盖这些写地址，并将接受
的 byte separation 推成 body preservation。此次接口与反例没有替代该证明。
