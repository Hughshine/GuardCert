# Loaded affine pointer 源：观察与稳定性的证明顺序

2026-10-06，接续 main `3d5af75`。本阶段交付真实 loaded 三角循环的局部 guarded rewrite、保留 source prefix 的 contract，以及观察／稳定性服务。新规则尚未安装进编译器；此前 891 次原生调用属于已安装的 register-bound compiler。完整 goal 保持 active。

## 实际源与目标

normalized Clight 源对应以下代码。n、rp、rq 是源原本就有的公开 preload，优化没有提前插入这些读取：

```c
n = p[0]; rp = p[0]; rq = q[0];
for (; i < p[0]; ++i) {
  k = i + 1;
  for (j = 0; j < k; ++j)
    p[32 + 64*i + j] = q[4096 + 64*i + j] + a;
}
```

源每次 outer test 都实际读取 p[0]。[Example](../prototype/interface/ClightAffineLoadedPointerExample.v) 证明：i=0 且初始缓存值满足 0<n≤64 时，已验证的写足迹排除 p[0]，因此实际源执行可以运输到原 register-bound 三角循环，保持相同 trace、全部 temps 和完整 memory。不能先假设 cached source 已经完成，再用它证明 loaded source 的稳定性。

[Rewrite](../prototype/interface/ClightAffineLoadedPointerRewrite.v) 将这个运输接到同一 checked source package 的候选证书、两套 candidate ranges、实际 lowering 和公开出口恢复。使用者提供 `affine_inner_pointer_candidate_package`，可以来自既有 mapped 或 tiling checker。这里没有重复候选等价证明，也没有证明任意优化提案正确。

实际 target 的 readonly tree 先检查 i=0、0<n≤64，再执行原候选条件；全部接受执行认证候选，任一拒绝执行原 loaded loop。condition certificate 消费 kernel 的 `sequence_readonly_conditions`，语言实例解释为真实 `decision_bind`／Clight if。

## D 与 P 的顺序

1. `source_preload_value` 从实际保留 prefix 取得缓存值、pointer binding 和当前 load 观察。后续 prefix 输出不得覆盖该值或 pointer；receipt 不要求未来 body 的 stores 保持观察。
2. `loaded_bound_completed_header` 从实际源执行取得第一次 loaded test。与 prefix 相等的读取证明缓存 n 的 integer 类型，并取得 i 的控制类型。prefix 同时提供 p/q 的 source capabilities。`alp_source_prefix_domain` 由此产生 D。
3. preliminary check 建立 i=0 与 0<n≤64。`memory_affine_pointer_loaded_first_words` 取得第一次实际活动 source row／inner body，证明 body-only scalar a 有定义；它不要求 write separation 或 load stability。
4. 静态 footprint certificate 与接受的 ranges 建立所有 reached points 的字节分离。实际 pointer body decoder 和 store 定律推出 p[0] 保持，然后运输 loaded source 到 checked cached source。
5. 该运输产生原候选 guard 的 completed-source 域，继续复用其安全、alias、ranges、候选证书和实际 execution。

`alp_completed_domain` 明确要求有限正常源完成。D 没有写入分离或未来 bound 稳定性；本阶段没有将它推广为任意无限源的有限前缀协议。

## 三方验证责任

| 责任 | 新增或复用 | 使用者仍须提供什么 |
| --- | --- | --- |
| framework | 核心未改，复用 readonly condition、域限制、依赖条件顺序组合 | 语言分派／安全定律和各阶段证书 |
| language／Clight | [preload 值观察](../prototype/interface/ClightSourcePreloadObservation.v)、[loaded-row 运输](../prototype/interface/ClightAffineLoadedBoundTransport.v)；复用 active-loop、表达式确定性、byte store/load、temp frame、prefix contract | 具体 row decoder、控制范围和 protected temps；语言服务不识别 schedule／affine footprint |
| optimizer／domain | [write-only 观察保持](../adapters/compcert-memory/GuardMemoryObservationStability.v)、[cell exclusion checker](../adapters/compcert-memory/GuardMemoryObservationExclusion.v)、[实际 pointer body 接口](../adapters/compcert-memory/GuardMemoryAffinePointerLoadedSource.v)及三角使用者 | AST/body 访问对应、所有 reached points 的范围／写分离、同一候选的证书和 lowering equation |
| language host＋规则 witness | 复用 `source_prefix_region_contract` 得到实际 prefix＋loaded loop 的 `projected_region_contract` | 完整安装还须 source progress、matcher、table／private pool 和真实 frontend 对应 |

核心不读取具体 semantics。困难处是两项证据的顺序：真实 source 活动许可 body 参数观察；接受的入口条件覆盖全部实际 writes，才能把反复读取换成 snapshot。`C_derive` 的全称覆盖与 `C_guard` 的定义性不能互相当作前提。

## 表达力与边界

`memory_writes_exclude_cell limits extent buffer observed operations` 核对非负系数 affine 下标的盒状上下界，要求每条 write 使用指定 buffer，并排除指定逻辑单元。支持任意有限操作列表，scalar 可附在坐标后；读足迹不必与观察分离。sound theorem 用 CompCert modular pointer 地址证明实际四字节区间分离，包括地址顺序绕回。

这是编译时 footprint certificate。runtime guard 仍须建立参数范围和观察 pointer 与逻辑单元的关系。本例 bound 是 write buffer 的 p[0]；generic 运输允许另一 pointer，但具体 rule 尚未合成任意 bound pointer 的 guard。证明 p[0] 被排除、p[97] 被拒绝，并提供源点 i=1、j=1、n=3 写到 p[97] 的 witness。不同 write buffer 的提案也被这个保守 checker 拒绝。

该 checker 不处理任意符号系数、一般 polyhedral projection 或任意 alias 布局；后续可复用 signed envelope／physical pair 服务。generic 观察保持定理可消费其他分离证据，不受此 checker 的系数限制。本例利用源已有 public cache，不能代替 private snapshot 引入和多个依赖 preload 的安全读序。

## 验证与后续

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make affine-loaded-pointer-proof
python3 scripts/validate_affine_inner_pointer.py
```

[独立审计](../scripts/audit_affine_loaded_pointer.py) 通过 31 个新增端点，其中 4 个语言端点；540 项实际依赖、884 份 source digests，新增全局公理为 0。cell exclusion 三个 soundness 端点闭合于全局上下文；loaded source、组合 condition 和 prefix contract 使用 6 项继承 CompCert 假设。既有 `compile_affine_inner_pointer_correct` 独立回归仍为原 42 项假设。

局部定理的 6 项假设不意味着候选证书无需验证：定理量化一份已经认证的 package，构造它仍须真实 mapped／tiling checker、源／候选对应与 lowering。本阶段未运行新 loaded rule 的提取或原生代码，也没有新 whole-program 入口。采用增量 selected closure，未 clean rebuild 整个 CompCert。

proof report SHA-256 为 `81a5cd23485299e2f0a5dd46a532c53de98263ab6d06090de3121fe18241e758`。原 compiler 的 source/object／extraction／native 绑定重验通过，继续绑定原 891 调用和七个机器探针；本次未重执行它们。两个报告分开，不把旧原生证据计给新规则。

本次 fetch 确认评审分支未更新：topdown 为 `f7936299fa6272fbf50db6b94a1bd0333808ea09`，evidence 为 `9673381`，performance 为 `3e9f008`。持续按 narrative 的三方责任与困难义务推进。

下一步先关闭不假设 bound 稳定的 loaded nested source progress／placement，再将 prefix contract、原候选工厂和新 matcher 接到完整 Csem→Asm 与提取。随后推广一般 bound pointer 和多个依赖 preload，逐项证明后项读取如何由 source 活动和已接受事实许可。性能与同例作者负担仍须单独测量。
