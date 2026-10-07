# 2026-10-07：完整原源 header-stability guard checkpoint

前一 goal turn 是实际进展：`18e1b50` 已推送 checked original site 与 entry。
本轮继续同一完整目标，合成真正的 guard；没有缩减为接口或 fixture 完成。
详见 [接口与责任](nested-constant-physical.md)。

## 产出与边界

实际代码执行 row gate、有序 capture、root/child gates、numeric probe、两个
helper assignments，以及完整 outer/child/component physical scan。`SitePrepare`
生产新的实际入口；`ScanNames`／`ScanStatic` 从 site 生产全部 static inputs；
`OuterConsumer` 完整实例化既有原源服务，没有新的 HEADER、effect、DOMAIN、
SOURCE_WORDS 或 source/model 语义回调。Kernel 不变，现有语言服务被实例消费。

`ncs_original_physical_guard_execution` 从实际原源 silent normal completion
给出整个 guard 的 same-memory execution、public frame、defined Boolean，以及
guard exit 上原 source 的 same-final-memory／public-exit execution。
实际接受导出 canonical model execution，并明确 model entry→actual guard exit
的 port frame。`ncs_physical_accepted_source_loop` 再消费 data lowering 的 `Some`
结果，连接真实 Loop source semantics；没有在检查许可时预设 cached completion。

安全 theorem 的域仍是 **silent normal completion**。下一项 candidate adapter
要沿 frame 证明真正使用的 context／pointer cells 对应；candidate dependency/
alias 检查、lowering／public exits、guarded factory、typed private pool 和 host
progress/divergence／placement 仍待完成。该结果不是完整程序上的 nested 优化。

## 验证范围

独立 Rocq closure：39 endpoints（36 domain／3 fixture）、590 dependencies、
1,089 source digests；max 六项既有 CompCert globals，零新增 global axiom。
Kernel 闭合，旧 compiler baseline 保持 42 项。父 site 源／对象保持。

Report SHA-256：
`73482e061adbb772a0faad52840152b4d33f2375000c36ab2d55b4090a289dab`。

新 report、父 site、旧 loaded-offset proof/native/path/guard-work 绑定验证通过。
旧 708 assembly calls／236 Clight calls／21 probes 是已有报告的绑定核对，没有
本轮新跑矩阵。新 fixtures 是完整 source-loop lowering、实际 empty-source full
guard receipt、所有 headers/BODY undefined 时的 nonzero-row 实际 guard refusal。
未新增 active accepting array fixture、compiler、extraction、native、timing 或
empty-build bootstrap。Figure 2 原 C 仍由 unchanged-source coverage 编译，不能
把旧 16-call 报告改成支持优化。

论文同步改为当前功能链及责任／验收边界，历史阶段计数保留在 evidence map，
避免把 proof counts 作为研究效益。Offline Tectonic 最终构建 11 页，无 undefined
reference/citation 或 overfull box；第 6–11 页渲染并查看。最终 paper report SHA：
`0468a1366bdd40c6d800dc60f8ef9b8334f3197107f9d4c3cfef12b146ac56f3`。

完整目标保持 active。Functional compiler 闭合后还须 compact condition、实用
接受域、guard／完整运行成本、编译/code size 和同例作者工作比较；不以本阶段
证明数量或正常完成域的正确性代替这些要求。

已核对下一项可复用的实际消费者：
`ClightLoadedOffsetAffineMultiGuard.offset_affine_multi_guard_execution` 先由
checked source scope 与 controls-writes 沿 ports frame 运输 canonical execution
到 guard exit，再许可旧 `affine_multi_alias_only_execution`。新 nested 实例优先
复用该模式，避免要求对任意 cell 的整个 location map 相等；保持真实 source
execution 和 candidate-used views 的对应。
