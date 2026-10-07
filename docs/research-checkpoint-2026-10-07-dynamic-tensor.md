# 2026-10-07：narrative 复核与动态布局服务

本轮属于具体 progress；完整 GuardCert 目标继续 active。

重新 fetch 后，`origin/topdown/research-positioning` 为
`271f6fc941910456da43a76e9f0eed38e8a5e200`，main 的
`docs/topdown/paper-narrative.md` 正文与它一致。继续吸收其最小 kernel 截止、
三方责任、四条逻辑链和 OLO proof／functional coverage／usability 的独立验收。
没有仅因澄清而改造核心接口或移动全程序安装责任。

源码复核更正了一项过宽判断：已有二维 runtime-stride compiler 保留变量 stride，
并非所有物理桥都只支持编译期系数。它与小 extent 的 loaded-stride 枚举不同。
当前缺口是通用坐标向量、复杂读写、loaded source／动态布局的组合，而非第一次
支持参数 stride。已有结果不重复算作本轮新成果。

新增 [dynamic tensor 服务](dynamic-tensor-layout.md)：mixed-radix logical cell、
modular pointer registry 的物理 nonalias、实际地址／load／store 对应、依赖指令
交换，以及标准 readonly volume guard certificate。检查先正数、再除法界、再
累计，任意 rank 的检查不依赖 signed64 足够大的假设。最小 kernel、已有
instruction computation／dependence contract 和语言 host 保持。

独立 proof report：
`d5d3622f044b82a842a691ab9234e8d820b79b797fd40b1664051494e5b8c578`。
33 个端点、160 依赖、13 个闭合端点，其余最多六项既有 CompCert 假设。
本轮没有新编译器、extraction、native、成本或作者负担测量；实际调用者 receipt
仍明确列为未完成，不能将有类型的字段当作已经生成。

后续验收顺序固定为：

1. 通用 vector affine coordinates 与 existing instruction reads/value lowering
   消费实际 access proofs，保持原依赖 checker；layout 参数受到 temp frame 保护。
2. Source adapter 识别变量 stride 地址；从真实首次活动路径生产维度定义性，
   并在空路径不提前读取参数。Loaded headers 的许可与保持沿原 prefix 库生产。
3. 实际 condition 接受生产全部活动坐标范围、source/model 对应及候选入口；
   运行时布局留在代码里，不靠小布局枚举或 guard 要求 stride 等于预选常量。
4. Source/candidate 出口、typed private pool、source progress 和 placement 交由
   语言 host 实际消费，接同一 Csem→Asm 链，随后提取和完整 C 运行。
5. 同一候选验证不同合法布局、范围／overflow 拒绝、空轴未初始化参数、RMW
   dependence、header alias、重复 rewrites 和公开 context。Guard work、bytes、
   实际完整成本及作者责任另报；完整 BT 仍需独立输入与功能验收。

这组计划对应 narrative 中困难的 source-definedness／entry derivation 和 host
boundary，不把 condition 数学证明当作完整条件合成，也不声称新的优化已安装。
