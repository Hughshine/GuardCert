# Narrative 对照：loaded store 序列的责任与验收

2026-10-08 再次 `git fetch origin topdown/research-positioning`，并核对远端全部
branch heads。当前可见 narrative 仍为
`12419c1e1e3da450bf378742a2fb4e204e51e060`，其
`docs/topdown/paper-narrative.md` 与 `context-lifting.md` 均与 main 正文一致；
本次没有观察到较新的澄清提交。下述结论对照的是这份完整正文，不宣称已读
未推送内容。

## 吸纳到实现的约束

- **Kernel 止于局部证书组合。** Readonly 是方便的 frontend；条件处理库和
  source-prefix 不因此成为 kernel 的通用语义知识。
- **逻辑链不等于用户手填的四个 record。** `C_opt`、`C_derive`、`C_guard`
  和 `C_host` 由不同 producer 生成。支持族的使用者应给源码和普通数据；
  新语言／新 domain 实现者仍负责新增证明。
- **局部选择与整程序安装分开。** Language host 的 progress、private state、
  boundary 与 placement 是独立证明。保证/要求分解仍是待现有 hosts 检验的
  设计问题，本阶段不因叙述边界改写 kernel 或另造 contract algebra。
- **最难的位置由真实案例推动。** Loaded 多 store 的检查许可必须来自原源，
  接受后先证明所有相关 header 保持，再许可后继读取。Permission transport
  不给出 RHS 值保持，也不允许用待证明的 cached execution 许可 guard。
- **实际 polyhedral pipeline 与可用条件是验收项。** Temp-bound 多数组族
  已有 marked C、真实 Pluto／prepared codegen 和 native 验收；其已闭合范围
  不自动覆盖 loaded 扩展。后继须走同一路径。紧凑条件与 OLO 比较仍需安全、
  充分性、状态运输及分别测量 code size、runtime work、接受域和完整成本。

## 本阶段与后续顺序

[Store-sequence prefix 服务](word-store-sequence-prefix.md)补一个具体依赖：
任意 assignment list 的后续 store 使用真实中间内存 receipt，静态地址检查
接受蕴含 header 保持，并接一条 loaded source axis 的 prefix advance。实际
AST checker 生产 body 的语言义务；它尚未生产完整 loaded factory、rank-n scan
或 region guarantee。

四模块／44 端点已独立审计：16 闭合、最多 6 项旧 globals、1,100 项实际
可达绑定、无新增公理。实际内存 fixtures 证明入口未定义的 A 经前一 store
定义后可供后续 RHS 读取，以及第二条 store/header 别名使 guard 拒绝。
这些是局部 `exec_stmt` 证明，不是新增 native 或整程序能力。

下一步沿完整 original nested prefix 组合多 header／条件读取，建立全接受的
cached/model 对应及实际 guard exit，再消费既有多数组 candidate、恢复与
selected installation。新的支持族验收必须包括实际 C→Asm 的接受、回退和
context；不将本阶段端点或内存 fixture 当作 compiler 完成。与此同时保留已
闭合 temp-bound slice 的 compact-condition／cost 工作，不把所有 source
扩展列为开始这项研究的前提。

Plan、responsibility 文档和稿件按上述范围同步。Active goal 不因该局部服务
或 narrative 再次对齐而标记完成。
