# 第二个 loaded header：capture、实际前缀与缓存运输

本步补上第二个 loaded bound 的语言／domain 服务；尚未安装支持它的完整优化器。
[阶段记录](research-checkpoint-2026-10-06-nested-headers.md)列出验证和后继验收。
最小 kernel 未改，现有 loaded＋offset compiler 仍是可运行入口。

## 外层进入后才捕获 child

以原片段为例：

```c
for (row = 0; row < shape[0] + 1; row++) {
  for (column = 0; column < shape[1] + 1; column++) {
    BODY;
  }
}
```

不能无条件预读 `shape[1]`。不进入外层时，原程序可以只有一个 shape word；
内层 counter 和 BODY 的 output pointer 也可以尚未定义。
`nested_expression_capture` 的真实 Clight 代码按以下顺序执行：

```text
cache_R := original_outer_bound;
if (original_row < cache_R)
  cache_C := original_child_bound;
```

`nested_expression_capture_execution` 从原 source completion 取得第一个
comparison；它为真时，从原 outer body 的 counter reset 和 child execution
取得第二个 comparison。这提供 child bound 的实际求值。返回的 source witness
保留原 loaded headers 和最终 memory；captures 只改变 private temps。
没有以未来的读取稳定性许可首次读取。

当前接口要求原 outer body 为 `reset(column); child_loop`，BODY 可以是任意
满足服务定律的 structured statement，包含更深层循环。提前到 guard entry
求值 child bound 要求它不读取自己的 counter：原 reset 只改变该 temp，表达式
运输据此保持求值。将同一个 child cache 用于后续 rows 还必须证明 HEADER
定律；支持表达式求值不等于支持将 row-dependent bound 跨 rows 固定为常数。

`ClightSignedIndexedOffsetHeader` 提供 `shape[k]+delta` 的实际求值、逆向
read receipt 和 observation 定律，包含 Figure 2 的 `shape[1]+1`。
observation 记录 raw loaded word 和实际 Mint32 地址；cache 是完整加法表达式
的结果，两者可以不同。地址和加法使用 CompCert 机器语义；数学域的 no-wrap
仍由 numeric/profile condition 另证。

## 每个 inner check 保护全部已有观察

稳定性 presumption 的典型形式为：

```text
every reached BODY write is byte-disjoint from both captured header reads
```

只保护 child 的观察不够：BODY 可能改写下一次 outer comparison 将读取的 word。
新服务统一携带 observation list。双 direct loaded＋offset client 连接两个 raw
observation 列表；indexed header 有同类定律，其完整 scan client 尚待连接。

`nested_expression_prefix_open` 从 actual outer prefix 打开 actual child
prefix，需要原 child execution，不需要 child 的缓存模型 execution。该 prefix：

- observations 和 permission anchor 保留在最初的 guard-entry memory；
- source witness 保留原程序实际到达的 memory；
- 外层 coordinate 和 stable temps 连接到该 witness；
- `memory_accesses_back` 把实际访问权限带回 guard entry。

最后一点只运输权限，不把实际 memory 的内容改回 guard entry。先前 stores
可能已初始化 BODY 会读的其他 cells，强行搬回旧 memory 会丢失这些值。

当前 row 的全部 inner checks 接受后，`nested_expression_row_cached` 导出
这一 row 的缓存执行及全部 observations 的保持，不要求后续 rows 已经检查。
`nested_expression_prefix_advance` 再推进 outer prefix。structured stores 的
权限运输由已有语言定律自动取得，使用者不另交任意 memory-effect 回调。

## 接受后的局部结果

`nested_loaded_offset_initial_cached` 对两个 loaded＋offset headers 证明：

```text
actual original nested source execution
joint snapshots + accepted point-preservation facts
--------------------------------------------------
both cached loops execute
same final memory and exact final temps
all captured observations still match
```

优化方仍要提交或经 checker 取得：每个被覆盖的真实 BODY 在检查接受后保持
observation list，以及源／模型和候选变换的对应。语言库导出 cached execution；
用户不把它作为安全检查的输入。框架不发现这些义务。

当前 `nested_cached_source` 在原 nested syntax 中替换两项比较，保留原 reset
和 BODY。它还不是 affine package 的 canonical model：后者需要
`child_bound := captured_parameter` 等额外 private assignments。连接二者必须
证明 projected execution transport，不能仅因数学 bounds 相同就套候选证明。

## Numeric check 的入口分开

changing loaded child 尚未固定时，不能假设整个 canonical body 能执行。
`affine_captured_package_guard_execution` 复用旧 numeric checker，输入是 root
counter/cache 和已捕获参数的 integer-word domain。递归
`affine_defined_parameters_first_headers` 根据 bound dependencies 许可 private
probe 的读取，未来 controls 由 probe 初始化；接受仍导出原 checked profile 的
`affine_math_domain`。

此服务不读取 data arrays，也不许可 physical alias comparisons。它要求参数
已定义；空外层的第二个 capture 未执行，完整 guard 必须跳过依赖 child 参数
的 numeric phase。Figure 2 的首次 child header 之前只有 reset，没有 memory
store，两项观察都来自原 memory。更一般的 later capture 若在前置 stores
之后，仍须证明这些 stores 不破坏后来捕获的观察，不能自动套已有观察的保持。

## 责任和接入

| 层次 | 本步已提供 | 继续需要的证据 |
| --- | --- | --- |
| 最小 kernel | 继续组合 guard／conditional-local／entry relation certificates | 不发现 assumptions，不检查 Clight 或 affine schedules |
| 语言和 prefix 库 | ordered capture、actual child receipt、public/private temp 运输、reached prefix、joint cache transport、store permissions | 完整新 guard 的资源与安装仍须接实际代码 |
| Affine domain 库 | captured words 到安全 numeric probe、接受到 math domain | actual child points 的访问许可、joint physical scan、覆盖和 point preservation |
| 优化实现者／使用者 | 可复用上述服务 | 选择片段／candidate，提交或经 checker 取得 model／candidate 对应，绑定原 AST 与 placement |

下一项按 narrative `226ba94` 先闭合功能链：joint scan → canonical cached
model → 旧候选 checker／typed pool／原 fallback／factory／host／Csem→Asm →
原 Figure 2 适配源的提取运行。随后继续 compact sufficient conditions 和真实
比较工作、接受域及计时。本步没有新增 kernel 能力或通用 condition projection。
