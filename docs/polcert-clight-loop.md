# 实际 Loop 计数循环与语言插件接口

`PolCertCountedClight.v` 与 `PolCertClightBody.v` 在已证明的仿射表达式和范围 guard 上增加有限计数循环及结构化 body lowering。实际输入仍是 PolCert 的 `Loop.stmt`，实际输出是 CompCert 的 Clight statement。

## 插件提供基本指令

`instruction_backend` 暴露 `lower_instruction` 与执行证书。指令实现自行定义 `I.State.t` 与 Clight 内存之间的 `view`，并证明实现相同的抽象指令执行。操作数通过 `operand_view` 对应实际 signed32 表达式与数学整数。

当前接口要求基本指令无观察 trace、正常结束并保留 temporaries；可以修改内存。这个限制适合参数只读、通过内存访问数组的初版实例。插件仍需证明具体指令的内存访问及实现，接口声明不代替这些证明。

框架负责：

- 检查并 lowering 仿射操作数列表。
- `Instr` 调用插件的指令实现及执行证书。
- `Seq` 组合指令／片段的执行。
- `Guard` 将已检查的实际 Loop 测试降低为条件树，与 body 或 `Sskip` 组合。
- 为一个外层 `Loop` 生成边界初始化、signed 比较和 iterator 增量。

初版 body 编译器拒绝内部 `Loop`；因此当前支持一个外层循环及由 `Instr/Seq/Guard` 组成的 body。嵌套循环需要扩展 private temporary 的状态关系。

## 运行时区间与计数器

`compile_single_loop` 使用区间分析给出的下界最小值、上界最大值，推导 body 的 iterator 区间。生成代码的入口先执行通用 range guard；接受建立原参数区间。实际迭代保证下界不大于当前 iterator，当前 iterator 严格小于上界，因此 body 的窄区间有证明支撑。

生成的循环形如：

```c
limit = upper;
iterator = lower;
while (iterator < limit) {
  body;
  iterator = iterator + 1;
}
```

`header_fresh` 检查 iterator 与 limit 不同，且二者不覆盖参数 layout。它只证明相对于参数布局的新鲜性；完整程序宿主还须分配私有标识符，并证明不会覆盖区域外的活跃 temporaries。

源迭代对应实际 PolCert `Zrange lower upper`。空范围不执行 body，最终 iterator 为 lower；非空范围最终为 upper。统一终值是 `Z.max lower upper`。上界可以等于 `INT_MAX`，最后一次增量从 `INT_MAX-1` 到 `INT_MAX` 后退出，不需要表示 `INT_MAX+1`。

## 证明端点

| 定理 | 提供的保证 |
| --- | --- |
| `range_iterations` | 真实 PolCert 的列表迭代语义与有限计数迭代对应。 |
| `compile_body_correct` | 给出指令插件、入口参数范围与 `typed_view` 后，成功编译的结构化 body 保持实际 Loop 的每次终止执行和内存 view。 |
| `compile_loop_header_correct` | 给出 body 实现证书后，运行时 guard 接受和静态边界证书足以降低一个真实 Loop 循环。 |
| `compile_single_loop_correct` | 组合 body 编译、推导的 iterator 区间和循环代码，得到正常、无迹的 Clight 执行。 |
| `compile_loop_header_steps` | 将循环执行提升为实际 Clight 小步 `star`，可放入任意函数及 continuation，结束于同一函数／continuation 的 `Sskip`。 |

已证明的空 body 实例不依赖指令实现证书；另有实际算法的仿射边界与临时变量冲突拒绝例子。

这些端点没有建立多面体优化的完整程序 simulation。尚需具体 C 指令／内存 view 实例、源区域提取、嵌套循环与 private temporary 的 frame、候选进展，以及多语句区域替换的宿主证明。已有 [PolCert 优化器适配](../adapters/polcert-optimizer/README.md) 消费的是 backward Loop endpoint；这里的 lowering 证明是从 Loop 执行到 Clight 执行，二者的方向与进展义务仍须明确组合。

## 复现

```sh
make polcert-loop-proof POLCERT_SOURCE=/path/to/verified-compilation-v10-driver
```

该目标包含仿射桥接的全部证明，并编译计数循环及 body 适配器。`build/polcert-loop-report.json` 比较实际 `ClightBigstep.exec_stmt`、`exec_stmt_steps` 的假设和新增适配器，只允许继承的语义假设及声明的 `I.State.t/I.t/I.instr_semantics`。语言插件执行证书是显式定理参数，没有新增公理。
