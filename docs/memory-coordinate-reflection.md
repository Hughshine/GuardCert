# 已验证的坐标反射

外部候选现在可以用 `(reflect position)` 声明坐标映射。这一步把指定的循环坐标取负，保留参数前缀，并同时变换多面体域、调度、指令实参和访问实参。`GuardMemoryCoordinateReflect.v` 证明映射为自身的逆、保持行宽、域成员资格、调度时间和实际指令执行；`memory_coordinate_reflect_execution` 给出完整多面体实例列表的执行等价。`MemoryReindexReflect` 随后进入组合映射的候选检查接口。

例如，对一维源 `for (;i<n;i++) p[i]=q[i]*alpha+beta`，一个直接反向候选为：

```lisp
(map-index ((reflect 0))
  (loop (sum (constant 1) (scale -1 (var 0))) (constant 1)
    (each (instr current ((scale -1 (var 0)))))))
```

候选的私有坐标从 `1-n` 递增到 `0`，实际访问坐标依次为 `n-1` 到 `0`。源循环仍由检查器独立识别；已有指令站点及稳定 RHS 参数由统一入口提供并核对。映射只是候选输入，不能绕过域、访问、依赖或机器代码检查。源和候选的出口公共计数器仍一致。

生成的反向调度也可携带同一映射。在 `scan_copy` 的参数前缀为 `n,alpha,beta` 时，输入为 `(schedule ((affine (0 0 0 -1) 0) ordinal) ((reflect 0)))`。反射还可以和平移组合，例如 `(reflect 0)` 后接 `(shift 0 3)`，并由检查器核对对应的循环范围和 `3-u` 访问式。未携带映射的一维反向输入当前仍拒绝；错误地将 identity 候选标成反射也拒绝。

对于上述逐元素双指针源，[循环式 alias guard](memory-loop-alias-guards.md)检查实际访问地址是否分离。通过时执行反向候选，重叠或其他条件失败时执行原循环。反向执行本身不能消除源中的依赖；二维邻居读写链的回归仍只允许检查器验证通过的计数范围。通用反射证明针对任意坐标位置和维数；本次 280 模块记录中的循环式 alias 检查是一轴、两个访问指针、单位步长和零偏移的实例。后续[一般仿射地址扫描](memory-affine-alias-scans.md)已扩大源范围，并提供 `(negative-coordinate position)` 的调度便利记法。

2026-10-03：280 个适配模块和七个 lowering 模块的完整 Rocq 重编译与假设审计通过，427 个证明源码哈希一致，完整编译器仍为原有 42 项假设。提取编译器 SHA256 为 `27f7f6ec0e39b4beb47e0ec5edf9326234a4298a945640c5b170cb9e35c69576`。

十二组配置共 1200 次完整 CompCert 汇编调用通过，六组接受配置另通过 600 次加标记 Clight 调用：276 次快分支、324 次回退，其中 192 次快分支调用超过旧 cap 8。数组和公共计数器均与 GCC 和独立机器字模型一致。分支诊断仅描述 GCC 执行的 Clight 打印副本；汇编执行结果由独立套件核对。生成反向、直接反向及反射加平移的完整 Clight／汇编文本分别为 10299／9664、9918／9494、10040／9602 字节；guard cap 均为 1024，没有运行速度声明。

`make native-memory-loop-alias` 可复现完整套件，报告在 `build/native-memory-loop-alias/report.json` 和 `branch-report.json`。`native_memory_recursive.loop_template` 也改为使用单步反射，从而支持一维输入，并用于检查二维反射与已有候选的兼容性。

同一新编译器另通过 19 个已有配置的完整汇编回归：多指针、单指针、稳定 RHS 标量、signed 地址各检查二维反射、调度交换、二维分块及伪造证书拒绝；显式源元数据检查后三类。各类 `smoke-report.json` 核对当前编译器和源码哈希。这些是选定配置的回归，没有将旧版完整套件报告计入本轮结果。
