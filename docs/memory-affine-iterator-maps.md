# 已证明的仿射 iterator 对应

统一 C 编译入口新增 `GuardedMappedCandidate`：候选包含实际 Loop 与一串坐标对应步骤。
步骤作用于候选的多面体 iterator，参数前缀固定。可用步骤包括相邻交换、整数平移和
整数剪切；可以组合它们表达平移后交换、斜向遍历及坐标反转。这里只接受这类可逆操作，
不把任意矩阵声明当作证明。

```text
(map-index ((skew 1 0 -1))
 (loop (constant 0) (var 0)
  (loop (var 0) (sum (var 0) (var 2))
   (each (instr current ((var 1) (sum (var 0) (scale -1 (var 1)))))))))
```

这份外部提案以 `j' = j + i` 遍历内层循环，调用源指令时使用 `j = j' - i`。
`(skew 1 0 -1)` 把候选的 `[i;j']` 映回源的 `[i;j]`。`shift` 的第二个参数也表示
从候选坐标映回源坐标的位移，因此循环起点从 0 改成 3 时使用 `(shift 0 -3)`。
编号 0 表示最外层 iterator；步骤按照列表顺序作用，运行时参数不参与该编号。

`GuardMemoryCoordinateShift` 和 `GuardMemoryCoordinateSkew` 分别证明整数向量的逆映射、
参数前缀保持、域成员对应、仿射计算相等和实际指令执行对应。域约束、调度和访问参数
都随坐标变换，而实际指令和完整 CompCert Mem 保持一致。
`GuardMemoryAffineReindex` 组合这些点同构，证明整个 PolyLang 执行双向对应。

`GuardMemoryAffineMappedExtractor` 提取源和候选、应用候选坐标对应、核对整数域等价，
再消费实际依赖验证证书。点对应不保证新的执行顺序正确；例如坐标反转虽然可逆，
仍可能违反行首读取依赖。`GuardMemoryNamedMappedChecker` 和
`GuardMemoryNamedMappedCompiler` 将这个检查接到真实多数组 C 源和候选后端。
完整入口仍是 `GuardMemoryUnifiedCompiler.compile_memory_unified_regions_correct`，
候选生成器没有正确性前提。

机器运算另行核对。候选每个循环边界与操作数都经过区间检查；数学坐标映射有逆，
并不意味着 `N + delta` 在机器整数上安全。检查失败时不采用候选，完整程序执行原片段。
运行时的范围和实际数组别名 guard 继续由共同宿主生成。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make native-memory-affine-maps
GUARDCERT_LOOP_CANDIDATE="$PWD/examples/loop-candidates/skew-inner.sexp" \
  build/compcert-memory-unified/ccomp \
  -conf build/compcert-memory-unified/compcert.ini \
  -stdlib build/compcert-memory-unified/runtime -S examples/native_memory_multiarray.c
```

局部和完整编译器证明已编译；73 个内存适配模块和 7 个 lowering 模块的全量审计
已经通过。指令桥保持 7 项继承假设，验证器保持 12 项，完整编译器保持 42 项并集，
没有新增全局公理。`build/native-memory-affine-maps/report.json` 已记录十三组通过的配置，
每组 4022 行输出与 GCC 和独立模型一致；其中也包括斜向域的错误参数拒绝回归。
合法映射实际命中十个支持函数，内层反转命中九个，行首读取依赖使三数组函数被拒绝。
错误映射、辅助边界溢出和故障证书均拒绝。测试也检查实际基址比较及公开 iterator 修复。
这扩展了候选侧的表示能力；源 C 仍限于已核对的矩形同布局数组操作，一般仿射 C 源
边界、邻居访问与指针切片仍需继续实现。
