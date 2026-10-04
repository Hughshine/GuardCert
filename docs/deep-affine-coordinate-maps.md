外部候选接口支持具体 skew 和 reflection，不需要将它们作为可信优化 pass。`scripts/affine_coordinate_candidate.py` 改写导出的 Loop IR，并提出坐标恢复映射；已证明的检查器核对域、参数、指令及顺序，机器 lowering 另检查候选运算范围。这个工具产生数据，本身不承担证明。

对源的前两层游标 `(i,j)`，skew 定义 `j'=j+k*i`。例如源内层范围 `0≤j<i+m` 改为 `k*i≤j'<(1+k)*i+m`。原叶子中的 `j` 和更深层读取 `j` 的上界都改成 `j'-k*i`。候选使用 `(skew 1 0 -k)` 将候选坐标恢复为源坐标；这里映射描述的轴顺序为外层先，而实际 Loop 表达式环境内层先。任意系数和语法仍由验证器检查。

reflection 将根坐标改为 `ri=-i`。源整数半开区间 `[start,n)` 对应候选 `[1-n,1-start)`，所有子上界、测试及指令参数中对源根游标的读取改为 `-ri`。恢复映射为 `(reflect 0)`。该构造逆转根遍历顺序，可能破坏依赖；正确坐标对应本身不能证明新的顺序合法。

这些具体映射复用 `GuardMemoryAffineReindex`、`GuardMemoryCoordinateSkew` 和 `GuardMemoryCoordinateReflect` 的执行对应定理，通过原有 `AffineIndexEvidence` 接入深层源证书、生成 guard、候选执行、公开出口及完整 Csem→Asm 入口。没有新增 Rocq 公理或编译器特殊可信分支。

```sh
python3 scripts/affine_coordinate_candidate.py requests candidates.sexp --mode skew --factor -2
GUARDCERT_AFFINE_MODE=external GUARDCERT_AFFINE_PROFILE=inferred \
  GUARDCERT_AFFINE_CANDIDATE=candidates.sexp \
  build/compcert-guardcert/ccomp -conf build/compcert-guardcert/compcert.ini \
  -stdlib build/compcert-guardcert/runtime -S source.c
```

先按[外部候选接口](external-affine-candidates.md)从实际源导出 `requests`，再提出候选。测试使用正系数 `1`、负系数 `-2`、根 reflection、缺少对应映射的错误候选及 oracle 资源限制。两份 skew 接受全部五个二层／三层源函数；reflection 接受四个独立函数，拒绝有未来读取依赖的 `multi_chain2`。独立 Word 模型在输入 `(2,0,0,3,2,2,-7)` 上给出错误根逆序的完整数组反例。

六组各运行 570 次，合计 3,420 次实际 CompCert 汇编调用。数组、公开游标和辅助出口全部与源 Word 模型和 GCC 参照一致。覆盖包括负候选坐标、源负入口、重叠地址、同块分离地址、空路径，以及值计算的 signed32 回绕。范围 guard 仍针对控制与地址的数学对应，不假设所有数据计算不溢出。

`make native-affine-nest-affine-maps` 运行此测试及单独的实际 Clight 分支诊断。证明与二进制复用此前 102 模块／713 证明源的已审计入口；本阶段新增候选数据产生工具与执行证据，未改编译器实现。

实际 Clight 的分支诊断另运行 1,597 次：246 次候选、1,351 次回退。两份 skew 各为 90 次候选、480 次回退；reflection 的四个已接受函数为 66 次候选、391 次回退。诊断还检查同块不相交地址、实际重叠回退及未定义深层参数的零次 guard 读取。这些 GCC 诊断只提供路径证据，实际汇编与证明独立保存。

同一统一入口二进制累计覆盖本阶段及此前固定的服务测试，共 22,772 次汇编调用、11,384 次分支诊断；二进制哈希没有改变，原有报告仍对应同一编译器。
