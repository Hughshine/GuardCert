# 真实 double tiling：提取编译器、原案例与回退

2026-10-09。本后继接上 [double tiling 证明链](double-tiling-proof.md) 的实际
native producer。用户给 marked C 和策略；目标来自真实 Pluto phases 和
提取的 prepared codegen，不要求手写 target 或 semantic callbacks。
[固定摘要](double-tiling-installation.json)验证15 reports、14,485 bindings，
SHA-256 `f4fd020f6c617c5bcbc2a2c7494f0f1aadb75cbd41ce1303fa65cfc3bc4c5c02`。
完整 goal active。

## 原程序验收

| Build／检查 | 实际结果 | 范围 |
| --- | --- | --- |
| Native-v1；62 raw originals＋2 disclosed adaptations | 59 raw和2 adapted native matches；2 known frontend refusals；`tce` 编译180秒超时 | Tile32、scratch32；9/62安装22处 |
| Native-v2；原 `tce` 较长预算重试 | 四处十层 tiled loops安装，digest匹配原GCC | 原五维double计算；600秒预算，编译229.206秒仅为诊断 |
| Native-v1；`mvt`／`matmul-seq` 五模式矩阵 | 10/10；tile各安装两处，其余不安装 | Unmarked、外部拒绝、错见证、malformed |
| Native-v1；轴大小 `(2,3)` | 原 `mvt` 两处安装、digest匹配 | 非方形tile |
| Native-v1；contexts | 14/14符合安装预期并匹配GCC | Dynamic、公开出口、多marked／unmarked、资源、旧路线 |
| Native-v1；unchanged assembly | 3/3 debugger observations通过 | 正／零输入两次candidate entry，负输入两次fallback entry |
| Native-v2；单位坐标补全 | 4/4：二维 `(1,3)`、`(3,1)`、`(1,1)`，三维 `(1,3,2)` | 原 `mvt`／`matmul-seq`，同一最终checker |
| Native-v2；默认32 regression | 原 `mvt`／`matmul-seq`各两处安装、digest匹配 | 普通nonunit配置保留 |

两份已绑定 builds 的实测并集为 **10/62原案例、26处** tiling installation：
`fusion6`、`fusion7`、`gemver`、`matmul-seq`、`matmul-seq3`、
`multi-loop-param`、`mvt`、`mxv-seq`、`mxv-seq3`、`tce`。
这不是 native-v2 重跑全部语料。Installation、源点顺序变化和收益分别记账；
一维tiling可以保持点顺序。不增加先前affine的8/62 nonidentity计数。

完整tile32比较中，50个已编译raw originals没有调用tiling phase。该配置
专门启用tiling，拒绝保持source，不用旧affine安装掩盖tiling拒绝。内部
static checker仍待逐个定位，不能统一归因于frontend。`corcol3`／`pca` 的
raw refusal和显式initializer adaptation继续分开；原double／I64运算保留。

## 接口和证明链

完整入口仍是
`DoubleTiledChoicesCompiler.compile_selected_tiled_choices_program`，对应
`..._correct` 为原Csyntax program的Csem→Asm backward simulation。
本native阶段没有修改Rocq源／objects、checker、kernel或host；没有新增语义
证明或global axiom，最大继承基线仍为42 globals。

`GuardSelectedDoubleTiledCandidate.phase` 导出actual OpenScop，运行真实Pluto
`--identity --nointratileopt --tile --noparallel` 等选项，读取midtransform／
afterscheduling输出，依据actual tile-domain rows提议point-space witnesses。
提取代码检查affine和tiling transitions，再调用prepared codegen。这是
**identity pretransform＋真实tiling**；自动affine scheduling后接tiling、ISS
及post-tiling phases仍未由本producer接通。

`adapt` 保留generated loop skeleton、instruction与argument tree，提议affine
enclosure和原域membership guards；point loops优先用tile-local bounds。
最终checker核对实际lowering的body，并在捕获参数下生产candidate execution。
Phase receipt不代替这个检查。当前最终模型检查覆盖所有参数，因此没有直接
把runtime limit当作常数上界截断quotient loops；充分parameter profile及其
检查接线仍需后续证明。Runtime guard复用safe count capture／footprint limit；
global metadata生产block separation，本阶段没有新增dynamic alias test。
原源执行是proof起点，不是runtime预执行。

第一次 `(1,3)` 已通过phase/codegen，但最终checker拒绝：codegen复用了
unit quotient作source point，删除了witness仍需的独立维度。原source保留、
native结果匹配，该拒绝不计支持。`GuardSelectedDoubleTiledCoordinates`
后继检查actual instruction slots，提议singleton point loops及argument重绑；
partial／all-unit均由同一tiling checker核对，不信任补全算法。其他skeleton
仍可能拒绝，四配置不证明任意affine/unit completion。

Native-v2 的原prepared输出是 `original-raw-generated.loop`，补全提议是
`completed.loop`，最终lowering输入为 `generated.loop`。Base adapter的
`raw-generated.loop` 记录adapter输入；unit情况下该输入已经补全，不将它
误称为原codegen。各阶段分别保留。

## Context、失败与成本边界

Public `(i,j)=(17,23)`：正界限退出 `(96,96)`，零／负界限为 `(0,23)`，
保留未到达的inner control。两个marked regions安装4处、实际调用4次Pluto；
有相同unmarked neighbor时只安装2处、调用2次。当前tiling没有旧affine的
proposal memoization。Private不足时静态拒绝、不调用phase；旧identity／
affine的mvt回归通过。Debugger只观测入口，没有改source、compiler或assembly。

首次context脚本误用旧memoization调用数，随后在legacy options的重复环境
keyword上停止；12项已完成native checks没有mismatch。失败／停止记录保留，
后继14项通过。第一次unit拒绝、full-corpus的`tce` terminal timeout和较长
预算后继也全部绑定。

没有受控速度或isolated guard-cost结果。部分检查并发，调用含harness初始化
和digest；`tce`完成较长预算验收不等于解决编译成本。Automatic scratch sizing、
紧凑quotient bounds及更快高维检查／codegen继续需要实际诊断。

## 使用与下一步

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/build_double_tiled_coordinates_compiler.py --attempt new-name
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/probe_double_tiled_originals.py \
    --compiler-report build/double-tiling/compiler-attempts/new-name/report.json \
    --attempt new-original-checks
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/summarize_double_tiled_installation.py --validate
```

已构建：`build/double-tiling/compiler-attempts/native-v2/ccomp`。
`GUARDCERT_ORIGINAL_MODE=tile`选择本路线；`GUARDCERT_TILE_SIZES`为一个
重复到各轴的正整数，或rank相符的逗号列表。当前仍通过`GUARDCERT_PLUTO`／
`GUARDCERT_ORIGINAL_OUTPUT`配置工具及独立dump目录；private count是检查过的
资源参数，默认16，本次五维用32。Tiling disabled时保留旧affine／identity。
摘要复核冻结证据，不自动重跑实验。

下一步接真实affine scheduling后的tiling，扩initialized／multiple-bound／
loaded及其他actual source structures，再推进ISS及其余sequential routes。
Source/model、条件安全／充分性、最终候选及whole-program delivery随每项扩展
一起验收。完整PolCert配置、原BT、LLVM／SPEC、larger tiers、有用接受域及
受控完整成本继续保留，不能以本阶段10案例代替完整目标。
