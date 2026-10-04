# CompCert 与 Rocq 基线

核对日期：2026-10-04。官方[下载页](https://compcert.org/download.html)和 [v3.18 发布记录](https://github.com/AbsInt/CompCert/releases/tag/v3.18)均将 CompCert 3.18 列为最新 release。这里锁定 release，而不跟随 master。

| 项目 | 本轮实际使用 |
| --- | --- |
| CompCert tag | `v3.18` |
| Tag commit | `14d616046360a0b2611ebdfc2f98368af402e1f7` |
| Rocq core / runtime | `9.2.0` |
| Rocq Stdlib | `9.2.0` |
| OCaml | `4.14.1` |
| Menhir | `20260209` |
| CompCert target | `x86_64-linux` |

v3.18 的 [configure](https://github.com/AbsInt/CompCert/blob/v3.18/configure) 支持 Rocq 9.0、9.1、9.2；最新 Rocq 不必与 CompCert 支持的最新版本相同，因此本项目明确选 9.2。核心源码使用 `From Stdlib`，构建使用 `rocq compile`。

下载的发布归档有一个元数据细节：其 `VERSION` 文件仍写 `version=3.17`。我们按已核对的 v3.18 tag、完整 commit 和归档 SHA-256 锁定来源，没有修改该上游文件或用版本字符串代替源码身份。

## 复现

依赖版本和归档 checksum 记录在 [toolchain.lock.json](../toolchain.lock.json)。新环境执行：

```sh
sh scripts/bootstrap.sh
opam exec --root="$PWD/.toolchain/opam" --switch=guard -- make check-compcert
```

bootstrap 只在隔离 opam root 中安装工具，不设置用户 shell、不做全局安装。`GUARD_OPAM_ROOT` 可以指定已有隔离 root。本轮实际 root 在 `/tmp/guard-opam`：

```sh
GUARD_OPAM_ROOT=/tmp/guard-opam sh scripts/bootstrap.sh
opam exec --root=/tmp/guard-opam --switch=guard -- make clean
opam exec --root=/tmp/guard-opam --switch=guard -- make check-compcert
```

`fetch_compcert.py` 将 checksum 核对后的上游 release 放在 `vendor/CompCert`；已有目录必须带匹配的来源记录，否则脚本停止，避免覆盖其他 checkout。上游 license 保留在下载目录中。

CompCert 构建等价于：

```sh
cd vendor/CompCert
./configure -clightgen x86_64-linux
make depend
make -j4 proof
```

`make check-compcert` 完成独立证明核与 Python 检查、CompCert proof 构建以及真实 Clight pass 和端到端定理编译。首次构建的依赖分析及完整 upstream proof 构建已实际通过；bootstrap 脚本也在已有隔离 switch 上执行通过。新 root 从头编译 OCaml 的路径尚未在本轮另建环境重复测试。

`make check-integration` 还在 `build/compcert-guard` 的独立副本中提取新驱动并构建 ccomp，运行真实 C 到汇编及原生示例。没有运行安装目标或改写 `vendor/CompCert` 源码。复现：

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make clean
opam exec --root=/tmp/guard-opam --switch=guard -- make check-integration
```

上述 `check-integration` 对应早期分支／表达式接入，提取入口为 `compile_common_rewrites`；其 C 示例和证明是独立的基线检查。当前统一入口是 `AffineNestUnifiedCompiler.compile_guardcert`，已连接深层单／多指针循环、实际源足迹检查与标量 rewrite。先完成既有适配器的 `make guard-memory-proof`，再在同一 Rocq 环境运行 `make affine-nest-prototype-proof` 和 `make guardcert-compiler`；具体执行命令见[使用说明](api-usage.md)和[统一编译器](unified-guardcert-compiler.md)。当前证明／运行记录与未完成的表达能力见[2026-10-04 交付记录](research-checkpoint-2026-10-04.md)，不能由早期目标的通过代替。
