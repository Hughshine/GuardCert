# 语言无关入口协议原型

当前使用者契约见 [guarded-rewrite-contract.md](../../docs/guarded-rewrite-contract.md)：使用者选择片段、候选及位置，框架插入只读 condition、源回退并证明等价。底层入口协议的设计与分类见 [language-independent-interface.md](../../docs/language-independent-interface.md)。

`GuardInterface.v` 暴露语言、检查、条件变换和上下文四份契约；它证明 guarded refinement、独立的 preservation 及满足宿主插入／目标可安装条件时的程序 refinement。状态、观察、检查的安全性质和关系均由实例解释。检查的存在性不能代替非确定语言的所有路径进展。

`GuardInterfaceExamples.v` 提供不依赖 CompCert 的数学函数语言。检查保留公开输入并覆写私有 scratch；实例覆盖绝对值特化、候选／回退、函数 continuation、任意死候选和 unknown 的否定，还证明源 preservation 不排除新增目标结果。

`GuardedRewrite.v` 提供只读条件、条件性局部等价、基于相同 view／frame 还原的局部提升及程序等价组合。`LocalScheduleEquivalence.v` 复用现有交换链，补足两方向的执行对应。`GuardedRewriteExamples.v` 展示单元分离下的有限循环写入重排和非回绕下的分支删除；各有 frame、条件编码和纯函数 continuation 证明。

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make interface-proof
```

这条命令编译五个接口模块及三个既有依赖，并保存源码摘要和二十三个接口闭合端点的检查记录，其中只读 rewrite 扩展占十四个。它不重建现有 CompCert 编译器，也不提供任意语言的现成适配器或一般条件发现。
