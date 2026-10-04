外部工具或人可以给统一编译器提交具体 Loop IR 候选。候选不需要来自内置交换或分块策略；数组指令、参数、迭代点对应及依赖仍由已证明的检查器验证。文件中的语法、匹配摘要和映射描述都不构成可信证书。

先导出实际源请求：

```sh
mkdir -p build/manual-requests
GUARDCERT_AFFINE_MODE=disabled \
GUARDCERT_AFFINE_PROFILE=inferred \
GUARDCERT_AFFINE_REQUEST_DIR=build/manual-requests \
build/compcert-guardcert/ccomp \
  -conf build/compcert-guardcert/compcert.ini \
  -stdlib build/compcert-guardcert/runtime \
  -S -o build/manual-original.s examples/native_affine_nest_multiple_pointers.c
```

每个 `.sexp` 文件记录已检查的源 Loop IR、上下文槽位、指针、轴范围和源指令站点。指令记录包含数组访问函数和 word 值计算。Loop IR 使用 de Bruijn 下标：内层坐标在低槽位，稳定上下文位于坐标之后。源导出给出这些槽位的具体实例；候选可以复用源指令站点并改变循环、守卫及指令参数。

例如下面的工具把根坐标从 `i` 改为 `i+1`，同时将子循环和指令中读取的根坐标改为 `i-1`，并提议将候选坐标映回源的 `(shift 0 -1)`：

```sh
python3 scripts/external_affine_candidate.py \
  build/manual-requests build/manual-candidates.sexp \
  --mode shift-root --delta 1
```

导入并编译完整程序：

```sh
GUARDCERT_AFFINE_MODE=external \
GUARDCERT_AFFINE_PROFILE=inferred \
GUARDCERT_AFFINE_CANDIDATE=build/manual-candidates.sexp \
build/compcert-guardcert/ccomp \
  -conf build/compcert-guardcert/compcert.ini \
  -stdlib build/compcert-guardcert/runtime \
  -dclight -S -o build/manual-optimized.s examples/native_affine_nest_multiple_pointers.c
```

文件可以是单个候选，也可以是 `(choices ...)`。`(request DIGEST candidate)` 根据导出的请求选择条目；`(rank N candidate)` 按轴数选择条目。摘要只服务匹配，不绕过语义检查。候选 Loop 语法复用现有解析器的 `loop`、`seq`、`guard`、`instr`、仿射表达式、常量除法、取模及 min/max。实际后端和验证器可能拒绝其中不支持的实例。

`(map-index (steps...) candidate)` 可以提议 `swap`、`shift`、`skew` 和 `reflect`。`(site-order (positions...) candidate)` 提议静态指令列表中的相邻交换，按源站点恢复对应，同时保留候选的实际时间戳。坐标对应、站点排列、域与依赖均由提取的检查器核对。[循环分裂实例](deep-affine-fission.md) 展示该接口处理多语句依赖；内置分块路线仍使用已有分块描述接口。

`(source DIGEST candidate)` 按导出的 `source-identity` 匹配实际源 IR、参数和指令，不包括范围提案，因此可供[有限条件搜索](deep-affine-condition-search.md)在不同条件下重验同一个候选。工具参数 `--source-match` 生成此格式。摘要和匹配均不承担证明义务。

条件合成来自实际源与经过检查的区间提议，而不是要求外部文件自行写一个可信 guard。检查器接受候选之后才安装整数检查、实际源足迹的地址分离扫描、候选执行和原片段回退。公开循环出口值仍由纯源控制重放恢复。这个接口支持人或外部算法提出变换，不要求信任提出变换的算法。

`make native-affine-nest-external` 运行外部 identity、正向平移、负向平移、错误映射、遗漏迭代点、损坏文件和 oracle 资源限制。七组各运行 570 次，合计 3,990 次实际 CompCert 汇编调用；全部数组与公开变量匹配模型。正确候选接受全部五个源函数，其余四组不安装候选。独立 Clight 插桩运行 1,710 次，观察到 270 次候选和 1,440 次回退。

这仍是顺序仿射数组变换接口。任意更改指令计算、volatile、外部副作用或非仿射控制，不会因为使用文件接口自动得到证明。可以另写插件，通过框架的条件正确性与片段契约接口接入这些变换。
