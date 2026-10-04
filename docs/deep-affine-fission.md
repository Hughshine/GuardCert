深层仿射循环可以含多条实际数组语句。外部候选工具可将它们分裂成多个循环，也可提议改变静态语句顺序。源片段、地址守卫、候选执行、公开出口与完整程序继续使用统一入口。

例子包含两类数据依赖：

```c
/* 本轮 producer/consumer：先完成所有 a 的写入，再计算 c 可以成立。 */
a[index] = b[index] + alpha;
c[index] = a[index] + beta;

/* 读取未来迭代：分裂可能提前覆盖源程序应读到的旧值。 */
a[index] = b[index] + alpha;
c[index] = a[index + 480] + beta;
```

候选文件中的 `fission` 工具将每个静态指令站点置于自己的源域循环中。`reverse-fission` 进一步逆转这些循环，提议由相邻交换组成的 `site-order` 描述。描述指明候选静态站点如何映回源站点，依赖验证器仍按候选的实际时间戳检查新执行顺序。

接口中的对应与顺序承担不同义务。`affine_site_swap_execution` 证明相邻交换多面体指令列表的存放位置时，动态站点编号可以可逆重映射；时间戳、实际指令和参数保持一致。因此这一步是表示转换。`affine_site_permutation_execution` 组合多个相邻交换。`validated_affine_site_domain_loops_at` 再连接实际提取器、坐标映射、站点排列、域对齐和原有依赖验证器。它不宣称任意语句顺序都安全。

同一指针内部的依赖由验证器判断。不同指针之间可能在运行时别名，仍由实际源足迹的分离守卫处理。候选被静态拒绝时不安装变换；候选通过验证但运行时守卫拒绝时执行原片段。

`AffineSiteEvidence steps positions` 暴露新的数据接口。`steps` 描述坐标映回源的转换，`positions` 描述候选指令列表的相邻站点交换。实际检查器产生原有 `memory_bounded_source_certificate`，无需修改区域或完整程序正确性契约。

在仓库工具链中运行：

```sh
make affine-nest-prototype-proof
make guardcert-compiler
make native-affine-nest-fission
```

该测试包含独立的两层和三层语句、本轮依赖和未来迭代依赖。它比较全部三个数组和公开控制变量，并独立插桩实际 Clight 分支。完整运行结果与接受范围由 `build/native-affine-nest-fission/report.json` 和 `branch-report.json` 记录；文档中的接口描述不替代这些运行结果。

四组实际汇编配置各运行 492 次，共 1,968 次。identity 接受全部四个源函数；正向分裂接受独立语句和本轮依赖，拒绝未来读取；反向分裂接受独立语句和当前范围内的未来读取，拒绝本轮依赖。资源限制保留全部原片段。三个 Word 模型反例分别展示正向未来读取、反向本轮读取以及 `m=40` 范围外反向分裂的错误，因此接受关系不能只按“是否存在依赖”分类。

独立 Clight 插桩共执行 1,230 次：204 次候选、1,026 次回退，含 130 次同数组分离访问的候选和 166 次数值条件成立但地址重叠的回退。范围外 `m=40` 的调用均回退。插桩由 GCC 执行，与上述真实 CompCert 汇编证据分开记录。
