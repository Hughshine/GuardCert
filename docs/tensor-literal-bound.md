# 实际 literal-bound tensor rewrite

这个入口让实际 C 的 `for(k=0;k<5;k++)` 参与已验证的 tensor 交换／分块。
它复用原 tensor 数据 factory、条件编译器、候选 checker 和 backend proof，补充
private literal 初始化及原源／检查后入口的实际执行运输，最后消费既有 kernel
与 expression-progress host。不是先要求原入口已有 fresh helper word。

职责与 narrative 的逐项核对见
[narrative literal-bound check](narrative-literal-bound-check-2026-10-07.md)。

## 实际生成的结构

```c
private_bound = 5;
/* shared guard sets private_choice using the prepared bound */
if (private_choice) {
    private_bound = 5;
    /* checked mapped/tiled tensor code, then public counter restoration */
} else {
    for (; i < n; i++)
        for (j = 0; j < columns; j++)
            for (k = 0; k < 5; k++)
                a[((j*ld)+i)*5+k] += alpha;
}
```

第二次 private 赋值使候选局部定理能够消费任意 public-ports-framed 实际入口；
helper 的值不属于公开关系。Guard 不改变 memory，原 AST 是拒绝分支。公开
ports 保护原源、上下文以及实际检查读到的公开 temps；freshness 和 typed pool
由查验器和语言 host 生产。这个示意省略了真正的安全机器检查，不是一条
`private_choice` 任意输入即可获得正确性的规则。

语言 mapper 只改变精确 typed signed comparison；地址、RHS、store 原样保留。
Chooser、descriptor、profile 和 candidate 是不受信任数据。Wrong literal、错误
坐标／reindex 和零 tile 不能通过相应查验；原 bound 不会被默默改写。

## 已完成的证明与证据边界

- `ClightLiteralBoundPreparation.v`：helper 实际赋值与原程序到 prepared 程序的
  真实 Clight execution/frame 运输。不是只证明两个 AST 在语法上对应。
- `ClightTensorLiteralPreservation.v`：原 silent normal completion 提供检查的
  canonical source-definedness；实际 materialized check execution、acceptance
  soundness、ports frame 和检查后候选执行。候选复用原 tensor correspondence，
  公开出口和 memory 保持。
- `ClightTensorLiteralCompiler.v`：数据查验与 region contract，安装到原 AST，
  完整 `compile_tensor_literal_regions_correct`，Csem→Asm backward simulation。
- `ClightTensorLiteralExample.v`：九项闭合 fixture，含原 literal recognizer、错误
  literal 拒绝、原 helper 未初始化、prepared helper 定义、地址不变和新／旧 host
  progress 区别。

独立 proof audit 是旧181＋新27＝208端点、440依赖、102闭合端点、最大42项
既有全局基线；无新增全局公理，kernel 仍闭合。新27分别是语言5、领域／局部9、
编译接线4、fixture9；依赖数增长包含已存在的 materialized/expression-host
服务。旧tensor proof report 及 sources/objects 的摘要由 parent validator 继续
检查，未替换其历史证据。

Proof report：`build/tensor-literal-region/proof/report.json`，SHA-256
`3e3023f6356f95a1d183ee1ac5e47711d1117b5c90e5e8ab2444776729682546`。
提取入口使用22个 typed private temps（literal helper、Boolean、20 counters）；
构建及 native 报告均绑定实际 source、proof report、objects、policies 和 compiler。

## 复现

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_literal_region.mk proof
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_literal_region.mk compiler
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_literal_region.mk native
opam exec --root=/tmp/guard-opam --switch=guard -- make -f scripts/tensor_literal_region.mk validate
```

## 实际 C 验收

八个配置通过1,152次完整汇编调用：source、identity、interchange、2×3 tiling，
以及错误reindex、零tile、错误坐标和错误literal。十二个函数覆盖两种Horner
地址次序、第三层literal 3／5／0／6、连续两次rewrite，以及goto／外围memory
效果。每次比较全部6,144 words、三个公开counter、首个site出口和context markers，
同时核对GCC `-fwrapv` source与独立Python word模型。保留unused components
参数的0／6输入，确认实际bound来自源literal而非旧参数。

三个有效候选各安装14个Clight sites。432次独立Clight调用每配置记录55次fast、
111次refusal；literal 3／5可接受，0的空第三层及6的coordinate范围外均回退。
Empty outer／literal 0用null pointer验证拒绝前无无效load/store。每个回退体
重新核对原literal test，没有改成private-bound test。错误metadata／literal、
reindex和零tile均不安装site。Clight观察不声称是未修改汇编的路径探针。

单site列访问函数的source／identity／interchange／tile machine bytes是
210／550／550／802。这一入口没有新的成本计时、machine dispatch probe、
source-only fresh rebuild或作者工时比较；不能转用旧入口的性能数字。
Native report：`build/tensor-literal-region/native/report.json`，SHA-256
`9dd4ab29acba9ffa3aa68753d649dd552a685b0b38f142b2b78c19b2d95c5065`。

## 保留的范围与下一步

这个入口仍是
rectangular nests、一个 Horner RMW leaf、一个 tensor；literal 之外的两层上界
仍是 temps。下一功能项是原 loaded grid bounds／+1 与这里的动态 layout 实际
组合；不能把分离实例的能力相加称完整 BT。更广 body、alias、affine domains、
source-only rebuild、代表性性能和比较作者工时继续独立验收。
