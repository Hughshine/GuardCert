# 辅助变量与带检查的循环分块

这条路径给片段变换增加了 private temporary 出口，并实现实际的 strip-mining：把动态计数循环分成至多 `B` 次迭代的连续块，包含尾块，接入完整 Csem→Asm。迭代顺序保持不变，因此允许循环体读取和写入数组、包含条件与多条语句，以及存在循环携带依赖或指针别名。它补齐了一种基本分块能力；一般仿射调度、带重排的多维 tiling 和依赖验证仍是后续工作。

## 使用效果

源代码是前端生成的 signed32 单位步长循环，循环体只改变普通内存。形如：

```c
for (; i < n; ++i) {
  a[i+1] = a[i] + b[i];
  if (i % 2 == 0) b[i] = a[i+1] - b[i];
  else b[i] = a[i+1] + b[i];
}
```

选择器在完整 AST、类型、控制变量区别、循环体效果和 helper freshness 核对后，使用统一性质与条件合成接口生成检查。逻辑上输出：

```c
if (i == 0 && 0 < n && n <= INT_MAX - B) {
  while (i < n) {
    private_end = i + B;
    if (n < private_end) private_end = n;
    for (; i < private_end; ++i) {
      /* 原循环体 */
    }
  }
} else {
  /* 原循环 */
}
```

实际 lowering 使用已有共享回退结构，原片段只出现一次。`private_end` 被加入函数的 `fn_temps`，它的值可以在出口改变。所有源程序标识符上的 temporary 值保持一致，完整 CompCert 内存相同。

`B` 是不受信任的配置输入，Rocq 选择器验证其为正且可表示为 signed32；0 或过大提案拒绝变换。运行时 `n <= INT_MAX-B` 建立辅助加法的无溢出前提。原循环的计数器与边界定义性从真实源执行推出。guard 只读取这些 temporaries，不读取数组、不改变内存，也不读取尚未初始化的 helper。

## 框架接口与证明

`ClightTempFootprint` 计算源表达式、语句和程序的 temporary 集合。`ClightTempScope` 证明这个范围随完整 Clight 执行保持，覆盖调用、返回、标签跳转和 switch。表达式运输以及 `ClightProjectedExecution.structured_execution_temp_transport` 证明，两个入口在源范围上相等时，辅助变量的不同值不会影响源片段执行。

`PrivateRegion.projected_region_contract live source target` 接受两个可能不同的 temporary 环境。它要求入口在 `live` 上相等，给出候选的实际小步执行、出口在 `live` 上相等及等价内存。`PrivateRegionProof.transform_program_correct2` 将这个局部契约提升到完整 Clight forward simulation。函数入口为辅助声明建立 `Vundef`，调用 continuation 分别保存两侧的 temporary frame，返回值只更新相应的源 temporary。

`transform_private_program` 在程序级 freshness 核对成功后，将 helper pool 加入每个内部函数。候选插件收到完整程序的源范围与声明池；碰撞会保留原程序。当前实例消费池中一个 signed32 helper。候选需要在读取辅助变量前自行初始化；宿主不假定它们有定义值。

`encoded_private_rule` 复用 `property_dimension`、检查原语和公式合成。插件提供源效果、检查域、源执行建立检查域的证明，以及前提成立时的实际候选执行和出口投影。`encoded_private_rule_sound` 负责把入口投影、条件合成、候选／原片段分派和出口关系接到区域契约。

具体分块证明分为：

- `CountedStripmine`：任意正块大小的迭代分割与拼接，证明没有丢失、增加或重排迭代；闭合于全局上下文。
- `ClightStripmineLoops`：辅助边界计算、尾块截断、真实内存循环体的 canonical execution 以及实际分块循环重建。
- `ClightStripmineGuard`：把计数起点与无溢出前提编码到安全的布尔检查，通过正向证据维度与共享条件合成器连接。
- `ClightStripmineRegion` / `ClightStripmineSelector`：实际源循环解码、源／候选执行对应及不受信任 AST 提案的核对。
- `StripmineCompiler.compile_stripmine_regions_correct`：对任意块大小输入的完整 Csem→Asm backward simulation；假设与原 CompCert 的 35 项完全一致。

编译路径先应用动态矩形交换，再应用带辅助变量的分块，最后复用分支／表达式 rewrites 与原 CompCert 后端。这里的组合定理允许这些 pass 串联；没有把分块内存对应当作一般调度的依赖验证。

## 运行与边界

```sh
make native-stripmine
GUARDCERT_TILE_WIDTH=7 build/compcert-stripmine/ccomp ... program.c
```

默认 `B=4`。原生 driver 的解析范围为 0…1024，用于限制配置输入的解析成本；Rocq 定理本身覆盖任意自然数提案。假设审计记录在 `build/stripmine-proof-report.json`，原生结果在 `build/native-stripmine/report.json`。本轮八种块大小的动态依赖／别名案例、递归与控制流上下文，以及同一编译器中矩形交换与分块的串联全部通过；具体数量和实际验证范围见 [validation.md](validation.md)。

本实例不接受循环体中的 temporary 赋值、调用、volatile 操作或提前 break/continue。真实前端通常把 volatile 操作降低为 builtin，从而被效果核对拒绝。数组读取、写入、分支及多个普通内存语句可以接受；不要求数组访问无别名，也不要求 loop-carried dependency 不存在，因为执行顺序保持不变。未进行性能测量，也未接入外部多面体调度器。
