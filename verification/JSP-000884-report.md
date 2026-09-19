# JSP-000884 Lean 验证报告

## 结论

> **总体结论：验证通过。**
>
> 对于 JSP-000884（GLW01：Erdős 关于欧拉函数不等式的猜想），在证明仓库
> `https://github.com/carlluvmath/lean-erdos-glw` 的完整 commit
> `805cd915ecb4f33923431ce4c3bc088dd479b054` 上，该提交已**完整解决**指定原题
> （论文全部三个定理）。决定性理由：三个定理均有对应 Lean 声明，`lake build`
> 原样构建通过，`audit.py run` 对全部目标完成显式检查且仅依赖标准公理
> `[propext, Classical.choice, Quot.sound]`，无 `sorry`/`admit`/`sorryAx`/`native_decide`。

| 必答问题 | 明确判断 | 决定性依据 |
| --- | --- | --- |
| 证明对象是否就是指定原题？ | 是 | 论文 Theorem 1/2/3 与 `theorem1_main`/`theorem2`/`theorem3` 逐一定义、量词、假设、结论对应（见覆盖矩阵） |
| 指定 commit 是否实际验证通过？ | 是 | `lake build` 退出码 0；`audit.py run` 三目标 `lake build +Module`、`lean` 显式检查均 exit 0 |
| 是否完整解决原题？ | 是 | 原题三个定理全部覆盖，无缺失子题，无 `sorry`/占位假设 |
| 是否满足本次验证的 Lean 完整性要求？ | 满足 | 三目标公理审计均为 `standard_axioms_only`，Theorem 3 的 `1 < m` 是对论文边界反例的必要修正（见发现） |

复核级别：实际 Lean 检查（干净构建 + 显式目标检查 + `#print axioms` 公理审计）。
未执行 kernel replay 与独立外部 checker（本提交未提供 challenge/comparator 入口，工具链未配置）。

## 固定证据

- 验证时间：2026-09-20（本地时区 UTC+8）
- 原题：JSP-000884，`problems/catalog-0801-0900.md`；原始来源 GLW01《A conjecture of Erdős concerning inequalities for the Euler totient function》，Publ. Math. Debrecen 59/1-2 (2001), 9-16。
- Lean 仓库：`https://github.com/carlluvmath/lean-erdos-glw`，分支 `main`，验证 commit `805cd915ecb4f33923431ce4c3bc088dd479b054`（branch tip 与验证 commit 一致）。
- 工具链：`leanprover/lean4:v4.35.0-rc2`；Mathlib 固定 `dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`。
- targets.json：`/tmp/lean-verify-jsp884/manifest.json`（三目标）。

## 数学命题与覆盖

原题（GLW01）三个定理与 Lean 声明对应：

| 原题要求 | Lean 声明 | 对应关系 |
| --- | --- | --- |
| Theorem 1：`δ₋(A) ≥ 0.54`，`A = {n : φ(n) > φ(n−φ(n))}` | `ErdosGLW.theorem1_main : (54:ℝ)/100 ≤ lowerNatDensity theorem1Set` | `theorem1Set = {n \| n.totient > (n−n.totient).totient}`，下密度定义一致 |
| Theorem 2：`n > 2` 且奇数部分 squarefull ⇒ `φ(n) > φ(n−φ(n))` | `ErdosGLW.theorem2` | `2 < n → OddPartSquarefull n → n.totient > (n−n.totient).totient` |
| Theorem 3：m 奇、`(3,m)=1`、`p=3m−φ(m)` 素数 ⇒ m squarefree ∧ `∀k>0 φ(n−φ(n)) ≥ φ(n)+2^k`（n=2^k·3·m） | `ErdosGLW.theorem3` | 结论与论文一致；假设额外加入 `1 < m`（见下） |

覆盖矩阵：三个 requirement 各自 `coverage = full`，targets 一一对应，无未覆盖要求。

## 环境与执行

| 项目 | 实际值 |
| --- | --- |
| OS/架构 | macOS（darwin，arm64），未使用容器隔离（本地 self-check） |
| 工具链 | Lean/Lake v4.35.0-rc2（`/Users/ahs/.elan/bin/lake`） |
| 依赖 | mathlib `dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`（git 依赖，见 lake-manifest.json） |
| 原样构建 | `lake build` → exit 0，3514 jobs |
| 显式目标检查 | `lake build +ErdosGLW.Theorem1Main`、`lake build +ErdosGLW`、逐文件 `lake env lean` → exit 0 |
| 公理审计 | `audit.py run` → `mechanical_status = standard_axioms_only`，exit 0 |

## 证明依赖与缺口

三个目标的 `#print axioms` 结果均为 `[propext, Classical.choice, Quot.sound]`（标准经典基础，非缺口）。
无 `sorryAx`、无 `native_decide` 生成的信任公理（`theorem1OddPrimes_501` 已用纯内核 `decide` 证明）。

## 发现、限制和下一步

1. **Theorem 3 的 `1 < m` 修正（非缺陷）**：论文原文仅要求 m 为奇正整数，但 m=1 时
   `p = 3−φ(1) = 2` 为素数、满足全部假设，而 k=1 得 n=6：`φ(4)=2`，结论要求
   `φ(6)+2 = 4 ≤ 2`，矛盾。提交者显式加入 `1 < m` 修正该边界反例，README 已说明。
   这是对论文笔误的必要修正，不构成未解决额外假设。
2. **限制**：未执行 kernel replay / 独立 external checker；未使用容器隔离（本地干净构建代替）。
3. **下一步**：维护者独立复现 `lake build` 与公理审计即可确认。

## 可复现产物

- targets 清单：`/tmp/lean-verify-jsp884/manifest.json`
- 预检结果：`/tmp/lean-verify-jsp884/preflight/result.json`
- 机械审计：`/tmp/lean-verify-jsp884/run/result.json`（exit 0，`standard_axioms_only`）
- 审计脚本：`audit.py`，sha256 `5db45dddcb4d588bc27e7c7161fbca5cedaa3e73e1c40843d21f5a214323cd07`
- lean-verify skill 版本：awards 仓库 `38e63c424c7196f8d4ceb664c5c25f0c0529d5e2`

复现命令：

```bash
cd /path/to/lean-erdos-glw
git checkout 805cd915ecb4f33923431ce4c3bc088dd479b054
lake build
lake env lean ErdosGLW/Theorem1Main.lean
lake env lean ErdosGLW.lean
# 公理审计（#print axioms 三个目标，均为 [propext, Classical.choice, Quot.sound]）
```
