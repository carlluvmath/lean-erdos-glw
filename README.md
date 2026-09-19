# Erdős–GLW 的 Lean 入门形式化

这是对论文 `JSP-000884_GLW01.pdf` 中 Theorem 2 和修正版 Theorem 3 的 Lean 4 形式化。

论文结论用初学者的话说：如果 `n > 2`，并且 `n` 去掉所有 2 的因子后，剩下的奇数部分中每个素因子都至少出现两次，那么

```text
φ(n) > φ(n - φ(n))
```

文件中的路线和学习顺序是：

1. 用 `ℕ` 表示自然数，用 `Nat.Prime` 表示素数，用 `∣` 表示整除；
2. 定义 `Squarefull` 和 `OddPartSquarefull`；
3. 使用 Mathlib 的 `Nat.totient`（欧拉函数）；
4. 证明素因子、素因子分解和欧拉函数之间的小引理；
5. 用有限集合的严格包含证明最后的 Theorem 2。

在本目录运行：

```bash
lake build
lake env lean ErdosGLW.lean
```

主定理是：

```lean
theorem theorem2 {n : ℕ} (hlarge : 2 < n) (hsq : OddPartSquarefull n) :
    n.totient > (n - n.totient).totient
```

这份代码只依赖本地的 Mathlib：`/Users/ahs/tools/mathlib4`。

## Theorem 3：已完成

结论：若 `1 < m`、`m` 是奇数、`3` 与 `m` 互素，且 `p = 3*m - φ(m)` 是素数，
那么 `m` 是 squarefree（没有素数的平方整除它），并且对每个 `k > 0`，
令 `n = 2^k * 3 * m`，都有 `φ(n) + 2^k ≤ φ(n - φ(n))`。
注意 squarefree 与前面的 squarefull 是不同概念。

### 为什么增加 `1 < m`

PDF 第 6 页的 Theorem 3 原文只要求 m 是奇正整数。m=1 满足原文全部假设，
但 k=1 时 n=6、φ(n)=2、φ(n-φ(n))=2，结论却要求 4≤2。
所以本项目明确证明修正版，不宣称证明原文不加限制的命题。
`Verification.lean` 用 Lean 验证这个反例。

### 按顺序读证明

1. `totient_special_product`：φ(2^k * 3 * m) = 2^k * φ(m)。
   只用奇性、互素性和 k>0，不需要 squarefree 假设。
2. `squarefree_of_prime_condition`：若 q² 整除 m，则
   q 整除 φ(q²)，φ(q²) 整除 φ(m)，所以 q 整除 p。
   p 是素数，迫使 q=p；但 q≤m<p，矛盾。
3. `totient_sub_value`：n-φ(n)=2^k*p，所以 φ(n-φ(n))=2^(k-1)*(p-1)。
4. `theorem3_inequality`：φ(m)<m 推出 p-1≥2*(φ(m)+1)，乘以 2^(k-1) 即可。
5. `theorem3`：把 squarefree 和对任意正整数 k 的不等式合在一起。

例子：m=5，p=15-4=11 是素数。k=1 时 n=30，φ(30)=8，φ(22)=10，
恰好满足 8+2=10。验证文件还直接调用 `theorem3`，证明 m=5 时所有 k>0 的结论。

```bash
lake build
lake env lean Verification.lean
```

`#print axioms` 检查主定理只依赖标准基础公理，不含 `sorryAx` 或自定义公理。

### 复用依据

本次公开检索未找到该 Theorem 3 的完整 Lean 实现；这不表示网上一定不存在。
实现复用了 Mathlib 的 [欧拉函数定理](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Totient.html)
和 [squarefree 判别](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Squarefree.html)。
特别是 `Nat.totient_dvd_of_dvd`、`Nat.totient_prime_pow_succ`、`Nat.totient_mul`、
`Nat.squarefree_iff_prime_squarefree`。平方素因子反证的写法亦参考了
[Mathlib 的 Carmichael 数证明](https://github.com/leanprover-community/mathlib4/blob/dec5b2b780537b6eaf7f5e5f000c12f7387fb24d/Mathlib/NumberTheory/CarmichaelNumber.lean#L98-L113)。

环境：Lean v4.35.0-rc2，本地 Mathlib Git 提交
`dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`。
## Theorem 1：已完成

Theorem 1 的无条件 0.54 下密度结论已全部形式化，主定理为 `theorem1_main`（无 `sorry`、无自定义公理）：

```lean
theorem theorem1_main : (54 : ℝ) / 100 ≤ lowerNatDensity theorem1Set
```

其中 `theorem1Set = {n | n.totient > (n - n.totient).totient}`，即论文中 `φ(n) > φ(n - φ(n))` 的自然数集合，其自然下密度至少为 54%。

模块与证明链：

- `ErdosGLW/Theorem1Arithmetic.lean` 证明奇偶充分条件、`totient_le_half_of_even`、有限异常集分割，以及“异常数至多 46% 则好数至少 54%”。
- `ErdosGLW/Theorem1TwoAdic.lean` 证明二进制指数分解，并定义论文的 `B₀(x)`、`Bₛ(x)`；偶数异常点已归入对应 `Bₛ`。
- `ErdosGLW/Theorem1Products.lean` / `Theorem1PrimeProducts.lean` 证明公式 (3) 的异常集覆盖与公式 (4) 的两个乘积上界：`T(x,0) ≤ (1/2)^|B₀|` 和 `T(x,s) ≤ (2/3)^|Bₛ|`。
- `ErdosGLW/Theorem1LogBounds.lean` / `Theorem1PrimeBounds.lean` 证明公式 (5)--(9) 的素数乘积下界、对数和估计。
- `ErdosGLW/Theorem1Final.lean` 汇合得到 `theorem1Exceptional_real_bound`：异常集基数 `≤ x · theorem1MainConstant + theorem1Error x`，且 `theorem1MainConstant < 46/100`。
- `ErdosGLW/Theorem1Limits.lean` 证明误差项除以 `x` 趋于 0（`theorem1DensityError_tendsto`）。
- `ErdosGLW/Theorem1Density.lean` 定义自然下密度，并证明 `theorem1_of_eventual_good_bound`：只要最终好集合比例至少 0.54，下密度结论即成立。
- `ErdosGLW/Theorem1Main.lean` 完成密度拼接：用 `theorem1MainConstant < 46/100` 的严格间隙吸收 `Good → GoodLarge` 的常数损失，结合 `theorem1Error = o(x)`，推出 `theorem1_main`。

构建命令（根模块 `ErdosGLW.lean` 已 import `Theorem1Main`，故 `lake build` 会一并构建全部 Theorem 1 模块）：

```bash
lake build
```
