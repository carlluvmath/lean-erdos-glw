import ErdosGLW

open ErdosGLW

-- 原文漏写 m > 1 的边界反例：原假设成立，结论在 k=1 不成立。
example : Odd (1 : ℕ) ∧ Nat.Coprime 3 1 ∧ Nat.Prime (3 * 1 - Nat.totient 1) := by
  decide
example : ¬ (Nat.totient (n3 1 1) + 2 ^ 1 ≤
    Nat.totient (n3 1 1 - Nat.totient (n3 1 1))) := by
  decide

-- m=5 满足修正后的全部条件；直接调用新定理，覆盖任意 k > 0。
example : Squarefree (5 : ℕ) ∧ ∀ k : ℕ, 0 < k →
    Nat.totient (n3 5 k) + 2 ^ k ≤
      Nat.totient (n3 5 k - Nat.totient (n3 5 k)) := by
  exact theorem3 (by decide) (by decide) (by decide) (by decide)

-- 具体例子 k=1：n=30，φ(n)=8，φ(22)=10。
example : n3 5 1 = 30 ∧ Nat.totient 30 = 8 ∧ Nat.totient (30 - 8) = 10 := by
  decide

-- 排除 k=0 是必要的：m=5, n=15 时加强后的不等式失败。
example : ¬ (Nat.totient (n3 5 0) + 2 ^ 0 ≤
    Nat.totient (n3 5 0 - Nat.totient (n3 5 0))) := by
  decide

#print axioms ErdosGLW.theorem2
#print axioms ErdosGLW.theorem3
#print axioms ErdosGLW.totient_le_half_of_even
#print axioms ErdosGLW.mem_theorem1Bs_two_adic
#print axioms ErdosGLW.theorem1Exceptional_covered
#print axioms ErdosGLW.theorem1T_le_two_thirds_pow
#print axioms ErdosGLW.theorem1T_zero_le_half_pow
#print axioms ErdosGLW.theorem1_of_eventual_good_bound
#print axioms ErdosGLW.theorem1Exceptional_real_bound
#print axioms ErdosGLW.theorem1MainConstant_lt
#print axioms ErdosGLW.theorem1_main
