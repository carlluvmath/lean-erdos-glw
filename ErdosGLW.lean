import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Ring
import ErdosGLW.Theorem1
import ErdosGLW.Theorem1Main

namespace ErdosGLW

open Nat Finset

/-!
# 给初学者的路线

这份文件按五步把论文中的 Theorem 2 写成 Lean：

1. 自然数、素数和整除由 `ℕ`、`Nat.Prime`、`∣` 表示；
2. `Squarefull` 和 `OddPartSquarefull` 表示 squarefull 条件；
3. 使用 Mathlib 已有的 `Nat.totient`；
4. 先证明“平方素因子会出现在欧拉函数里”等小引理；
5. `theorem2` 用有限集合的严格包含完成论文结论。

-/

/-- A first tiny Lean exercise: divisibility. -/
example : 2 ∣ (12 : ℕ) := by decide

/-- A first tiny Lean exercise: primality. -/
example : Nat.Prime 5 := by decide

/-- Mathlib can calculate small values of Euler's totient function. -/
example : Nat.totient 9 = 6 := by decide

/-- Every prime factor of a squarefull number occurs with exponent at least two. -/
def Squarefull (m : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ m → p ^ 2 ∣ m

/-- The odd part of `n` is the part left after removing all powers of two. -/
def OddPartSquarefull (n : ℕ) : Prop :=
  Squarefull (ordCompl[2] n)

lemma prime_dvd_totient_of_sq_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hpow : p ^ 2 ∣ n) : p ∣ n.totient := by
  have hk : 2 ≤ n.factorization p :=
    (hp.pow_dvd_iff_le_factorization hn).mp hpow
  let f : ℕ →₀ ℕ := Finsupp.single p 2
  have hmem : p ∈ n.factorization.support := by
    rw [Finsupp.mem_support_iff]
    exact (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hk))
  have hsupp : f.support ⊆ n.factorization.support := by
    intro q hq
    have hqp : q = p := by
      simpa [f] using hq
    simpa [hqp] using hmem
  have hprod : f.prod (fun q k => q ^ (k - 1) * (q - 1)) ∣
      n.factorization.prod (fun q k => q ^ (k - 1) * (q - 1)) := by
    apply Finsupp.prod_dvd_prod_of_subset_of_dvd hsupp
    intro q hq
    have hqp : q = p := by
      simpa [f] using hq
    subst q
    simp only [f, Finsupp.single_eq_same]
    apply Nat.mul_dvd_mul_right
    rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt]
    exact Nat.sub_le_sub_right hk 1
  rw [Nat.totient_eq_prod_factorization hn] at ⊢
  have hterm : p ∣ f.prod (fun q k => q ^ (k - 1) * (q - 1)) := by
    simp only [f, Finsupp.prod]
    norm_num
  exact dvd_trans hterm hprod

lemma prime_dvd_odd_part {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ n) : p ∣ ordCompl[2] n := by
  apply Nat.dvd_ordCompl_of_dvd_not_dvd hpn
  intro h2
  have hodd : Odd p := hp.odd_of_ne_two hp2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

lemma prime_dvd_totient_of_odd_part_squarefull {n p : ℕ} (hn : n ≠ 0)
    (hlarge : 2 < n) (hsq : OddPartSquarefull n) (hp : p.Prime) (hpn : p ∣ n) : p ∣ n.totient := by
  by_cases hp2 : p = 2
  · subst p
    exact (even_iff_two_dvd.mp (Nat.totient_even hlarge))
  · have hop : p ∣ ordCompl[2] n := prime_dvd_odd_part hp hp2 hpn
    have hpowop := hsq p hp hop
    exact prime_dvd_totient_of_sq_dvd hn hp (dvd_trans hpowop (Nat.ordCompl_dvd n 2))

lemma coprime_of_coprime_sub {n t a : ℕ}
    (hprime : ∀ p, p.Prime → p ∣ n → p ∣ t)
    (hcop : (n - t).Coprime a) : n.Coprime a := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpa
  have hpt : p ∣ t := hprime p hp hpn
  have hpm : p ∣ n - t := Nat.dvd_sub hpn hpt
  have hp1 : p = 1 := Nat.eq_one_of_dvd_coprimes hcop hpm hpa
  exact hp.ne_one hp1

theorem theorem2 {n : ℕ} (hlarge : 2 < n) (hsq : OddPartSquarefull n) :
    n.totient > (n - n.totient).totient := by
  have hn : n ≠ 0 := by omega
  have hprime : ∀ p, p.Prime → p ∣ n → p ∣ n.totient := by
    intro p hp hpn
    exact prime_dvd_totient_of_odd_part_squarefull hn hlarge hsq hp hpn
  have hphi_pos : 0 < n.totient := Nat.totient_pos.mpr (by omega)
  have hphi_ne_one : n.totient ≠ 1 := by
    intro h
    have hcases := (Nat.totient_eq_one_iff.mp h).resolve_left
      (by omega : n ≠ 1)
    exact (by omega : n ≠ 2) hcases
  have hphi_gt_one : 1 < n.totient := by omega
  have hphi_le : n.totient ≤ n := Nat.totient_le n
  have hsub_le : n - n.totient ≤ n - 1 := by omega
  let S : Finset ℕ := (Finset.range (n - n.totient)).filter
    (fun a => (n - n.totient).Coprime a)
  let T : Finset ℕ := (Finset.range n).filter (fun a => n.Coprime a)
  have hST : S ⊂ T := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro a ha
      have ha' := (Finset.mem_filter.mp ha)
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ha'.1) (Nat.sub_le n n.totient))
      · exact coprime_of_coprime_sub hprime ha'.2
    · intro hEq
      have hnmem : n - 1 ∈ T := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_range.mpr (Nat.sub_lt (by omega) (by omega))
        · rw [Nat.coprime_self_sub_right (by omega : 1 ≤ n)]
          simp
      have hnotmem : n - 1 ∉ S := by
        simp only [S, Finset.mem_filter, Finset.mem_range]
        omega
      exact hnotmem (hEq ▸ hnmem)
  have hcard : S.card < T.card := Finset.card_lt_card hST
  calc
    n.totient = T.card := by simp [T, Nat.totient_eq_card_coprime]
    _ > S.card := hcard
    _ = (n - n.totient).totient := by
      symm
      rw [Nat.totient_eq_card_coprime]

end ErdosGLW

/-! ## Theorem 3（补上原文遗漏的 m > 1 条件）

原文的“奇正整数”允许 m = 1，但此时 k = 1 给出 2 ≥ 4 的假命题。
下面显式加入 `1 < m`，保留 squarefree 和所有正整数 k 的完整结论。
-/

namespace ErdosGLW

/-- Theorem 3 中的 n = 2^k · 3 · m。 -/
def n3 (m k : ℕ) : ℕ := 2 ^ k * 3 * m


/-- 公式 (15)：只需奇性、互素性和 k > 0，不需要 squarefree 假设。 -/
lemma totient_special_product {m k : ℕ} (hm : Odd m) (hc : Nat.Coprime 3 m)
    (hk : 0 < k) :
    (2 ^ k * 3 * m).totient = 2 ^ k * m.totient := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have h2m : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
  have h2 : Nat.Coprime 2 (3 * m) :=
    (by decide : Nat.Coprime 2 3).mul_right h2m
  rw [mul_assoc, Nat.totient_mul (h2.pow_left _), Nat.totient_mul hc,
    Nat.totient_prime_pow_succ Nat.prime_two]
  have h3 : Nat.totient 3 = 2 := by decide
  rw [h3]
  simp only [Nat.add_one_sub_one, mul_one, pow_succ]
  ring

/-- 若素数 q 的平方整除 m，则 q 整除 3m - φ(m)，导致大小矛盾。 -/
lemma squarefree_of_prime_condition {m : ℕ} (hm : 1 < m)
    (hp : Nat.Prime (3 * m - m.totient)) : Squarefree m := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro q hq hsq
  have hqm : q ∣ m := dvd_trans (dvd_mul_right q q) hsq
  have hqphi : q ∣ m.totient := by
    have hd := Nat.totient_dvd_of_dvd hsq
    have he : (q * q).totient = q * (q - 1) := by
      simpa [pow_two] using Nat.totient_prime_pow_succ hq 1
    rw [he] at hd
    exact dvd_trans (dvd_mul_right q (q - 1)) hd
  have hqp : q ∣ 3 * m - m.totient :=
    Nat.dvd_sub (dvd_mul_of_dvd_right hqm 3) hqphi
  have heq : 3 * m - m.totient = q := (hp.dvd_iff_eq hq.ne_one).mp hqp
  have hle := Nat.totient_le m
  have hqle := Nat.le_of_dvd (by omega : 0 < m) hqm
  omega

/-- 公式 (16)：先得到 n - φ(n) = 2^k p，再用互素乘法公式。 -/
lemma totient_sub_value {m k : ℕ} (hm : 1 < m) (hodd : Odd m)
    (hc : Nat.Coprime 3 m) (hk : 0 < k)
    (hp : Nat.Prime (3 * m - m.totient)) :
    (2 ^ k * 3 * m - (2 ^ k * 3 * m).totient).totient =
      2 ^ (k - 1) * ((3 * m - m.totient) - 1) := by
  have hp2 : 3 * m - m.totient ≠ 2 := by
    have := Nat.totient_le m
    omega
  have hcop : Nat.Coprime 2 (3 * m - m.totient) :=
    Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)
  rw [totient_special_product hodd hc hk, mul_assoc, ← Nat.mul_sub_left_distrib,
    Nat.totient_mul (hcop.pow_left k), Nat.totient_prime hp,
    Nat.totient_prime_pow Nat.prime_two hk]
  simp

/-- 将两个欧拉函数公式代入，再由 φ(m) < m 完成不等式。 -/
lemma theorem3_inequality {m k : ℕ} (hm : 1 < m) (hodd : Odd m)
    (hc : Nat.Coprime 3 m) (hk : 0 < k)
    (hp : Nat.Prime (3 * m - m.totient)) :
    (2 ^ k * 3 * m).totient + 2 ^ k ≤
      (2 ^ k * 3 * m - (2 ^ k * 3 * m).totient).totient := by
  rw [totient_sub_value hm hodd hc hk hp, totient_special_product hodd hc hk]
  have hlt := Nat.totient_lt m hm
  have hbound : 2 * (m.totient + 1) ≤ (3 * m - m.totient) - 1 := by omega
  have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  calc
    2 ^ k * m.totient + 2 ^ k = 2 ^ (k - 1) * (2 * (m.totient + 1)) := by
      rw [hpow]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ hbound


/-- GLW Theorem 3 的修正版；没有把 squarefree 当作额外假设。 -/
theorem theorem3 {m : ℕ} (hm_gt_one : 1 < m) (hm_odd : Odd m)
    (hm_coprime : Nat.Coprime 3 m)
    (hp : Nat.Prime (3 * m - Nat.totient m)) :
    Squarefree m ∧
      ∀ k : ℕ, 0 < k →
        Nat.totient (n3 m k - Nat.totient (n3 m k)) ≥
          Nat.totient (n3 m k) + 2 ^ k := by
  refine ⟨squarefree_of_prime_condition hm_gt_one hp, ?_⟩
  intro k hk
  exact theorem3_inequality hm_gt_one hm_odd hm_coprime hk hp

end ErdosGLW
