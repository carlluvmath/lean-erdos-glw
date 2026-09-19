import ErdosGLW.Theorem1PrimeProducts

namespace ErdosGLW

/-- The positive logarithmic weight attached to an odd prime. -/
noncomputable def theorem1PrimeLogWeight (p : ℕ) : ℝ :=
  -Real.log (1 - (p : ℝ)⁻¹)

/-- The weighted finite prime sum on the right side of formula (6). -/
noncomputable def theorem1PrimeLogSum (x s : ℕ) : ℝ :=
  ∑ p ∈ theorem1OddPrimes x,
    (((x : ℝ) / (2 ^ s * p) + 1) / 2) * theorem1PrimeLogWeight p

noncomputable def theorem1S0 (x : ℕ) : ℝ :=
  ∑ p ∈ theorem1OddPrimes x, theorem1PrimeLogWeight p / p

noncomputable def theorem1S1 (x : ℕ) : ℝ :=
  ∑ p ∈ theorem1OddPrimes x, theorem1PrimeLogWeight p

lemma theorem1PrimeLogSum_eq (x s : ℕ) :
    theorem1PrimeLogSum x s =
      (x : ℝ) / (2 * 2 ^ s) * theorem1S0 x + (1 : ℝ) / 2 * theorem1S1 x := by
  unfold theorem1PrimeLogSum theorem1S0 theorem1S1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.1.ne_zero
  have hpow0 : (2 : ℝ) ^ s ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

private lemma oddPrimeFactor_pos_of_mem {x p : ℕ}
    (hp : p ∈ theorem1OddPrimes x) : 0 < (1 - (p : ℝ)⁻¹) := by
  have hpPrime := (Finset.mem_filter.mp hp).2.1
  have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hinv : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ (by exact_mod_cast hpPrime.pos)).2 hpgt
  linarith

private lemma log_prime_product (x s : ℕ) :
    Real.log (∏ p ∈ theorem1OddPrimes x,
      (1 - (p : ℝ)⁻¹) ^ (((x : ℝ) / (2 ^ s * p) + 1) / 2)) =
      ∑ p ∈ theorem1OddPrimes x,
        (((x : ℝ) / (2 ^ s * p) + 1) / 2) *
          Real.log (1 - (p : ℝ)⁻¹) := by
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Real.log_rpow]
    exact oddPrimeFactor_pos_of_mem hp
  · intro p hp
    exact (Real.rpow_pos_of_pos (oddPrimeFactor_pos_of_mem hp) _).ne'

private lemma prime_product_pos (x s : ℕ) :
    0 < ∏ p ∈ theorem1OddPrimes x,
      (1 - (p : ℝ)⁻¹) ^ (((x : ℝ) / (2 ^ s * p) + 1) / 2) := by
  apply Finset.prod_pos
  intro p hp
  exact Real.rpow_pos_of_pos (oddPrimeFactor_pos_of_mem hp) _

/-- Formula (6) for `s > 0`. -/
lemma theorem1_log_bound_pos (x s : ℕ) :
    ((theorem1BadOddInputs x s).card : ℝ) * Real.log ((3 : ℝ) / 2) ≤
      theorem1PrimeLogSum x s := by
  have hprod := (theorem1_prime_product_lower_bound x s).trans
    (theorem1T_le_two_thirds_pow x s)
  have hlog := Real.log_le_log (prime_product_pos x s) hprod
  rw [log_prime_product, Real.log_pow] at hlog
  have hneg := neg_le_neg hlog
  unfold theorem1PrimeLogSum theorem1PrimeLogWeight
  have hbase : -Real.log ((2 : ℝ) / 3) = Real.log ((3 : ℝ) / 2) := by
    rw [← Real.log_inv]
    norm_num
  calc
    ((theorem1BadOddInputs x s).card : ℝ) * Real.log ((3 : ℝ) / 2) =
        -(((theorem1BadOddInputs x s).card : ℝ) * Real.log ((2 : ℝ) / 3)) := by
      rw [← hbase]
      ring
    _ ≤ -∑ p ∈ theorem1OddPrimes x,
        (((x : ℝ) / (2 ^ s * p) + 1) / 2) * Real.log (1 - (p : ℝ)⁻¹) := hneg
    _ = ∑ p ∈ theorem1OddPrimes x,
        (((x : ℝ) / (2 ^ s * p) + 1) / 2) *
          -Real.log (1 - (p : ℝ)⁻¹) := by
      rw [← Finset.sum_neg_distrib]
      congr 1
      funext p
      ring

/-- Formula (6) for the odd stratum `s = 0`. -/
lemma theorem1_log_bound_zero (x : ℕ) :
    ((theorem1B0 x).card : ℝ) * Real.log 2 ≤ theorem1PrimeLogSum x 0 := by
  have hprod := (theorem1_prime_product_lower_bound x 0).trans
    (theorem1T_zero_le_half_pow x)
  have hlog := Real.log_le_log (prime_product_pos x 0) hprod
  rw [log_prime_product, Real.log_pow] at hlog
  have hneg := neg_le_neg hlog
  unfold theorem1PrimeLogSum theorem1PrimeLogWeight
  have hbase : -Real.log ((1 : ℝ) / 2) = Real.log 2 := by
    rw [← Real.log_inv]
    norm_num
  calc
    ((theorem1B0 x).card : ℝ) * Real.log 2 =
        -(((theorem1B0 x).card : ℝ) * Real.log ((1 : ℝ) / 2)) := by
      rw [← hbase]
      ring
    _ ≤ -∑ p ∈ theorem1OddPrimes x,
        (((x : ℝ) / (2 ^ 0 * p) + 1) / 2) * Real.log (1 - (p : ℝ)⁻¹) := hneg
    _ = ∑ p ∈ theorem1OddPrimes x,
        (((x : ℝ) / (2 ^ 0 * p) + 1) / 2) *
          -Real.log (1 - (p : ℝ)⁻¹) := by
      rw [← Finset.sum_neg_distrib]
      congr 1
      funext p
      ring

/-- Formula (6), split into the two prime sums used in the paper. -/
lemma theorem1_log_bound_pos_split (x s : ℕ) :
    ((theorem1BadOddInputs x s).card : ℝ) * Real.log ((3 : ℝ) / 2) ≤
      (x : ℝ) / (2 * 2 ^ s) * theorem1S0 x + (1 : ℝ) / 2 * theorem1S1 x := by
  rw [← theorem1PrimeLogSum_eq]
  exact theorem1_log_bound_pos x s

/-- Formula (6) for `s = 0`, split into `S₀(x)` and `S₁(x)`. -/
lemma theorem1_log_bound_zero_split (x : ℕ) :
    ((theorem1B0 x).card : ℝ) * Real.log 2 ≤
      (x : ℝ) / 2 * theorem1S0 x + (1 : ℝ) / 2 * theorem1S1 x := by
  have h := theorem1_log_bound_zero x
  rw [theorem1PrimeLogSum_eq] at h
  norm_num at h ⊢
  exact h

end ErdosGLW
