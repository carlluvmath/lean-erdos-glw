import ErdosGLW.Theorem1LogBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ErdosGLW

lemma theorem1PrimeLogWeight_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ theorem1PrimeLogWeight p := by
  unfold theorem1PrimeLogWeight
  have hpgt : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hbase0 : 0 < (1 - (p : ℝ)⁻¹) := by
    have hinv : (p : ℝ)⁻¹ < 1 :=
      (inv_lt_one₀ (by exact_mod_cast hp.pos)).2 hpgt
    linarith
  have hbase1 : (1 - (p : ℝ)⁻¹) ≤ 1 :=
    sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg p))
  exact neg_nonneg.mpr (Real.log_nonpos hbase0.le hbase1)

lemma theorem1PrimeLogWeight_le_two_div {p : ℕ} (hp : p.Prime) :
    theorem1PrimeLogWeight p ≤ (2 : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hbase : 0 < (1 - (p : ℝ)⁻¹) := by
    have hinv : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).2 hp1
    linarith
  have hlog := Real.log_le_sub_one_of_pos (x := (1 - (p : ℝ)⁻¹)⁻¹)
    (inv_pos.mpr hbase)
  have hrewrite : theorem1PrimeLogWeight p =
      Real.log ((1 - (p : ℝ)⁻¹)⁻¹) := by
    unfold theorem1PrimeLogWeight
    rw [Real.log_inv]
  rw [hrewrite]
  have hpSub0 : (0 : ℝ) < p - 1 := by linarith
  have heq : (1 - (p : ℝ)⁻¹)⁻¹ - 1 = 1 / (p - 1) := by
    field_simp
    ring
  rw [heq] at hlog
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact hlog.trans ((div_le_div_iff₀ hpSub0 hp0).2 (by nlinarith))

/-- Rewriting the logarithmic prime weight in a form suited to tail bounds. -/
lemma theorem1PrimeLogWeight_eq_log_one_add {p : ℕ} (hp : p.Prime) :
    theorem1PrimeLogWeight p =
      Real.log (1 + 1 / ((p : ℝ) - 1)) := by
  unfold theorem1PrimeLogWeight
  rw [← Real.log_inv]
  congr 1
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  field_simp
  ring

/-- The logarithmic prime weight is at most `1 / (p - 1)`. -/
lemma theorem1PrimeLogWeight_le_inv_sub_one {p : ℕ} (hp : p.Prime) :
    theorem1PrimeLogWeight p ≤ 1 / ((p : ℝ) - 1) := by
  rw [theorem1PrimeLogWeight_eq_log_one_add hp]
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast hp.one_lt
  have hden : 0 < (p : ℝ) - 1 := sub_pos.mpr hp1
  have hpos : 0 < 1 + 1 / ((p : ℝ) - 1) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith

/-- Dividing the weight by its prime gives the telescoping majorant. -/
lemma theorem1PrimeLogWeight_div_le_reciprocal {p : ℕ} (hp : p.Prime) :
    theorem1PrimeLogWeight p / p ≤
      1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  calc
    theorem1PrimeLogWeight p / p ≤
        (1 / ((p : ℝ) - 1)) / p :=
      div_le_div_of_nonneg_right (theorem1PrimeLogWeight_le_inv_sub_one hp) hp0
    _ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hpm1 : (p : ℝ) - 1 ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
      field_simp

/-- A rational upper certificate for `theorem1PrimeLogWeight p / p`, obtained
from the first `N` terms of the atanh expansion of the logarithm. -/
noncomputable def theorem1WeightUpper (p N : ℕ) : ℝ :=
  let r : ℝ := 1 / (2 * p - 1)
  (2 * ((∑ i ∈ Finset.range N, r ^ (2 * i + 1) / (2 * i + 1)) +
    r ^ (2 * N + 1) / (1 - r ^ 2))) / p

lemma theorem1PrimeLogWeight_div_le_upper {p N : ℕ} (hp : p.Prime) :
    theorem1PrimeLogWeight p / p ≤ theorem1WeightUpper p N := by
  let r : ℝ := 1 / (2 * p - 1)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg zero_le_one (by linarith)
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one]
    · linarith
    · linarith
  have hlog := Real.log_div_le_sum_range_add hr0 hr1 N
  have hratio : ((1 + r) / (1 - r)) = 1 + 1 / ((p : ℝ) - 1) := by
    have hd1 : 2 * (p : ℝ) - 1 ≠ 0 := by linarith
    have hd2 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hplus : 1 + r = (2 * (p : ℝ)) / (2 * p - 1) := by
      dsimp [r]
      field_simp [hd1]
      ring
    have hminus : 1 - r = (2 * ((p : ℝ) - 1)) / (2 * p - 1) := by
      dsimp [r]
      field_simp [hd1]
      ring
    rw [hplus, hminus]
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    field_simp [hd1, hd2, htwo]
    ring
  rw [hratio, ← theorem1PrimeLogWeight_eq_log_one_add hp] at hlog
  unfold theorem1WeightUpper
  dsimp only
  exact (div_le_div_iff₀ hp0 hp0).2 (by nlinarith)

private def theorem1PrimesBelow501 : Finset ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
    71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
    151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
    233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
    317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
    419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499].toFinset

set_option maxRecDepth 20000 in
private lemma theorem1OddPrimes_501 :
    theorem1OddPrimes 501 = theorem1PrimesBelow501 := by
  decide

set_option maxHeartbeats 2000000 in
private lemma theorem1WeightUpper_sum_lt :
    (∑ p ∈ theorem1OddPrimes 501, theorem1WeightUpper p 3) < (467 : ℝ) / 2000 := by
  rw [theorem1OddPrimes_501]
  norm_num [theorem1PrimesBelow501, theorem1WeightUpper]

def theorem1PrimeTail (x : ℕ) : Finset ℕ :=
  (theorem1OddPrimes x).filter fun p => 501 ≤ p

private lemma theorem1PrimeLogWeight_div_tail_bound {p : ℕ}
    (hp : p.Prime) (_hp501 : 501 ≤ p) :
    theorem1PrimeLogWeight p / p ≤
      3 / (2 * ((p : ℝ) ^ 2 - 1)) := by
  refine (theorem1PrimeLogWeight_div_le_reciprocal hp).trans ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hleft : 0 < (p : ℝ) * (p - 1) := mul_pos hp0 (sub_pos.mpr hp1)
  have hright : 0 < 2 * ((p : ℝ) ^ 2 - 1) := by nlinarith
  rw [div_le_div_iff₀ hleft hright]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  nlinarith [sq_nonneg ((p : ℝ) - 2)]

private lemma odd_tail_reconstruct {p : ℕ} (hp501 : 501 ≤ p) (hpodd : Odd p) :
    501 + 2 * ((p - 501) / 2) = p := by
  obtain ⟨k, hk⟩ := hpodd
  omega

private lemma theorem1TailSum_le_range (x : ℕ) :
    (∑ p ∈ theorem1PrimeTail x, 3 / (2 * ((p : ℝ) ^ 2 - 1))) ≤
      ∑ k ∈ Finset.range x,
        3 / (2 * (((501 + 2 * k : ℕ) : ℝ) ^ 2 - 1)) := by
  classical
  apply Finset.sum_le_sum_of_injOn (fun p => (p - 501) / 2)
  · intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have haOdd : Odd a :=
      (Finset.mem_filter.mp ha'.1).2.1.odd_of_ne_two
        (Finset.mem_filter.mp ha'.1).2.2
    have hbOdd : Odd b :=
      (Finset.mem_filter.mp hb'.1).2.1.odd_of_ne_two
        (Finset.mem_filter.mp hb'.1).2.2
    rw [← odd_tail_reconstruct ha'.2 haOdd,
      ← odd_tail_reconstruct hb'.2 hbOdd]
    exact congrArg (fun q => 501 + 2 * q) hab
  · intro k hk
    rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
    apply Finset.mem_range.mpr
    have hp' := Finset.mem_filter.mp hp
    have hpx := Finset.mem_range.mp (Finset.mem_filter.mp hp'.1).1
    omega
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpOdd : Odd p :=
      (Finset.mem_filter.mp hp'.1).2.1.odd_of_ne_two
        (Finset.mem_filter.mp hp'.1).2.2
    rw [odd_tail_reconstruct hp'.2 hpOdd]
  · intro k hk hnot
    have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
    have hden : 0 < (((501 + 2 * k : ℕ) : ℝ) ^ 2 - 1) := by
      push_cast
      nlinarith [sq_nonneg (501 + 2 * (k : ℝ))]
    positivity

private lemma theorem1TelescopingSum (n : ℕ) :
    (∑ k ∈ Finset.range n,
      3 / (2 * (((501 + 2 * k : ℕ) : ℝ) ^ 2 - 1))) =
        (3 : ℝ) / 4 * (1 / 500 - 1 / (500 + 2 * n)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      have h₁ : (500 + 2 * (n : ℝ)) ≠ 0 := by positivity
      have h₂ : (502 + 2 * (n : ℝ)) ≠ 0 := by positivity
      have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
      have h₃ : ((501 + 2 * (n : ℝ)) ^ 2 - 1) ≠ 0 := by
        nlinarith [sq_nonneg (501 + 2 * (n : ℝ))]
      field_simp
      ring

private lemma theorem1PrimeTail_bound (x : ℕ) :
    (∑ p ∈ theorem1PrimeTail x, theorem1PrimeLogWeight p / p) ≤
      (3 : ℝ) / 2000 := by
  calc
    (∑ p ∈ theorem1PrimeTail x, theorem1PrimeLogWeight p / p) ≤
        ∑ p ∈ theorem1PrimeTail x, 3 / (2 * ((p : ℝ) ^ 2 - 1)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact theorem1PrimeLogWeight_div_tail_bound
        (Finset.mem_filter.mp hp'.1).2.1 hp'.2
    _ ≤ ∑ k ∈ Finset.range x,
        3 / (2 * (((501 + 2 * k : ℕ) : ℝ) ^ 2 - 1)) := theorem1TailSum_le_range x
    _ = (3 : ℝ) / 4 * (1 / 500 - 1 / (500 + 2 * x)) := theorem1TelescopingSum x
    _ ≤ (3 : ℝ) / 2000 := by
      have hnonneg : 0 ≤ (1 : ℝ) / (500 + 2 * x) := by positivity
      nlinarith

def theorem1PrimeHead (x : ℕ) : Finset ℕ :=
  (theorem1OddPrimes x).filter fun p => p < 501

private lemma theorem1WeightUpper_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ theorem1WeightUpper p 3 := by
  unfold theorem1WeightUpper
  dsimp only
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : (0 : ℝ) < 2 * p - 1 := by linarith
  have hr : (0 : ℝ) ≤ 1 / (2 * p - 1) := by positivity
  have hrlt : (1 / (2 * (p : ℝ) - 1)) ^ 2 < 1 := by
    have hp1 : (1 : ℝ) < 2 * p - 1 := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    have hfrac : 1 / (2 * (p : ℝ) - 1) < 1 := by
      rw [div_lt_one hden]
      exact hp1
    nlinarith [sq_nonneg (1 / (2 * (p : ℝ) - 1))]
  positivity

private lemma theorem1PrimeHead_bound (x : ℕ) :
    (∑ p ∈ theorem1PrimeHead x, theorem1PrimeLogWeight p / p) <
      (467 : ℝ) / 2000 := by
  calc
    (∑ p ∈ theorem1PrimeHead x, theorem1PrimeLogWeight p / p) ≤
        ∑ p ∈ theorem1PrimeHead x, theorem1WeightUpper p 3 := by
      apply Finset.sum_le_sum
      intro p hp
      exact theorem1PrimeLogWeight_div_le_upper
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    _ ≤ ∑ p ∈ theorem1OddPrimes 501, theorem1WeightUpper p 3 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hpPrime := (Finset.mem_filter.mp hp'.1).2.1
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hp'.2, hpPrime,
            (Finset.mem_filter.mp hp'.1).2.2⟩
      · intro p hp hnot
        exact theorem1WeightUpper_nonneg (Finset.mem_filter.mp hp).2.1
    _ < (467 : ℝ) / 2000 := theorem1WeightUpper_sum_lt

lemma theorem1S0_lt (x : ℕ) : theorem1S0 x < (47 : ℝ) / 200 := by
  have hpartition : theorem1S0 x =
      (∑ p ∈ theorem1PrimeHead x, theorem1PrimeLogWeight p / p) +
      ∑ p ∈ theorem1PrimeTail x, theorem1PrimeLogWeight p / p := by
    unfold theorem1S0 theorem1PrimeHead theorem1PrimeTail
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := theorem1OddPrimes x) (p := fun p => p < 501)]
    congr 2
    ext p
    simp
  rw [hpartition]
  nlinarith [theorem1PrimeHead_bound x, theorem1PrimeTail_bound x]

private lemma sum_range_inv_cast_eq_harmonic_pred (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℝ)⁻¹) = (harmonic (n - 1) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hn : n = 0
      · simp [hn]
      rw [Finset.sum_range_succ, ih, Nat.succ_sub_one]
      have hnform : n - 1 + 1 = n := Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr hn)
      conv_rhs => rw [← hnform, harmonic_succ]
      push_cast
      have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast hnform.symm
      rw [hcast]

lemma theorem1S1_le_two_harmonic (x : ℕ) :
    theorem1S1 x ≤ 2 * (harmonic x : ℝ) := by
  calc
    theorem1S1 x ≤ ∑ p ∈ theorem1OddPrimes x, (2 : ℝ) / p := by
      unfold theorem1S1
      apply Finset.sum_le_sum
      intro p hp
      exact theorem1PrimeLogWeight_le_two_div (Finset.mem_filter.mp hp).2.1
    _ ≤ ∑ p ∈ Finset.range x, (2 : ℝ) / p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (Finset.mem_filter.mp hp).1
      · intro p hp hnot
        positivity
    _ = 2 * (harmonic (x - 1) : ℝ) := by
      simp only [div_eq_mul_inv]
      rw [← Finset.mul_sum]
      rw [sum_range_inv_cast_eq_harmonic_pred]
    _ ≤ 2 * (harmonic x : ℝ) := by
      gcongr
      have hmono : harmonic (x - 1) ≤ harmonic x := by
        unfold harmonic
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (Nat.sub_le x 1)
        · intro i hi hnot
          positivity
      exact_mod_cast hmono

lemma theorem1S1_le_two_one_add_log (x : ℕ) :
    theorem1S1 x ≤ 2 * (1 + Real.log x) := by
  exact (theorem1S1_le_two_harmonic x).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast harmonic_le_one_add_log x) (by norm_num))

end ErdosGLW
