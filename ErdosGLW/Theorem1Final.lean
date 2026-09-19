import ErdosGLW.Theorem1PrimeBounds
import ErdosGLW.Theorem1TwoAdic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ErdosGLW

open Filter Finset

def theorem1Strata (x : ℕ) : Finset ℕ :=
  Finset.Icc 1 (Nat.log 2 x)

noncomputable def theorem1BadCover (x : ℕ) : Finset ℕ :=
  insert 0 (theorem1B0 x ∪ (theorem1Strata x).biUnion (theorem1Bs x))

lemma theorem1Exceptional_subset_badCover (x : ℕ) :
    theorem1Exceptional x ⊆ theorem1BadCover x := by
  intro n hn
  rcases theorem1Exceptional_covered_log hn with hzero | hrest
  · subst n
    simp [theorem1BadCover]
  · rcases hrest with hB0 | ⟨s, hs, hBs⟩
    · simp [theorem1BadCover, hB0]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨s, hs, hBs⟩

lemma theorem1Exceptional_card_le_strata (x : ℕ) :
    (theorem1Exceptional x).card ≤
      1 + (theorem1B0 x).card +
        ∑ s ∈ theorem1Strata x, (theorem1Bs x s).card := by
  have hsubset := Finset.card_le_card (theorem1Exceptional_subset_badCover x)
  have hi := Finset.card_insert_le 0
    (theorem1B0 x ∪ (theorem1Strata x).biUnion (theorem1Bs x))
  have hu := Finset.card_union_le (theorem1B0 x)
    ((theorem1Strata x).biUnion (theorem1Bs x))
  have hb := Finset.card_biUnion_le
    (s := theorem1Strata x) (t := theorem1Bs x)
  simp only [theorem1BadCover] at hsubset
  omega

lemma theorem1B0_real_bound (x : ℕ) :
    ((theorem1B0 x).card : ℝ) ≤
      ((x : ℝ) / 2 * ((47 : ℝ) / 200) + (1 : ℝ) / 2 * theorem1S1 x) /
        Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlog).2
  refine (theorem1_log_bound_zero_split x).trans ?_
  have hx0 : 0 ≤ (x : ℝ) / 2 := by positivity
  have hS0 := (theorem1S0_lt x).le
  gcongr

lemma theorem1Bs_real_bound (x s : ℕ) :
    ((theorem1Bs x s).card : ℝ) ≤
      ((x : ℝ) / (2 * 2 ^ s) * ((47 : ℝ) / 200) +
        (1 : ℝ) / 2 * theorem1S1 x) / Real.log ((3 : ℝ) / 2) := by
  have hlog : 0 < Real.log ((3 : ℝ) / 2) := Real.log_pos (by norm_num)
  rw [theorem1Bs_card_eq_badOddInputs_card]
  apply (le_div_iff₀ hlog).2
  refine (theorem1_log_bound_pos_split x s).trans ?_
  have hx0 : 0 ≤ (x : ℝ) / (2 * 2 ^ s) := by positivity
  have hS0 := (theorem1S0_lt x).le
  gcongr

private lemma theorem1_geometric_strata_le_one (x : ℕ) :
    (∑ s ∈ theorem1Strata x, ((2 : ℝ) ^ s)⁻¹) ≤ 1 := by
  let L := Nat.log 2 x
  have hIcc : theorem1Strata x = Finset.Ico 1 (L + 1) := by
    ext s
    simp [theorem1Strata, L]
  rw [hIcc]
  have hgeom := geom_sum_Ico' (x := (2 : ℝ)⁻¹) (by norm_num) (m := 1)
    (n := L + 1) (by omega)
  simp only [inv_pow] at hgeom
  rw [hgeom]
  have hpow : 0 ≤ ((2 : ℝ) ^ (L + 1))⁻¹ := by positivity
  norm_num
  linarith

private lemma theorem1_strata_card_le_log (x : ℕ) :
    (theorem1Strata x).card ≤ Nat.log 2 x := by
  simp [theorem1Strata, Nat.card_Icc]

lemma theorem1Strata_real_bound (x : ℕ) :
    (∑ s ∈ theorem1Strata x, ((theorem1Bs x s).card : ℝ)) ≤
      ((x : ℝ) * ((47 : ℝ) / 200) / 2 +
        (Nat.log 2 x : ℝ) * ((1 : ℝ) / 2 * theorem1S1 x)) /
          Real.log ((3 : ℝ) / 2) := by
  have hlog : 0 < Real.log ((3 : ℝ) / 2) := Real.log_pos (by norm_num)
  calc
    (∑ s ∈ theorem1Strata x, ((theorem1Bs x s).card : ℝ)) ≤
        ∑ s ∈ theorem1Strata x,
          (((x : ℝ) / (2 * 2 ^ s) * ((47 : ℝ) / 200) +
            (1 : ℝ) / 2 * theorem1S1 x) / Real.log ((3 : ℝ) / 2)) := by
      apply Finset.sum_le_sum
      intro s hs
      exact theorem1Bs_real_bound x s
    _ = (((x : ℝ) * ((47 : ℝ) / 200) / 2) *
          (∑ s ∈ theorem1Strata x, ((2 : ℝ) ^ s)⁻¹) +
        ((theorem1Strata x).card : ℝ) * ((1 : ℝ) / 2 * theorem1S1 x)) /
          Real.log ((3 : ℝ) / 2) := by
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      field_simp
    _ ≤ ((x : ℝ) * ((47 : ℝ) / 200) / 2 +
        (Nat.log 2 x : ℝ) * ((1 : ℝ) / 2 * theorem1S1 x)) /
          Real.log ((3 : ℝ) / 2) := by
      apply div_le_div_of_nonneg_right _ hlog.le
      apply add_le_add
      · exact mul_le_of_le_one_right (by positivity) (theorem1_geometric_strata_le_one x)
      · apply mul_le_mul_of_nonneg_right
        · exact_mod_cast theorem1_strata_card_le_log x
        · apply mul_nonneg (by norm_num)
          unfold theorem1S1
          apply Finset.sum_nonneg
          intro p hp
          exact theorem1PrimeLogWeight_nonneg (Finset.mem_filter.mp hp).2.1

/-- Main coefficient in the exceptional-set estimate. -/
noncomputable def theorem1MainConstant : ℝ :=
  (47 / 400) * (1 / Real.log 2 + 1 / Real.log (3 / 2))

/-- Explicit logarithmic remainder, which is o(x). -/
noncomputable def theorem1Error (x : ℕ) : ℝ :=
  1 + (1 + Real.log x) / Real.log 2 +
    (Real.log x / Real.log 2) * (1 + Real.log x) / Real.log (3 / 2)

lemma theorem1Exceptional_real_bound (x : ℕ) :
    ((theorem1Exceptional x).card : ℝ) ≤
      x * theorem1MainConstant + theorem1Error x := by
  have hcard : ((theorem1Exceptional x).card : ℝ) ≤
      1 + ((theorem1B0 x).card : ℝ) +
      ∑ s ∈ theorem1Strata x, ((theorem1Bs x s).card : ℝ) := by
    exact_mod_cast theorem1Exceptional_card_le_strata x
  have hsum := add_le_add (add_le_add_left (theorem1B0_real_bound x) 1)
    (theorem1Strata_real_bound x)
  have hsum' : 1 + ((theorem1B0 x).card : ℝ) +
      ∑ s ∈ theorem1Strata x, ((theorem1Bs x s).card : ℝ) ≤
      1 + ((x : ℝ) / 2 * ((47 : ℝ) / 200) + (1 : ℝ) / 2 * theorem1S1 x) /
        Real.log 2 +
      ((x : ℝ) * ((47 : ℝ) / 200) / 2 +
        (Nat.log 2 x : ℝ) * ((1 : ℝ) / 2 * theorem1S1 x)) /
          Real.log ((3 : ℝ) / 2) := by
    linarith
  refine (hcard.trans hsum').trans ?_
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hs1 : theorem1S1 x / 2 ≤ 1 + Real.log x := by
    linarith [theorem1S1_le_two_one_add_log x]
  have hlog : (Nat.log 2 x : ℝ) ≤ Real.log x / Real.log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb x 2
  have hl0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have hmul : (Nat.log 2 x : ℝ) * (theorem1S1 x / 2) ≤
      (Real.log x / Real.log 2) * (1 + Real.log x) := by
    calc
      _ ≤ (Nat.log 2 x : ℝ) * (1 + Real.log x) :=
        mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hlog (by linarith)
  have hb0 := div_le_div_of_nonneg_right
    (add_le_add_left hs1 ((x : ℝ) / 2 * (47 / 200))) hl2.le
  have hbs := div_le_div_of_nonneg_right
    (add_le_add_left hmul ((x : ℝ) * (47 / 200) / 2)) hl3.le
  unfold theorem1MainConstant theorem1Error
  convert add_le_add (add_le_add_left hb0 1) hbs using 1 <;> ring

lemma theorem1MainConstant_lt : theorem1MainConstant < (46 : ℝ) / 100 := by
  have hl2 : (693 : ℝ) / 1000 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hl3 : (405 : ℝ) / 1000 < Real.log (3 / 2 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_gt_d9, Real.log_two_lt_d9]
  have h2 := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 693 / 1000) hl2
  have h3 := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 405 / 1000) hl3
  unfold theorem1MainConstant
  nlinarith

end ErdosGLW
