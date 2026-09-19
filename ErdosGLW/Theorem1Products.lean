import ErdosGLW.Theorem1TwoAdic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ErdosGLW

/-- Odd inputs `m` occurring in the `s`-th two-adic stratum below `x`. -/
def theorem1OddInputs (x s : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun m => Odd m ∧ 2 ^ s * m < x

/-- Inputs in the `s > 0` exceptional stratum. -/
def theorem1BadOddInputs (x s : ℕ) : Finset ℕ :=
  (theorem1OddInputs x s).filter fun m => 3 * m.totient ≤ 2 * m

lemma theorem1Bs_eq_image_badOddInputs (x s : ℕ) :
    theorem1Bs x s =
      (theorem1BadOddInputs x s).image (fun m => 2 ^ s * m) := by
  classical
  ext n
  constructor
  · intro hn
    rcases (mem_theorem1Bs_iff.mp hn) with ⟨hnx, m, rfl, hm, hbad⟩
    apply Finset.mem_image.mpr
    refine ⟨m, ?_, rfl⟩
    have hmle : m ≤ 2 ^ s * m := by
      exact Nat.le_mul_of_pos_left m (by positivity)
    have hmx : m < x := hmle.trans_lt hnx
    simp [theorem1BadOddInputs, theorem1OddInputs, hm, hbad, hnx, hmx]
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    have hm' := Finset.mem_filter.mp hm
    have hinput := Finset.mem_filter.mp hm'.1
    exact (mem_theorem1Bs_iff).2
      ⟨hinput.2.2, m, rfl, hinput.2.1, hm'.2⟩

lemma theorem1Bs_card_eq_badOddInputs_card (x s : ℕ) :
    (theorem1Bs x s).card = (theorem1BadOddInputs x s).card := by
  classical
  rw [theorem1Bs_eq_image_badOddInputs]
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ s) hab

/-- The totient ratio on a positive integer, as a real number. -/
noncomputable def totientRatio (m : ℕ) : ℝ :=
  (m.totient : ℝ) / m

/-- The finite product used in formula (4), written over the odd inputs `m`. -/
noncomputable def theorem1T (x s : ℕ) : ℝ :=
  ∏ m ∈ theorem1OddInputs x s, totientRatio m

lemma totientRatio_nonneg (m : ℕ) : 0 ≤ totientRatio m := by
  unfold totientRatio
  positivity

lemma totientRatio_le_one (m : ℕ) : totientRatio m ≤ 1 := by
  unfold totientRatio
  by_cases hm : m = 0
  · simp [hm]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))).2
      (Nat.cast_le.mpr (Nat.totient_le m))

lemma totientRatio_eq_prod_primeFactors {m : ℕ} (hm : m ≠ 0) :
    totientRatio m =
      ∏ p ∈ m.primeFactors, (1 - ((p : ℝ)⁻¹)) := by
  have hq := Nat.totient_eq_mul_prod_factors m
  have hq' : ((m.totient : ℚ) / m) =
      ∏ p ∈ m.primeFactors, (1 - ((p : ℚ)⁻¹)) := by
    rw [hq, mul_div_cancel_left₀]
    exact_mod_cast hm
  have hr := congrArg (fun q : ℚ => (q : ℝ)) hq'
  push_cast at hr
  unfold totientRatio
  exact hr

lemma totientRatio_le_two_thirds_of_bad {x s m : ℕ}
    (hm : m ∈ theorem1BadOddInputs x s) :
    totientRatio m ≤ (2 : ℝ) / 3 := by
  have hbad := (Finset.mem_filter.mp hm).2
  have hmOdd := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2.1
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hmOdd.pos
  have hbad' : 3 * (m.totient : ℝ) ≤ 2 * m := by exact_mod_cast hbad
  unfold totientRatio
  rw [div_le_iff₀ hmpos]
  nlinarith

/-- Formula (4) for the positive two-adic strata, in the equivalent form
`T ≤ (2/3)^b`. -/
lemma theorem1T_le_two_thirds_pow (x s : ℕ) :
    theorem1T x s ≤
      ((2 : ℝ) / 3) ^ (theorem1BadOddInputs x s).card := by
  classical
  unfold theorem1T
  calc
    (∏ m ∈ theorem1OddInputs x s, totientRatio m) ≤
        ∏ m ∈ theorem1OddInputs x s,
          if m ∈ theorem1BadOddInputs x s then (2 : ℝ) / 3 else 1 := by
      apply Finset.prod_le_prod₀
      · intro m hm
        exact totientRatio_nonneg m
      · intro m hm
        split_ifs with hbad
        · exact totientRatio_le_two_thirds_of_bad hbad
        · exact totientRatio_le_one m
    _ = ((2 : ℝ) / 3) ^ (theorem1BadOddInputs x s).card := by
      have hfilter :
          (theorem1OddInputs x s).filter
              (fun m => m ∈ theorem1BadOddInputs x s) =
            theorem1BadOddInputs x s := by
        ext m
        simp [theorem1BadOddInputs]
      rw [Finset.prod_ite, hfilter]
      simp
      rw [div_pow]

lemma totientRatio_le_half_of_mem_B0 {x m : ℕ} (hm : m ∈ theorem1B0 x) :
    totientRatio m ≤ (1 : ℝ) / 2 := by
  have hm' := mem_theorem1B0_iff.mp hm
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm'.2.1.pos
  have hbad : 2 * m.totient ≤ m := by omega
  have hbad' : 2 * (m.totient : ℝ) ≤ m := by exact_mod_cast hbad
  unfold totientRatio
  rw [div_le_iff₀ hmpos]
  nlinarith

/-- Formula (4) for the odd stratum, in the equivalent form
`T(x,0) ≤ (1/2)^|B₀|`. -/
lemma theorem1T_zero_le_half_pow (x : ℕ) :
    theorem1T x 0 ≤ ((1 : ℝ) / 2) ^ (theorem1B0 x).card := by
  classical
  unfold theorem1T
  calc
    (∏ m ∈ theorem1OddInputs x 0, totientRatio m) ≤
        ∏ m ∈ theorem1OddInputs x 0,
          if m ∈ theorem1B0 x then (1 : ℝ) / 2 else 1 := by
      apply Finset.prod_le_prod₀
      · intro m hm
        exact totientRatio_nonneg m
      · intro m hm
        split_ifs with hbad
        · exact totientRatio_le_half_of_mem_B0 hbad
        · exact totientRatio_le_one m
    _ = ((1 : ℝ) / 2) ^ (theorem1B0 x).card := by
      have hfilter :
          (theorem1OddInputs x 0).filter (fun m => m ∈ theorem1B0 x) =
            theorem1B0 x := by
        ext m
        simp [theorem1OddInputs, theorem1B0, and_assoc, and_left_comm]
      rw [Finset.prod_ite, hfilter]
      simp

end ErdosGLW
