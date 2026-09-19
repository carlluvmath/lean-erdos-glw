import ErdosGLW.Theorem1Final
import ErdosGLW.Theorem1Limits
import ErdosGLW.Theorem1Density

/-!
# Theorem 1: the density splice

This file assembles the two analytic ingredients already formalized

* `theorem1Exceptional_real_bound` (in `Theorem1Final`): the exceptional set has
  cardinality at most `x * theorem1MainConstant + theorem1Error x`, where
  `theorem1MainConstant < 46/100` strictly;
* `theorem1DensityError_tendsto` (in `Theorem1Limits`): the error term divided
  by `x` tends to `0`.

into the eventual pointwise lower bound on `theorem1GoodLarge` required by
`theorem1_of_eventual_good_bound`, hence the unconditional `54/100` natural
lower-density conclusion for `theorem1Set`.
-/

namespace ErdosGLW

open Filter Finset
open scoped Topology

/-- The strict gap `46/100 - theorem1MainConstant > 0`. -/
noncomputable def theorem1Gap : ℝ :=
  (46 : ℝ) / 100 - theorem1MainConstant

lemma theorem1Gap_pos : 0 < theorem1Gap := by
  unfold theorem1Gap
  linarith [theorem1MainConstant_lt]

/-- The raw error term divided by `x` tends to zero, derived from the already
formalized `theorem1DensityError_tendsto` using the identity
`theorem1DensityError x = (theorem1Error x + 3) / x`. -/
lemma theorem1Error_div_tendsto_zero :
    Tendsto (fun x : ℕ => theorem1Error x / (x : ℝ)) atTop (𝓝 0) := by
  have h3 : Tendsto (fun x : ℕ => (3 : ℝ) / (x : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h := theorem1DensityError_tendsto.sub h3
  have h0 : Tendsto (fun x : ℕ => theorem1DensityError x - (3 : ℝ) / (x : ℝ)) atTop
      (𝓝 0) := by
    simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with x hx
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  unfold theorem1Error theorem1DensityError
  field_simp [hx']
  ring

/-- Eventually the error term is at most half the gap times `x`. -/
lemma theorem1Error_eventually_le_half_gap :
    ∀ᶠ x : ℕ in atTop, theorem1Error x ≤ (theorem1Gap / 2) * (x : ℝ) := by
  have hhalf : 0 < theorem1Gap / 2 := div_pos theorem1Gap_pos (by norm_num)
  have hlt := (tendsto_order.1 theorem1Error_div_tendsto_zero).2 (theorem1Gap / 2) hhalf
  filter_upwards [hlt, eventually_ne_atTop (0 : ℕ)] with x hltx hx0
  have hxpos : 0 < (x : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hx0)
  have hmul := mul_lt_mul_of_pos_right hltx hxpos
  have hmul' : theorem1Error x < (theorem1Gap / 2) * (x : ℝ) := by
    rwa [div_mul_cancel₀ (theorem1Error x) (ne_of_gt hxpos)] at hmul
  exact le_of_lt hmul'

/-- Eventually the exceptional set has cardinality at most
`(46/100 - theorem1Gap/2) * x`. -/
lemma theorem1Exceptional_eventually_bound :
    ∀ᶠ x : ℕ in atTop,
      ((theorem1Exceptional x).card : ℝ) ≤
        ((46 : ℝ) / 100 - theorem1Gap / 2) * (x : ℝ) := by
  filter_upwards [theorem1Error_eventually_le_half_gap] with x hx
  have hbound := theorem1Exceptional_real_bound x
  have hfinal : x * theorem1MainConstant + (theorem1Gap / 2) * (x : ℝ) ≤
      ((46 : ℝ) / 100 - theorem1Gap / 2) * (x : ℝ) := by
    have hcoe : theorem1MainConstant + theorem1Gap / 2 = (46 : ℝ) / 100 - theorem1Gap / 2 := by
      unfold theorem1Gap
      ring
    calc
      x * theorem1MainConstant + (theorem1Gap / 2) * (x : ℝ)
          = (theorem1MainConstant + theorem1Gap / 2) * (x : ℝ) := by ring
      _ ≤ ((46 : ℝ) / 100 - theorem1Gap / 2) * (x : ℝ) := by
        rw [hcoe]
  nlinarith [hbound, hx, hfinal]

/-- Eventually the good set has cardinality at least
`(54/100 + theorem1Gap/2) * x`. -/
lemma theorem1Good_eventually_lower :
    ∀ᶠ x : ℕ in atTop,
      ((54 : ℝ) / 100 + theorem1Gap / 2) * (x : ℝ) ≤ ((theorem1Good x).card : ℝ) := by
  filter_upwards [theorem1Exceptional_eventually_bound] with x hE
  have hpart := theorem1Good_card_add_exceptional_card x
  have hpart' : ((theorem1Good x).card : ℝ) + ((theorem1Exceptional x).card : ℝ) = (x : ℝ) := by
    exact_mod_cast hpart
  nlinarith [hE, hpart']

/-- At most three small values (`0`, `1`, `2`) are lost when passing from
`theorem1Good` to `theorem1GoodLarge`. -/
lemma theorem1Good_small_card_le_three (x : ℕ) :
    ((theorem1Good x).filter fun n => ¬ 2 < n).card ≤ 3 := by
  classical
  have hsub : ((theorem1Good x).filter fun n => ¬ 2 < n) ⊆ Finset.range 3 := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    exact Finset.mem_range.mpr (by omega)
  exact (Finset.card_le_card hsub).trans (by simp)

lemma theorem1GoodLarge_card_ge (x : ℕ) :
    (theorem1Good x).card ≤ (theorem1GoodLarge x).card + 3 := by
  classical
  have h : (theorem1GoodLarge x).card +
      ((theorem1Good x).filter fun n => ¬ 2 < n).card = (theorem1Good x).card := by
    simpa [theorem1GoodLarge] using Finset.card_filter_add_card_filter_not
      (s := theorem1Good x) (p := fun n => 2 < n)
  have hsmall := theorem1Good_small_card_le_three x
  omega

/-- Eventually `(theorem1Gap / 2) * x` dominates the constant `3`. -/
lemma theorem1_eventually_gap_ge_three :
    ∀ᶠ x : ℕ in atTop, (3 : ℝ) ≤ (theorem1Gap / 2) * (x : ℝ) := by
  have hpos : 0 < theorem1Gap / 2 := div_pos theorem1Gap_pos (by norm_num)
  have ht : Tendsto (fun x : ℕ => (theorem1Gap / 2) * (x : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hpos (tendsto_natCast_atTop_atTop (R := ℝ))
  exact ht.eventually (eventually_ge_atTop (3 : ℝ))

/-- Eventually `54/100 ≤ (theorem1GoodLarge x).card / x`, the hypothesis needed by
`theorem1_of_eventual_good_bound`. -/
theorem theorem1_eventual_good_large_bound :
    ∀ᶠ x : ℕ in atTop,
      (54 : ℝ) / 100 ≤ ((theorem1GoodLarge x).card : ℝ) / (x : ℝ) := by
  filter_upwards [theorem1Good_eventually_lower, theorem1_eventually_gap_ge_three,
      eventually_ne_atTop (0 : ℕ)] with x hGood hGap hx0
  have hdiff : ((theorem1Good x).card : ℝ) ≤ ((theorem1GoodLarge x).card : ℝ) + 3 := by
    exact_mod_cast (theorem1GoodLarge_card_ge x)
  have hxpos : 0 < (x : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hx0)
  have hGoodLarge : (54 : ℝ) / 100 * (x : ℝ) ≤ ((theorem1GoodLarge x).card : ℝ) := by
    nlinarith [hGood, hGap, hdiff]
  exact (le_div_iff₀ hxpos).2 hGoodLarge

/-- Theorem 1: the set `theorem1Set` has natural lower density at least `54/100`. -/
theorem theorem1_main :
    (54 : ℝ) / 100 ≤ lowerNatDensity theorem1Set := by
  exact theorem1_of_eventual_good_bound theorem1_eventual_good_large_bound

end ErdosGLW
