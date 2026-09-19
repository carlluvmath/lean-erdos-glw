import ErdosGLW.Theorem1Arithmetic
import Mathlib.Topology.Order.LiminfLimsup

namespace ErdosGLW

open Filter Finset

/-- Number of members of `A` below `x`. -/
noncomputable def countBelow (A : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.range x).filter (fun n => n ∈ A)).card

/-- Natural lower density, using the paper's counting convention `n < x`. -/
noncomputable def lowerNatDensity (A : Set ℕ) : ℝ :=
  liminf (fun x : ℕ => (countBelow A x : ℝ) / x) atTop

lemma lowerNatDensity_ge_of_eventually_ge {A : Set ℕ} {c : ℝ}
    (h : ∀ᶠ x : ℕ in atTop, c ≤ (countBelow A x : ℝ) / x) :
    c ≤ lowerNatDensity A := by
  apply le_liminf_of_le
  · have hbounded : IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ)
        (fun x : ℕ => (countBelow A x : ℝ) / x) := by
      apply isBoundedUnder_of
      refine ⟨(1 : ℝ), fun x => ?_⟩
      have hcount : countBelow A x ≤ x := by
        classical
        simp only [countBelow]
        exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range x)
      by_cases hx : x = 0
      · simp [hx]
      · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hx))).2
          (Nat.cast_le.mpr hcount)
    exact hbounded.isCoboundedUnder_ge
  · exact h

/-- The set `A` from the paper. -/
def theorem1Set : Set ℕ :=
  {n | n.totient > (n - n.totient).totient}

/-- The finite sufficient-condition set, excluding the three irrelevant
small values where the paper's strict inequality is not asserted. -/
def theorem1GoodLarge (x : ℕ) : Finset ℕ :=
  (theorem1Good x).filter fun n => 2 < n

lemma theorem1GoodLarge_subset_count {x : ℕ} :
    (theorem1GoodLarge x).card ≤ countBelow theorem1Set x := by
  classical
  apply Finset.card_le_card
  intro n hn
  simp only [theorem1GoodLarge, Finset.mem_filter] at hn
  rcases hn with ⟨hnGood, hnLarge⟩
  have hnGood' := Finset.mem_filter.mp hnGood
  change n ∈ (Finset.range x).filter (fun n => n ∈ theorem1Set)
  apply Finset.mem_filter.mpr
  refine ⟨hnGood'.1, ?_⟩
  apply theorem1Good_mem_of_arithmetic (Finset.mem_range.mp hnGood'.1) hnLarge
  intro hbad
  exact hnGood'.2 (Finset.mem_filter.mp hbad).2

/-- Once the finite good sets have an eventual 54 percent lower bound,
Theorem 1 follows at the natural lower-density level. -/
theorem theorem1_of_eventual_good_bound
    (hgood : ∀ᶠ x : ℕ in atTop,
      (54 : ℝ) / 100 ≤ ((theorem1GoodLarge x).card : ℝ) / x) :
    (54 : ℝ) / 100 ≤ lowerNatDensity theorem1Set := by
  apply lowerNatDensity_ge_of_eventually_ge
  filter_upwards [hgood] with x hx
  exact hx.trans (div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (theorem1GoodLarge_subset_count (x := x))) (Nat.cast_nonneg x))

end ErdosGLW
