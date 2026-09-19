import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace ErdosGLW

/-- The odd case used in Theorem 1. For odd `n`, the paper's
`φ(n) ≥ n/2` condition is represented without coercions as
`n + 1 ≤ 2 * φ(n)`. -/
lemma theorem1_odd_condition {n : ℕ} (_hodd : Odd n)
    (hphi : n + 1 ≤ 2 * n.totient) :
    n.totient > (n - n.totient).totient := by
  have hsub : n - n.totient < n.totient := by
    omega
  exact (Nat.totient_le _).trans_lt hsub

/-- Euler's totient is at most half of every even natural number. -/
lemma totient_le_half_of_even {n : ℕ} (heven : Even n) :
    n.totient ≤ n / 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · simp [hn0]
    obtain ⟨q, hq⟩ := heven
    have h2q : n = 2 * q := by omega
    have hq_lt : q < n := by omega
    have hdiv : n / 2 = q := by omega
    rw [hdiv, h2q]
    by_cases hqeven : Even q
    · rw [Nat.totient_two_mul_of_even hqeven]
      have hrec := ih q hq_lt hqeven
      have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hrec
      simpa [mul_comm] using hmul
    · rw [Nat.totient_two_mul_of_odd (Nat.not_even_iff_odd.mp hqeven)]
      exact Nat.totient_le q

/-- Even-case arithmetic using the elementary pairing bound
`φ(t) ≤ t/2` for even `t`. -/
lemma theorem1_even_condition {n : ℕ} (hn : 2 < n) (heven : Even n)
    (hphi : 3 * n.totient > n) :
    n.totient > (n - n.totient).totient := by
  have hsub_even : Even (n - n.totient) := by
    exact (Nat.even_sub (Nat.totient_le n)).mpr
      (iff_of_true heven (Nat.totient_even hn))
  have hhalf := totient_le_half_of_even hsub_even
  have hhalf_lt : (n - n.totient) / 2 < n.totient := by
    apply Nat.div_lt_of_lt_mul
    omega
  exact hhalf.trans_lt hhalf_lt

/-- Theorem 1's arithmetic reduction before the analytic density estimate. -/
lemma theorem1_arithmetic_core {n : ℕ} (hn : 2 < n)
    (hodd_good : Odd n → n + 1 ≤ 2 * n.totient)
    (heven_good : ¬ Odd n → 3 * n.totient > n) :
    n.totient > (n - n.totient).totient := by
  by_cases hodd : Odd n
  · exact theorem1_odd_condition hodd (hodd_good hodd)
  · exact theorem1_even_condition hn (Nat.not_odd_iff_even.mp hodd)
      (heven_good hodd)

/-- Exact finite exceptional predicate used by the paper's counting argument.
The analytic part must bound the cardinality of this set asymptotically. -/
def theorem1Exceptional (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun n =>
    (Odd n ∧ 2 * n.totient < n + 1) ∨
    (¬ Odd n ∧ 3 * n.totient ≤ n)

/-! The following lemmas isolate the finite counting interface used by the
analytic part of the paper.  No density or asymptotic claim is hidden here. -/

def theorem1Good (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun n => ¬(
    (Odd n ∧ 2 * n.totient < n + 1) ∨
    (¬ Odd n ∧ 3 * n.totient ≤ n))

lemma theorem1Good_card_add_exceptional_card (x : ℕ) :
    (theorem1Good x).card + (theorem1Exceptional x).card = x := by
  classical
  let P : ℕ → Prop := fun n =>
    (Odd n ∧ 2 * n.totient < n + 1) ∨
    (¬ Odd n ∧ 3 * n.totient ≤ n)
  change ((Finset.range x).filter fun n => ¬ P n).card +
      ((Finset.range x).filter P).card = x
  rw [add_comm]
  simpa using (Finset.card_filter_add_card_filter_not (s := Finset.range x) P)

lemma theorem1Good_card_lower_bound {x b : ℕ}
    (hb : 100 * b ≤ 46 * x)
    (hbad : (theorem1Exceptional x).card ≤ b) :
    54 * x ≤ 100 * (theorem1Good x).card := by
  have hpartition := theorem1Good_card_add_exceptional_card x
  omega

lemma theorem1Good_mem_of_arithmetic {x n : ℕ} (hnx : n < x)
    (hn : 2 < n)
    (hgood : n ∉ theorem1Exceptional x) :
    n.totient > (n - n.totient).totient := by
  apply theorem1_arithmetic_core hn
  · intro hnodd
    by_contra h
    apply hgood
    simp only [theorem1Exceptional, Finset.mem_filter, Finset.mem_range]
    exact ⟨hnx, Or.inl ⟨hnodd, Nat.lt_of_not_ge h⟩⟩
  · intro hnodd
    by_contra h
    apply hgood
    simp only [theorem1Exceptional, Finset.mem_filter, Finset.mem_range]
    exact ⟨hnx, Or.inr ⟨hnodd, Nat.le_of_not_gt h⟩⟩

end ErdosGLW
