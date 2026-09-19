import ErdosGLW.Theorem1Arithmetic
import ErdosGLW.Theorem1TwoAdic
import ErdosGLW.Theorem1Products
import ErdosGLW.Theorem1Density

/-
Legacy draft retained temporarily for provenance. The checked implementation is
split across the three modules imported above.

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace ErdosGLW

/-- The odd sufficient condition from the proof of Theorem 1. -/
lemma theorem1_odd_condition {n : ℕ} (hn_odd : Odd n)
    (hphi : n / 2 ≤ n.totient) :
    n.totient > (n - n.totient).totient := by
  have hphi_le : n.totient ≤ n := Nat.totient_le n
  have hsub_lt : n - n.totient < n.totient := by
    omega
  exact lt_of_le_of_lt (Nat.totient_le _) hsub_lt

/-- For even n > 2, Euler's totient is even. -/
lemma theorem1_even_totient {n : ℕ} (hn : 2 < n) (heven : Even n) :
    Even n.totient := Nat.totient_even hn

/-- The even sufficient condition from the proof of Theorem 1.
The hypothesis is stated in natural-number form to avoid coercion to reals. -/
lemma theorem1_even_condition {n : ℕ} (hn : 2 < n) (heven : Even n)
    (hphi : n / 3 < n.totient) :
    n.totient > (n - n.totient).totient := by
  have hphi_le : n.totient ≤ n := Nat.totient_le n
  have hsub_even : Even (n - n.totient) := by
    exact heven.sub (Nat.totient_even hn)
  obtain ⟨j, hj⟩ := hsub_even
  have hhalf : (n - n.totient).totient ≤ (n - n.totient) / 2 := by
    rw [Nat.div_eq_of_lt] <;> omega
  have hsub_lt : n - n.totient < n.totient := by
    omega
  exact lt_of_le_of_lt hhalf hsub_lt

/-- A finite, exact formulation of the exceptional sets used in the density proof.
This is the arithmetic bridge before analytic prime-product estimates. -/
def Theorem1Bad (x s : ℕ) : Finset ℕ :=
  if s = 0 then
    (Finset.range x).filter (fun n => Odd n ∧ n.totient < n / 2)
  else
    (Finset.range x).filter (fun n => ∃ m, n = 2 ^ s * m ∧ Odd m ∧ m.totient ≤ 2 * m / 3)

lemma theorem1_good_of_not_bad {x n : ℕ} (hnx : n < x)
    (hnot : ∀ s : ℕ, n ∉ Theorem1Bad x s) :
    n.totient > (n - n.totient).totient := by
  by_cases hnodd : Odd n
  · have hphi : n / 2 ≤ n.totient := by
      by_contra h
      have hbad : n ∈ Theorem1Bad x 0 := by
        simp [Theorem1Bad, hnodd, Nat.not_le.mp h, hnx]
      exact hnot 0 hbad
    exact theorem1_odd_condition hnodd hphi
  · have heven : Even n := (Nat.not_odd_iff_even.mp hnodd)
    by_cases hnsmall : n ≤ 2
    · omega
    have hphi : n / 3 < n.totient := by
      by_contra h
      obtain ⟨s, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd
        (Nat.ne_of_gt (lt_of_lt_of_le (by omega) (Nat.zero_le n)))
      have hs : 0 < s := by
        by_contra hs0
        have hs' : s = 0 := Nat.eq_zero_of_not_pos hs0
        have hodd : Odd n := by
          rw [hnm, hs']
          simpa using hm
        exact hnodd hodd
      have hbad : m.totient ≤ 2 * m / 3 := by
        by_contra hbad
        have hgood : 2 * m / 3 < m.totient := Nat.lt_of_not_ge hbad
        exact hnot s (by
          simp [Theorem1Bad, hs.ne', hnm, hm, hgood])
      have h2m : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
      have hcop : Nat.Coprime (2 ^ s) m := h2m.pow_left s
      have hformula : n.totient = 2 ^ (s - 1) * m.totient := by
        rw [hnm, Nat.totient_mul hcop,
          Nat.totient_prime_pow Nat.prime_two hs]
      rw [hformula] at h
      omega
    exact theorem1_even_condition (by omega) heven hphi

end ErdosGLW
-/
