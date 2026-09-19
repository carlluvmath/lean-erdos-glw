import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
import ErdosGLW.Theorem1Arithmetic

namespace ErdosGLW

/-!
The two-adic bookkeeping used in the proof of Theorem 1.

For a nonzero natural number `n`, Mathlib's `ordProj[2] n` is the largest
power of two dividing `n`, and `ordCompl[2] n` is the complementary odd part.
-/

def twoAdicExponent (n : ℕ) : ℕ := n.factorization 2

def twoAdicOddPart (n : ℕ) : ℕ := ordCompl[2] n

lemma two_adic_decomp {n : ℕ} (_hn : n ≠ 0) :
    n = 2 ^ twoAdicExponent n * twoAdicOddPart n := by
  exact (Nat.ordProj_mul_ordCompl_eq_self n 2).symm

lemma two_adic_odd_part {n : ℕ} (hn : n ≠ 0) :
    Odd (twoAdicOddPart n) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  exact Nat.not_dvd_ordCompl Nat.prime_two hn (even_iff_two_dvd.mp heven)

lemma two_adic_exponent_pos {n : ℕ} (hn : n ≠ 0) (heven : Even n) :
    0 < twoAdicExponent n := by
  by_contra hpos
  have hz : twoAdicExponent n = 0 := Nat.eq_zero_of_not_pos hpos
  have hnot : ¬2 ∣ n := by
    intro hdvd
    have hfac := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn hdvd
    exact (Nat.ne_of_gt hfac) hz
  exact hnot (even_iff_two_dvd.mp heven)

lemma two_adic_odd_part_coprime {n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime 2 (twoAdicOddPart n) := by
  exact Nat.coprime_ordCompl Nat.prime_two hn

lemma two_adic_exponent_zero_iff_odd {n : ℕ} (hn : n ≠ 0) :
    twoAdicExponent n = 0 ↔ Odd n := by
  constructor
  · intro hz
    have hnot : ¬2 ∣ n := by
      intro hdvd
      have hfac := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn hdvd
      exact (Nat.ne_of_gt hfac) hz
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact hnot (even_iff_two_dvd.mp heven)
  · intro hodd
    by_contra hpos
    have hs : 0 < twoAdicExponent n := Nat.pos_of_ne_zero hpos
    have hpow : 2 ∣ 2 ^ twoAdicExponent n := by
      exact dvd_pow_self 2 (Nat.ne_of_gt hs)
    have hdiv : 2 ∣ n := by
      rw [two_adic_decomp hn]
      exact dvd_mul_of_dvd_left hpow _
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)

/-!
Finite versions of the exceptional sets in the paper. `B₀` contains the odd
exceptions, while `Bₛ` records the even exceptions with a fixed two-adic
exponent `s > 0`.
-/

def theorem1B0 (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun n =>
    Odd n ∧ 2 * n.totient < n + 1

noncomputable def theorem1Bs (x s : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range x).filter fun n =>
    ∃ m, n = 2 ^ s * m ∧ Odd m ∧ 3 * m.totient ≤ 2 * m

lemma totient_two_pow_mul {s m : ℕ} (hs : 0 < s) (hm : Odd m) :
    (2 ^ s * m).totient = 2 ^ (s - 1) * m.totient := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
  rw [Nat.totient_mul (hcop.pow_left _),
    Nat.totient_prime_pow_succ Nat.prime_two]
  simp [Nat.add_one_sub_one, mul_comm]

lemma mem_theorem1B0_iff {x n : ℕ} :
    n ∈ theorem1B0 x ↔ n < x ∧ Odd n ∧ 2 * n.totient < n + 1 := by
  simp [theorem1B0, and_left_comm]

lemma mem_theorem1Bs_iff {x s n : ℕ} :
    n ∈ theorem1Bs x s ↔
      n < x ∧ ∃ m, n = 2 ^ s * m ∧ Odd m ∧ 3 * m.totient ≤ 2 * m := by
  classical
  simp [theorem1Bs, and_left_comm]

lemma mem_theorem1Bs_two_adic {x n : ℕ}
    (hnx : n < x) (hn : n ≠ 0) (heven : Even n)
    (hbad : 3 * n.totient ≤ n) :
    n ∈ theorem1Bs x (twoAdicExponent n) := by
  have hs : 0 < twoAdicExponent n :=
    two_adic_exponent_pos hn heven
  have hm : Odd (twoAdicOddPart n) :=
    two_adic_odd_part hn
  have hdecomp := two_adic_decomp hn
  refine (mem_theorem1Bs_iff).2 ⟨hnx, twoAdicOddPart n, hdecomp, hm, ?_⟩
  have hpow : 2 ^ twoAdicExponent n =
      2 ^ (twoAdicExponent n - 1) * 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hs]
    rw [pow_succ]
  have hphi : n.totient =
      2 ^ (twoAdicExponent n - 1) * (twoAdicOddPart n).totient := by
    calc
      n.totient = (2 ^ twoAdicExponent n * twoAdicOddPart n).totient :=
        congrArg Nat.totient hdecomp
      _ = 2 ^ (twoAdicExponent n - 1) * (twoAdicOddPart n).totient :=
        totient_two_pow_mul hs hm
  have hbound : 3 * (2 ^ (twoAdicExponent n - 1) *
      (twoAdicOddPart n).totient) ≤
      2 ^ twoAdicExponent n * twoAdicOddPart n := by
    calc
      3 * (2 ^ (twoAdicExponent n - 1) *
          (twoAdicOddPart n).totient) = 3 * n.totient := by rw [hphi]
      _ ≤ n := hbad
      _ = 2 ^ twoAdicExponent n * twoAdicOddPart n := hdecomp
  rw [hpow] at hbound
  have hpos : 0 < 2 ^ (twoAdicExponent n - 1) := by positivity
  have hcancel :
      3 * (twoAdicOddPart n).totient ≤ 2 * twoAdicOddPart n := by
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ (twoAdicExponent n - 1)) _ hpos
    simpa [mul_assoc, mul_left_comm, mul_comm] using hbound
  exact hcancel

/-- Formula (3), before truncating the two-adic exponent: every exceptional
number is zero, an odd member of `B₀`, or belongs to the `Bₛ` indexed by its
positive two-adic exponent. -/
lemma theorem1Exceptional_covered {x n : ℕ}
    (hn : n ∈ theorem1Exceptional x) :
    n = 0 ∨ n ∈ theorem1B0 x ∨
      ∃ s : ℕ, 0 < s ∧ n ∈ theorem1Bs x s := by
  have hn' := Finset.mem_filter.mp hn
  rcases hn'.2 with hodd | heven
  · exact Or.inr (Or.inl ((mem_theorem1B0_iff).2
      ⟨Finset.mem_range.mp hn'.1, hodd.1, hodd.2⟩))
  · by_cases hn0 : n = 0
    · exact Or.inl hn0
    · have hneven : Even n := Nat.not_odd_iff_even.mp heven.1
      have hs := two_adic_exponent_pos hn0 hneven
      exact Or.inr (Or.inr ⟨twoAdicExponent n, hs,
        mem_theorem1Bs_two_adic (Finset.mem_range.mp hn'.1) hn0 hneven heven.2⟩)

lemma mem_theorem1Bs_exponent_le_log {x s n : ℕ}
    (hn : n ∈ theorem1Bs x s) : s ≤ Nat.log 2 x := by
  rcases (mem_theorem1Bs_iff.mp hn) with ⟨hnx, m, rfl, hm, hbad⟩
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  have hmpos : 0 < m := hm.pos
  have hpowle : 2 ^ s ≤ 2 ^ s * m := by
    exact Nat.le_mul_of_pos_right _ hmpos
  exact hpowle.trans (Nat.le_of_lt hnx)

/-- Formula (3), with the two-adic exponent restricted to the finite range
used by the paper. -/
lemma theorem1Exceptional_covered_log {x n : ℕ}
    (hn : n ∈ theorem1Exceptional x) :
    n = 0 ∨ n ∈ theorem1B0 x ∨
      ∃ s ∈ Finset.Icc 1 (Nat.log 2 x), n ∈ theorem1Bs x s := by
  rcases theorem1Exceptional_covered hn with hzero | hzero
  · exact Or.inl hzero
  · rcases hzero with hB0 | ⟨s, hs, hBs⟩
    · exact Or.inr (Or.inl hB0)
    · exact Or.inr (Or.inr ⟨s, Finset.mem_Icc.mpr
        ⟨hs, mem_theorem1Bs_exponent_le_log hBs⟩, hBs⟩)

end ErdosGLW
