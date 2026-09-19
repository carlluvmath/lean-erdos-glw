import ErdosGLW.Theorem1Counting
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ErdosGLW
open Finset

def theorem1OddPrimes (x : ℕ) : Finset ℕ :=
  (range x).filter fun p => p.Prime ∧ p ≠ 2

def theorem1PrimeMultiplicity (x s p : ℕ) : ℕ :=
  ((theorem1OddInputs x s).filter fun m => p ∣ m).card

lemma primeFactors_subset_oddPrimes {x s m : ℕ}
    (hm : m ∈ theorem1OddInputs x s) : m.primeFactors ⊆ theorem1OddPrimes x := by
  rcases mem_filter.mp hm with ⟨hmx, hodd, _⟩
  intro p hp
  have hpm := Nat.dvd_of_mem_primeFactors hp
  refine mem_filter.mpr ⟨mem_range.mpr ?_, Nat.prime_of_mem_primeFactors hp, ?_⟩
  · exact (Nat.le_of_dvd hodd.pos hpm).trans_lt (mem_range.mp hmx)
  · intro heq
    subst p
    exact hodd.not_two_dvd_nat hpm

/-- Regroup Euler factors by prime: the exponent counts divisible odd inputs. -/
lemma theorem1T_eq_prime_product (x s : ℕ) :
    theorem1T x s = ∏ p ∈ theorem1OddPrimes x,
      (1 - (p : ℝ)⁻¹) ^ theorem1PrimeMultiplicity x s p := by
  classical
  unfold theorem1T
  calc
    (∏ m ∈ theorem1OddInputs x s, totientRatio m) =
        ∏ m ∈ theorem1OddInputs x s, ∏ p ∈ theorem1OddPrimes x,
          if p ∣ m then (1 - (p : ℝ)⁻¹) else 1 := by
      apply prod_congr rfl
      intro m hm
      have hm0 := (mem_filter.mp hm).2.1.pos.ne'
      rw [totientRatio_eq_prod_primeFactors hm0, ← prod_filter]
      congr 1
      ext p
      constructor
      · intro hp
        exact mem_filter.mpr ⟨primeFactors_subset_oddPrimes hm hp,
          Nat.dvd_of_mem_primeFactors hp⟩
      · intro hp
        exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).2.1,
          (mem_filter.mp hp).2, hm0⟩
    _ = _ := by
      rw [prod_comm]
      apply prod_congr rfl
      intro p hp
      rw [← prod_filter, prod_const]
      rfl

lemma oddPrimeFactor_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ (1 - (p : ℝ)⁻¹) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpinv : (p : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hp0]
    exact hp1
  exact sub_nonneg.mpr hpinv

lemma oddPrimeFactor_le_one (p : ℕ) : (1 - (p : ℝ)⁻¹) ≤ 1 := by
  exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg p))

/-- Formula (5)'s order-theoretic core: any upper bounds on the prime
multiplicities produce a lower bound for `T`. -/
lemma prime_product_lower_bound {x s : ℕ} {e : ℕ → ℕ}
    (he : ∀ p ∈ theorem1OddPrimes x, theorem1PrimeMultiplicity x s p ≤ e p) :
    (∏ p ∈ theorem1OddPrimes x, (1 - (p : ℝ)⁻¹) ^ e p) ≤ theorem1T x s := by
  rw [theorem1T_eq_prime_product]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact pow_nonneg (oddPrimeFactor_nonneg (Finset.mem_filter.mp hp).2.1) _
  · intro p hp
    apply pow_le_pow_of_le_one
    · exact oddPrimeFactor_nonneg (Finset.mem_filter.mp hp).2.1
    · exact oddPrimeFactor_le_one p
    · exact he p hp

/-- Formula (5), with the real exponent appearing in the paper. -/
lemma theorem1_prime_product_lower_bound (x s : ℕ) :
    (∏ p ∈ theorem1OddPrimes x,
      (1 - (p : ℝ)⁻¹) ^ (((x : ℝ) / (2 ^ s * p) + 1) / 2)) ≤
      theorem1T x s := by
  rw [theorem1T_eq_prime_product]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact Real.rpow_nonneg (oddPrimeFactor_nonneg (Finset.mem_filter.mp hp).2.1) _
  · intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2.1
    have hpOdd : Odd p := hpPrime.odd_of_ne_two (Finset.mem_filter.mp hp).2.2
    have hcount := theorem1OddMultipleCount (x := x) (s := s) hpPrime hpOdd
    have hbase0 : 0 < (1 - (p : ℝ)⁻¹) := by
      have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
      have : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by exact_mod_cast hpPrime.pos)).2 hpgt
      linarith
    have hbase1 : (1 - (p : ℝ)⁻¹) ≤ 1 := oddPrimeFactor_le_one p
    calc
      (1 - (p : ℝ)⁻¹) ^ (((x : ℝ) / (2 ^ s * p) + 1) / 2) ≤
          (1 - (p : ℝ)⁻¹) ^
            (((theorem1OddInputs x s).filter fun m => p ∣ m).card : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1 hcount
      _ = (1 - (p : ℝ)⁻¹) ^
          theorem1PrimeMultiplicity x s p := by
        rw [Real.rpow_natCast]
        rfl

end ErdosGLW
