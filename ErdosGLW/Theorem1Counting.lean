import ErdosGLW.Theorem1Products

namespace ErdosGLW

private lemma odd_eq_two_mul_div_two_add_one {n : ℕ} (hn : Odd n) :
    n = 2 * (n / 2) + 1 := by
  obtain ⟨k, rfl⟩ := hn
  omega

/-- Integer form of the count of odd multiples of an odd prime in one
two-adic stratum. -/
lemma theorem1OddMultipleCount_nat {x s p : ℕ} (hp : Nat.Prime p)
    (_hpodd : Odd p) :
    ((theorem1OddInputs x s).filter fun m => p ∣ m).card ≤
      (x + 2 ^ s * p) / (2 * (2 ^ s * p)) := by
  classical
  let inputs := (theorem1OddInputs x s).filter fun m => p ∣ m
  let bound := (x + 2 ^ s * p) / (2 * (2 ^ s * p))
  let index : ℕ → ℕ := fun m => (m / p) / 2
  have hden_pos : 0 < 2 * (2 ^ s * p) :=
    mul_pos (by omega) (mul_pos (by positivity) hp.pos)
  have hmaps : Set.MapsTo index (inputs : Set ℕ) (Finset.range bound : Set ℕ) := by
    intro m hm
    have hm' : m ∈ inputs := hm
    have hmfilter := Finset.mem_filter.mp hm'
    have hminput := Finset.mem_filter.mp hmfilter.1
    have hmodd : Odd m := hminput.2.1
    have hscaled : 2 ^ s * m < x := hminput.2.2
    have hpdiv : p ∣ m := hmfilter.2
    have hm_factor : p * (m / p) = m := Nat.mul_div_cancel' hpdiv
    have hquot_odd : Odd (m / p) := by
      apply Nat.Odd.of_mul_right
      rw [hm_factor]
      exact hmodd
    have hquotient :
        m / p = 2 * ((m / p) / 2) + 1 :=
      odd_eq_two_mul_div_two_add_one hquot_odd
    have hscaled' :
        (2 ^ s * p) * (2 * ((m / p) / 2) + 1) < x := by
      calc
        (2 ^ s * p) * (2 * ((m / p) / 2) + 1) =
            (2 ^ s * p) * (m / p) :=
              congrArg (fun q => (2 ^ s * p) * q) hquotient.symm
        _ = 2 ^ s * (p * (m / p)) := by ring
        _ = 2 ^ s * m := by rw [hm_factor]
        _ < x := hscaled
    have hindex : index m < bound := by
      apply (Nat.lt_div_iff_mul_lt hden_pos).2
      dsimp [index, bound]
      have hsplit :
          (2 ^ s * p) * (2 * ((m / p) / 2)) + (2 ^ s * p) < x := by
        calc
          (2 ^ s * p) * (2 * ((m / p) / 2)) + (2 ^ s * p) =
              (2 ^ s * p) * (2 * ((m / p) / 2) + 1) := by ring
          _ < x := hscaled'
      rw [show (m / p) / 2 * (2 * (2 ^ s * p)) =
          (2 ^ s * p) * (2 * ((m / p) / 2)) by ring]
      omega
    simpa [bound] using hindex
  have hinj : Set.InjOn index (inputs : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∈ inputs := ha
    have hb' : b ∈ inputs := hb
    have ha_filter := Finset.mem_filter.mp ha'
    have hb_filter := Finset.mem_filter.mp hb'
    have ha_input := Finset.mem_filter.mp ha_filter.1
    have hb_input := Finset.mem_filter.mp hb_filter.1
    have ha_factor : p * (a / p) = a := Nat.mul_div_cancel' ha_filter.2
    have hb_factor : p * (b / p) = b := Nat.mul_div_cancel' hb_filter.2
    have ha_quot_odd : Odd (a / p) := by
      apply Nat.Odd.of_mul_right
      rw [ha_factor]
      exact ha_input.2.1
    have hb_quot_odd : Odd (b / p) := by
      apply Nat.Odd.of_mul_right
      rw [hb_factor]
      exact hb_input.2.1
    have ha_quotient :
        a / p = 2 * ((a / p) / 2) + 1 :=
      odd_eq_two_mul_div_two_add_one ha_quot_odd
    have hb_quotient :
        b / p = 2 * ((b / p) / 2) + 1 :=
      odd_eq_two_mul_div_two_add_one hb_quot_odd
    have hquotient : a / p = b / p := by
      dsimp [index] at hab
      omega
    calc
      a = p * (a / p) := ha_factor.symm
      _ = p * (b / p) := by rw [hquotient]
      _ = b := hb_factor
  have hcard :
      inputs.card ≤ (Finset.range bound).card :=
    Finset.card_le_card_of_injOn index hmaps hinj
  simpa [inputs, bound] using hcard

/-- Real-valued odd-multiple count used in the prime-product estimate. -/
lemma theorem1OddMultipleCount {x s p : ℕ} (hp : Nat.Prime p)
    (hpodd : Odd p) :
    (((theorem1OddInputs x s).filter fun m => p ∣ m).card : ℝ) ≤
      ((x : ℝ) / (2 ^ s * p) + 1) / 2 := by
  have hnat := theorem1OddMultipleCount_nat (x := x) (s := s) hp hpodd
  have hcast :
      (((theorem1OddInputs x s).filter fun m => p ∣ m).card : ℝ) ≤
        (((x + 2 ^ s * p) / (2 * (2 ^ s * p)) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    (((theorem1OddInputs x s).filter fun m => p ∣ m).card : ℝ) ≤
        (((x + 2 ^ s * p) / (2 * (2 ^ s * p)) : ℕ) : ℝ) := hcast
    _ ≤ ((x + 2 ^ s * p : ℕ) : ℝ) / (2 * (2 ^ s * p) : ℕ) :=
      Nat.cast_div_le
    _ = ((x : ℝ) / (2 ^ s * p) + 1) / 2 := by
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpow0 : (2 : ℝ) ^ s ≠ 0 := pow_ne_zero _ (by norm_num)
      push_cast
      field_simp [hp0, hpow0]

end ErdosGLW
