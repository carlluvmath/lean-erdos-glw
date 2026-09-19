import Mathlib.Data.Nat.Totient

namespace ErdosGLW

open Nat Finset

/-- Every prime factor of a squarefull number occurs with exponent at least two. -/
def Squarefull (m : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ m → p ^ 2 ∣ m

/-- The odd part of `n` is the part left after removing all powers of two. -/
def OddPartSquarefull (n : ℕ) : Prop :=
  Squarefull (ordCompl[2] n)

lemma prime_dvd_totient_of_sq_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hpow : p ^ 2 ∣ n) : p ∣ n.totient := by
  have hk : 2 ≤ n.factorization p :=
    (hp.pow_dvd_iff_le_factorization hn).mp hpow
  let f : ℕ →₀ ℕ := Finsupp.single p 2
  have hmem : p ∈ n.factorization.support := by
    rw [Finsupp.mem_support_iff]
    exact (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hk))
  have hsupp : f.support ⊆ n.factorization.support := by
    intro q hq
    have hqp : q = p := by
      simpa [f] using hq
    simpa [hqp] using hmem
  have hprod : f.prod (fun q k => q ^ (k - 1) * (q - 1)) ∣
      n.factorization.prod (fun q k => q ^ (k - 1) * (q - 1)) := by
    apply Finsupp.prod_dvd_prod_of_subset_of_dvd hsupp
    intro q hq
    have hqp : q = p := by
      simpa [f] using hq
    subst q
    simp only [f, Finsupp.single_eq_same]
    apply Nat.mul_dvd_mul_right
    rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt]
    exact Nat.sub_le_sub_right hk 1
  rw [Nat.totient_eq_prod_factorization hn] at ⊢
  have hterm : p ∣ f.prod (fun q k => q ^ (k - 1) * (q - 1)) := by
    simp only [f, Finsupp.prod, Finsupp.support_single, Finset.prod_singleton]
    norm_num
  exact dvd_trans hterm hprod

lemma prime_dvd_odd_part {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ n) : p ∣ ordCompl[2] n := by
  apply Nat.dvd_ordCompl_of_dvd_not_dvd hpn
  intro h2
  have hodd : Odd p := hp.odd_of_ne_two hp2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

lemma prime_dvd_totient_of_odd_part_squarefull {n p : ℕ} (hn : n ≠ 0)
    (hlarge : 2 < n) (hsq : OddPartSquarefull n) (hp : p.Prime) (hpn : p ∣ n) : p ∣ n.totient := by
  by_cases hp2 : p = 2
  · subst p
    exact (even_iff_two_dvd.mp (Nat.totient_even hlarge))
  · have hop : p ∣ ordCompl[2] n := prime_dvd_odd_part hp hp2 hpn
    have hpowop := hsq p hp hop
    exact prime_dvd_totient_of_sq_dvd hn hp (dvd_trans hpowop (Nat.ordCompl_dvd n 2))

end ErdosGLW

namespace ErdosGLW

lemma coprime_of_coprime_sub {n t a : ℕ}
    (hprime : ∀ p, p.Prime → p ∣ n → p ∣ t)
    (hcop : (n - t).Coprime a) : n.Coprime a := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpa
  have hpt : p ∣ t := hprime p hp hpn
  have hpm : p ∣ n - t := Nat.dvd_sub hpn hpt
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop hpm hpa)

theorem theorem2 {n : ℕ} (hlarge : 2 < n) (hsq : OddPartSquarefull n) :
    n.totient > (n - n.totient).totient := by
  have hn : n ≠ 0 := by omega
  have hprime : ∀ p, p.Prime → p ∣ n → p ∣ n.totient := by
    intro p hp hpn
    exact prime_dvd_totient_of_odd_part_squarefull hn hlarge hsq hp hpn
  have hphi_pos : 0 < n.totient := Nat.totient_pos.mpr (by omega)
  have hphi_ne_one : n.totient ≠ 1 := by
    intro h
    have hn2 : n = 2 := (Nat.totient_eq_one_iff.mp h).resolve_left (by omega : n ≠ 1)
    omega
  have hphi_gt_one : 1 < n.totient := by omega
  have hphi_le : n.totient ≤ n := Nat.totient_le n
  let S : Finset ℕ := (Finset.range (n - n.totient)).filter
    (fun a => (n - n.totient).Coprime a)
  let T : Finset ℕ := (Finset.range n).filter (fun a => n.Coprime a)
  have hST : S ⊂ T := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro a ha
      have ha' := (Finset.mem_filter.mp ha)
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ha'.1) (Nat.sub_le n n.totient))
      · exact coprime_of_coprime_sub hprime ha'.2
    · intro hEq
      have hnmem : n - 1 ∈ T := by
        apply Finset.mem_filter.mpr
        constructor
        · omega
        · rw [Nat.coprime_self_sub_right (by omega : 1 ≤ n)]
          simp
      have hnotmem : n - 1 ∉ S := by
        simp only [S, Finset.mem_filter, Finset.mem_range, not_and]
        intro hlt _
        exfalso
        have ht_le_one : n.totient ≤ 1 := by omega
        omega
      exact hnotmem (hEq ▸ hnmem)
  have hcard : S.card < T.card := Finset.card_lt_card hST
  change S.card < T.card
  exact hcard

end ErdosGLW
