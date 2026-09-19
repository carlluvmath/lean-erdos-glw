import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace ErdosGLW

open Filter Asymptotics
open scoped Topology

noncomputable def theorem1DensityConstant : ℝ :=
  (47 : ℝ) / 400 * (1 / Real.log 2 + 1 / Real.log (3 / 2))

noncomputable def theorem1DensityError (x : ℕ) : ℝ :=
  (4 + (1 + Real.log (x : ℝ)) / Real.log 2 +
    (Real.log (x : ℝ) / Real.log 2) *
      (1 + Real.log (x : ℝ)) / Real.log (3 / 2)) / x

lemma theorem1_main_constant_lt :
    theorem1DensityConstant < (46 : ℝ) / 100 := by
  have hlog_two : (693 : ℝ) / 1000 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog_three_halves : (405 : ℝ) / 1000 < Real.log (3 / 2 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_gt_d9, Real.log_two_lt_d9]
  have htwo := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 693 / 1000)
    hlog_two
  have hthree := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 405 / 1000)
    hlog_three_halves
  unfold theorem1DensityConstant
  nlinarith

lemma theorem1DensityConstant_lt :
    theorem1DensityConstant < (46 : ℝ) / 100 :=
  theorem1_main_constant_lt

private lemma theorem1_log_div_nat_tendsto_zero :
    Tendsto (fun x : ℕ => Real.log (x : ℝ) / (x : ℝ)) atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa using h.tendsto_div_nhds_zero

private lemma theorem1_log_sq_div_nat_tendsto_zero :
    Tendsto (fun x : ℕ => Real.log (x : ℝ) ^ 2 / (x : ℝ)) atTop (𝓝 0) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa using h.tendsto_div_nhds_zero

private lemma theorem1_const_div_nat_tendsto_zero (c : ℝ) :
    Tendsto (fun x : ℕ => c / (x : ℝ)) atTop (𝓝 0) := by
  simpa using (tendsto_const_nhds.div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ)))

lemma theorem1_error_tendsto :
    Tendsto theorem1DensityError atTop (𝓝 0) := by
  have hconst := theorem1_const_div_nat_tendsto_zero 4
  have hconst1 := theorem1_const_div_nat_tendsto_zero 1
  have hlog := theorem1_log_div_nat_tendsto_zero
  have hlog_sq := theorem1_log_sq_div_nat_tendsto_zero
  have hA := (hconst1.add hlog).const_mul (1 / Real.log 2)
  have hB := (hlog.add hlog_sq).const_mul (1 / (Real.log 2 * Real.log (3 / 2 : ℝ)))
  have hsum := hconst.add (hA.add hB)
  have hsum0 : Tendsto
      (fun x : ℕ =>
        4 / ↑x + (1 / Real.log 2 * (1 / ↑x + Real.log ↑x / ↑x) +
          1 / (Real.log 2 * Real.log (3 / 2)) * (Real.log ↑x / ↑x + Real.log ↑x ^ 2 / ↑x)))
      atTop (𝓝 0) := by
    simpa using hsum
  apply hsum0.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with x hx
  unfold theorem1DensityError
  field_simp
  ring

lemma theorem1DensityError_tendsto :
    Tendsto theorem1DensityError atTop (𝓝 0) :=
  theorem1_error_tendsto

end ErdosGLW
