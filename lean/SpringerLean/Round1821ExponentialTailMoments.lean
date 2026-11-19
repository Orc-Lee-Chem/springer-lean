import SpringerLean.Round1818ReferenceTailPointwise
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 600000

theorem exponential_tail_first_moment {σ : ℝ} (hσ : 0 < σ) :
    (∫ t : ℝ in Ioi 0, t*Real.exp (-(σ*t)))=1/σ^2 := by
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := σ) (by norm_num) hσ
  have hGamma : Real.Gamma 2=1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  norm_num [hGamma,Real.rpow_two] at hh
  simpa only [div_eq_mul_inv,one_mul] using hh

theorem exponential_tail_second_moment {σ : ℝ} (hσ : 0 < σ) :
    (∫ t : ℝ in Ioi 0, t^2*Real.exp (-(σ*t)))=2/σ^3 := by
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := σ) (by norm_num) hσ
  have hGamma : Real.Gamma 3=2 := by
    simpa using Real.Gamma_nat_eq_factorial 2
  norm_num [hGamma,show (2 : ℝ)=(2 : ℕ) by norm_num,Real.rpow_natCast,
    show (3 : ℝ)=(3 : ℕ) by norm_num] at hh
  simpa only [div_eq_mul_inv,mul_comm] using hh

theorem exponential_tail_first_integrable {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t*Real.exp (-(σ*t))) (Ioi 0) := by
  by_contra hnot
  have hh := exponential_tail_first_moment hσ
  rw [integral_undef hnot] at hh
  have hp : (0 : ℝ) < 1/σ^2 := by positivity
  linarith

theorem exponential_tail_second_integrable {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t^2*Real.exp (-(σ*t))) (Ioi 0) := by
  by_contra hnot
  have hh := exponential_tail_second_moment hσ
  rw [integral_undef hnot] at hh
  have hp : (0 : ℝ) < 2/σ^3 := by positivity
  linarith

end SpringerLean

#print axioms SpringerLean.exponential_tail_first_moment
#print axioms SpringerLean.exponential_tail_second_moment
