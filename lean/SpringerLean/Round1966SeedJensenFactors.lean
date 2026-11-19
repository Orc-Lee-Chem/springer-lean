import SpringerLean.Round1965SeedPotentialFactor
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

open MeasureTheory

namespace SpringerLean

/-- The outside linear factor contributes exactly `log ‖z‖` to the
unit-circle logarithmic average. -/
theorem exterior_circleAverage_log_factor
    (z : ℂ) (hz : 1 < ‖z‖) :
    Real.circleAverage (fun u : ℂ => Real.log ‖u - z‖) 0 1 =
      Real.log ‖z‖ := by
  rw [circleAverage_log_norm_sub_const_eq_posLog]
  exact Real.posLog_eq_log (by simpa only [abs_of_nonneg (norm_nonneg z)] using hz.le)

/-- The interior partner contributes zero to the logarithmic average. -/
theorem oddStarSeedPartner_circleAverage_log_zero
    (t : ℝ) (ht : |t| < 1) (z : ℂ) (hz : 1 < ‖z‖) :
    Real.circleAverage
      (fun u : ℂ => Real.log ‖u - oddStarSeedPartner t z‖) 0 1 = 0 := by
  rw [circleAverage_log_norm_sub_const_eq_posLog]
  apply (Real.posLog_eq_zero_iff _).2
  rw [abs_of_nonneg (norm_nonneg _)]
  exact (oddStarSeedPartner_norm_lt_one t ht z hz).le

/-- The pole of the rational seed is inside the circle, so its
logarithmic denominator has zero circle average. -/
theorem oddStarSeedPole_circleAverage_log_zero
    (t : ℝ) (ht : |t| < 1) :
    Real.circleAverage
      (fun u : ℂ => Real.log ‖u - (t : ℂ) * Complex.I‖) 0 1 = 0 := by
  rw [circleAverage_log_norm_sub_const_eq_posLog]
  apply (Real.posLog_eq_zero_iff _).2
  rw [abs_of_nonneg (norm_nonneg _)]
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  simpa only [Real.norm_eq_abs] using ht.le

end SpringerLean

#print axioms SpringerLean.exterior_circleAverage_log_factor
#print axioms SpringerLean.oddStarSeedPartner_circleAverage_log_zero
#print axioms SpringerLean.oddStarSeedPole_circleAverage_log_zero
