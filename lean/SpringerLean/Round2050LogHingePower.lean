import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Real Set

namespace SpringerLean

noncomputable def radialLogHingeWeight (p a t : ℝ) : ℝ :=
  Real.exp (p * t) * Real.posLog (a / Real.exp t)

theorem radialLogHingeWeight_nonneg (p a t : ℝ) : 0 ≤ radialLogHingeWeight p a t :=
  mul_nonneg (Real.exp_nonneg _) Real.posLog_nonneg

/-- Positive powers are integrals of logarithmic radial hinges. At
radius zero the hinge is everywhere zero. -/
theorem radialLogHingeWeight_integral (p a : ℝ) (hp : 0 < p) (ha : 0 ≤ a) :
    Integrable (radialLogHingeWeight p a) ∧
      (∫ t, radialLogHingeWeight p a t) = a ^ p / p ^ 2 := by
  obtain rfl | ha := ha.eq_or_lt
  · have hz : radialLogHingeWeight p 0 = 0 := by
      funext t
      simp [radialLogHingeWeight]
    simp [hz, Real.zero_rpow hp.ne']
  let g : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun t => t * Real.exp (-(p*t)))
  have hγ : (∫ t : ℝ in Ioi 0, t * Real.exp (-(p*t))) = (1 / p) ^ 2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hp
    have hg2 : Real.Gamma 2 = 1 := by
      simp
    rw [hg2, mul_one] at h
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      Real.rpow_two] using h
  have hgI : IntegrableOn (fun t => t * Real.exp (-(p*t))) (Ioi 0) := by
    by_contra h
    have hzero := integral_undef h
    rw [hγ] at hzero
    exact (pow_pos (one_div_pos.mpr hp) 2).ne' hzero
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr hgI
  have heq (t : ℝ) :
      radialLogHingeWeight p a t = a ^ p * g (Real.log a - t) := by
    change Real.exp (p * t) * max 0 (Real.log (a / Real.exp t)) = _
    rw [Real.log_div ha.ne' (Real.exp_ne_zero _), Real.log_exp]
    simp only [g]
    by_cases ht : 0 < Real.log a - t
    · rw [max_eq_right ht.le,
        indicator_of_mem (show Real.log a - t ∈ Ioi (0 : ℝ) from ht),
        Real.rpow_def_of_pos ha]
      have hexp : Real.exp (Real.log a * p) * Real.exp (-(p * (Real.log a - t))) =
          Real.exp (p * t) := by rw [← Real.exp_add]; congr 1; ring
      rw [show Real.exp (Real.log a * p) *
          ((Real.log a - t) * Real.exp (-(p * (Real.log a - t)))) =
          (Real.exp (Real.log a * p) * Real.exp (-(p * (Real.log a - t)))) *
            (Real.log a - t) by ring, hexp]
    · rw [max_eq_left (le_of_not_gt ht), mul_zero,
        indicator_of_notMem (show Real.log a - t ∉ Ioi (0 : ℝ) from ht), mul_zero]
  have hmp := (volume : Measure ℝ).measurePreserving_sub_left (Real.log a)
  have hemb : MeasurableEmbedding (fun t : ℝ => Real.log a - t) := by
    exact (MeasurableEquiv.subLeft (Real.log a)).measurableEmbedding
  have hfun : radialLogHingeWeight p a =
      fun t => a ^ p * g (Real.log a - t) := funext heq
  rw [hfun]
  refine ⟨(hmp.integrable_comp_of_integrable hg).const_mul _, ?_⟩
  rw [integral_const_mul, hmp.integral_comp hemb g]
  simp only [g, integral_indicator measurableSet_Ioi, hγ]
  field_simp [hp.ne']

end SpringerLean
