import SpringerLean.Round19ThresholdSet
import SpringerLean.Round679ActualAngularLevels
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open MeasureTheory Set

namespace SpringerLean
set_option Elab.async false

/-- Reflection of the angle preserves the raw integral over a turn.
This keeps the analytic reflected-coordinate convention separate from
the positive-angle convention of the final actual set comparison. -/
theorem periodic_reflected_turn_integral
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (hp : Function.Periodic f T) :
    (∫ t in Ioc 0 T, f (-t)) = ∫ t in Ioc 0 T, f t := by
  calc
    (∫ t in Ioc 0 T, f (-t)) = ∫ t in 0..T, f (-t) :=
      (intervalIntegral.integral_of_le hT.le).symm
    _ = ∫ t in 0..T, f t := by
      rw [intervalIntegral.integral_comp_neg f]
      simpa using hp.intervalIntegral_add_eq (-T) 0
    _ = ∫ t in Ioc 0 T, f t := intervalIntegral.integral_of_le hT.le

/-- Positive-part integrals over one full period do not depend on the
angular cut. No sign or mean-zero assumption on the original function. -/
theorem periodic_positivePart_turn_integral
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (hp : Function.Periodic f T)
    (ell q : ℝ) :
    (∫ t in Ioc q (q+T), max (f t-ell) 0) =
      ∫ t in Ioc 0 T, max (f t-ell) 0 := by
  have hper : Function.Periodic (fun t => max (f t-ell) 0) T := by
    intro t
    exact congrArg (fun u : ℝ => max (u-ell) 0) (hp t)
  calc
    (∫ t in Ioc q (q+T), max (f t-ell) 0) =
        ∫ t in q..q+T, max (f t-ell) 0 :=
      (intervalIntegral.integral_of_le (by linarith : q ≤ q+T)).symm
    _ = ∫ t in 0..T, max (f t-ell) 0 := by
      simpa only [zero_add] using hper.intervalIntegral_add_eq q 0
    _ = ∫ t in Ioc 0 T, max (f t-ell) 0 :=
      intervalIntegral.integral_of_le hT.le

/-- The same threshold upper bound controls signed integrals of candidates
in ANY one-period representative. This permits choosing a cut in an
excluded open interval without a measurable modulo-folding construction. -/
theorem periodic_setIntegral_le_threshold
    (f : ℝ → ℝ) (hf : Continuous f) {T : ℝ} (hT : 0 < T)
    (hp : Function.Periodic f T) (ell q : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) (hsub : A ⊆ Ioc q (q+T)) :
    (∫ t in A, f t) ≤ ell*volume.real A +
      ∫ t in Ioc 0 T, max (f t-ell) 0 := by
  let μ : Measure ℝ := volume.restrict (Ioc q (q+T))
  have hInt : Integrable f μ :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hPos : Integrable (fun t => max (f t-ell) 0) μ :=
    (((hf.sub continuous_const).max continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hAmass : μ.real A = volume.real A := by
    simp only [Measure.real_def, μ, Measure.restrict_apply hA,
      inter_eq_left.mpr hsub]
  have hAmeasure : μ.restrict A = volume.restrict A :=
    Measure.restrict_restrict_of_subset hsub
  have hle := setIntegral_le_threshold_add_positivePart f A hA hInt ell hPos
  rw [hAmass] at hle
  change (∫ t, f t ∂(μ.restrict A)) ≤ ell*volume.real A +
    ∫ t in Ioc q (q+T), max (f t-ell) 0 at hle
  rw [hAmeasure, periodic_positivePart_turn_integral f hT hp ell q] at hle
  exact hle

theorem actualHarmonic_angular_projection_periodic
    (F : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Function.Periodic
      (fun t : ℝ => (c*actualHarmonic F (circleMap 0 r t)).re) (2*Real.pi) := by
  intro t
  exact congrArg (fun z : ℂ => (c*actualHarmonic F z).re) (periodic_circleMap 0 r t)

theorem actualHarmonic_angular_test_reflected_turn_integral
    (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (ψ : ℝ → ℝ) :
    (∫ t in Ioc 0 (2*Real.pi),
      ψ ((c*actualHarmonic F (circleMap 0 r (-t))).re)) =
      ∫ t in Ioc 0 (2*Real.pi),
        ψ ((c*actualHarmonic F (circleMap 0 r t)).re) := by
  have hp : Function.Periodic
      (fun t : ℝ => ψ ((c*actualHarmonic F (circleMap 0 r t)).re)) (2*Real.pi) := by
    intro t
    exact congrArg (fun z : ℂ => ψ ((c*actualHarmonic F z).re)) (periodic_circleMap 0 r t)
  exact periodic_reflected_turn_integral
    (fun t : ℝ => ψ ((c*actualHarmonic F (circleMap 0 r t)).re)) (by positivity) hp

/-- An actual-F candidate bound, valid after ANY angular cut. Raw angular
length/integral is used on both sides. This is a proved input to the
optimizer argument, not yet the sharp inner-circle set comparison. -/
theorem actualHarmonic_angular_setIntegral_le_threshold
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ell q : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) (hsub : A ⊆ Ioc q (q+2*Real.pi)) :
    (∫ t in A, (c*actualHarmonic F (circleMap 0 r t)).re) ≤
      ell*volume.real A + ∫ t in Ioc 0 (2*Real.pi),
        max ((c*actualHarmonic F (circleMap 0 r t)).re-ell) 0 := by
  exact periodic_setIntegral_le_threshold _
    (actualHarmonic_angular_projection_analytic F hc c hr0 hr1).continuous
    (by positivity) (actualHarmonic_angular_projection_periodic F c r)
    ell q A hA hsub

end SpringerLean
