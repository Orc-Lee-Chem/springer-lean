import SpringerLean.Round691AngularTopDual
import SpringerLean.Round13Mean

open MeasureTheory Set
open scoped ComplexConjugate ENNReal

namespace SpringerLean
set_option Elab.async false

/-- The raw full-turn mean is zero, for an arbitrary complex direction.
The normalization is removed explicitly from the verified circle mean. -/
theorem actualHarmonic_angular_projection_turn_integral_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ t in Ioc 0 (2*Real.pi),
      (c*actualHarmonic F (circleMap 0 r t)).re) = 0 := by
  have hm := actualHarmonic_projection_circleAverage_zero F hc (conj c) hr0 hr1
  simp only [Complex.conj_conj] at hm
  rw [Real.circleAverage_def, smul_eq_mul] at hm
  have hn : (2*Real.pi)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  have hz := (mul_eq_zero.mp hm).resolve_left hn
  simpa only [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2*Real.pi)] using hz

/-- Zero full-turn mean implies nonnegativity of every top-mass integral.
The bounded dual optimizer, rather than a measurable family of sets, is used. -/
theorem actualAngularTopValue_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    0 ≤ actualAngularTopValue F c r h := by
  let I : Set ℝ := Ioc 0 (2*Real.pi)
  let f : ℝ → ℝ := fun t => (c*actualHarmonic F (circleMap 0 r t)).re
  have hf : Continuous f :=
    (actualHarmonic_angular_projection_analytic F hc c hr0 hr1).continuous
  have hInt : IntegrableOn f I :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hzero : (∫ t in I, f t) = 0 :=
    actualHarmonic_angular_projection_turn_integral_zero F hc c hr0 hr1
  obtain ⟨ell, hbound, hval⟩ :=
    actualAngularTopValue_exists_bounded_threshold F hc c hr0 hr1 hh0 hhpi
  have hPos : IntegrableOn (fun t => max (f t-ell) 0) I :=
    (((hf.sub continuous_const).max continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hPnonneg : 0 ≤ ∫ t in I, max (f t-ell) 0 :=
    integral_nonneg (fun t => le_max_right _ _)
  change actualAngularTopValue F c r h =
    2*h*ell + ∫ t in I, max (f t-ell) 0 at hval
  by_cases hell : 0 ≤ ell
  · rw [hval]
    exact add_nonneg (mul_nonneg (by linarith) hell) hPnonneg
  · have hconst : (∫ t in I, ell) = (2*Real.pi)*ell := by
      rw [setIntegral_const]
      change volume.real (Ioc 0 (2*Real.pi))*ell = _
      rw [Measure.real_def, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.pi)]
    have hdiff : (∫ t in I, f t-ell) = -(2*Real.pi)*ell := by
      rw [integral_sub hInt (integrable_const ell), hzero, hconst]
      ring
    have hmono : (∫ t in I, f t-ell) ≤ ∫ t in I, max (f t-ell) 0 :=
      integral_mono (hInt.sub (integrable_const ell)) hPos (fun t => le_max_left _ _)
    have hprod : 0 ≤ (2*Real.pi-2*h)*(-ell) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- The other horizontal edge of the star strip is controlled by zero mean.
This is a coarse endpoint estimate, not the sharp4r*sin(h) comparison. -/
theorem actualAngularTopValue_le_complement_mass
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    actualAngularTopValue F c r h ≤ 4*‖c‖*r*(Real.pi-h) := by
  let I : Set ℝ := Ioc 0 (2*Real.pi)
  let f : ℝ → ℝ := fun t => (c*actualHarmonic F (circleMap 0 r t)).re
  let B : ℝ := ‖c‖*(2*r)
  have hf : Continuous f :=
    (actualHarmonic_angular_projection_analytic F hc c hr0 hr1).continuous
  have hInt : IntegrableOn f I :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hzero : (∫ t in I, f t) = 0 :=
    actualHarmonic_angular_projection_turn_integral_zero F hc c hr0 hr1
  have hfun : (fun t => max (f t-(-B)) 0) = fun t => f t+B := by
    funext t
    have hb := actualHarmonic_angular_projection_abs_le F hc c hr0 hr1 t
    change |f t| ≤ B at hb
    rw [sub_neg_eq_add, max_eq_left (by linarith [(abs_le.mp hb).1])]
  have hconst : (∫ t in I, B) = (2*Real.pi)*B := by
    rw [setIntegral_const]
    change volume.real (Ioc 0 (2*Real.pi))*B = _
    rw [Measure.real_def, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.pi)]
  have hupper := actualAngularTopValue_le_threshold F hc c hr0 hr1 hh0 hhpi (-B)
  change actualAngularTopValue F c r h ≤
    2*h*(-B) + ∫ t in I, max (f t-(-B)) 0 at hupper
  rw [hfun, integral_add hInt (integrable_const B), hzero, hconst, zero_add] at hupper
  convert hupper using 1 <;> dsimp [B] <;> ring

theorem actualAngularTopValue_abs_le_complement_mass
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    |actualAngularTopValue F c r h| ≤ 4*‖c‖*r*(Real.pi-h) := by
  rw [abs_of_nonneg (actualAngularTopValue_nonneg F hc c hr0 hr1 hh0 hhpi)]
  exact actualAngularTopValue_le_complement_mass F hc c hr0 hr1 hh0 hhpi

end SpringerLean

#print axioms SpringerLean.actualHarmonic_angular_projection_turn_integral_zero
#print axioms SpringerLean.actualAngularTopValue_nonneg
#print axioms SpringerLean.actualAngularTopValue_le_complement_mass
#print axioms SpringerLean.actualAngularTopValue_abs_le_complement_mass
