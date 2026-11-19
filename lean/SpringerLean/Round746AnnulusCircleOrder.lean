import SpringerLean.Round740PoissonCauchyExtension
import SpringerLean.Round11PolarArea
import SpringerLean.Round27DoubleCircle

open MeasureTheory Set Metric

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false

/-- The raw angular integral, with the polar radial factor counted ONCE. -/
theorem greenPolar_angular_integral_eq_circleAverage (f : ℂ → ℝ) (r : ℝ) :
    (∫ θ in Icc (0 : ℝ) (2*Real.pi), r*f (greenPolar r θ)) =
      r*(2*Real.pi)*Real.circleAverage f 0 r := by
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc, circleAverage_eq_angle_Ioc_general]
  simp only [greenPolar, circleMap_zero]
  simp_rw [mul_comm (_ : ℂ) Complex.I]
  field_simp [Real.pi_ne_zero]

/-- Compact polar integrability requires only continuity on the actual
closed radius-b disk, not on the whole plane or the unit boundary. -/
theorem greenPolar_pullback_integrableOn_of_continuousOn_closedBall
    (f : ℂ → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hf : ContinuousOn f (closedBall (0 : ℂ) b)) (c d : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1*f (greenPolar p.1 p.2))
      (Icc a b ×ˢ Icc c d) := by
  have hp : Continuous (fun p : ℝ × ℝ => greenPolar p.1 p.2) := by
    unfold greenPolar
    fun_prop
  have hm : MapsTo (fun p : ℝ × ℝ => greenPolar p.1 p.2)
      (Icc a b ×ˢ Icc c d) (closedBall (0 : ℂ) b) := by
    intro p hps
    rw [mem_closedBall, dist_zero_right, greenPolar_norm_of_nonneg (ha.trans hps.1.1)]
    exact hps.1.2
  exact (continuous_fst.continuousOn.mul
    (hf.comp hp.continuousOn hm)).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- Signed real integration on an actual planar annulus in terms of the
SAME circle probability measure. Its normalized radial measure is2r dr. -/
theorem greenPolarRegion_integral_eq_radial_circleAverage
    (f : ℂ → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hf : ContinuousOn f (closedBall (0 : ℂ) b)) :
    (∫ z in greenPolarRegion a b, f z) =
      ∫ r in Icc a b, r*(2*Real.pi)*Real.circleAverage f 0 r := by
  let Q : ℝ × ℝ → ℝ := fun p => p.1*f (greenPolar p.1 p.2)
  have hzero := greenPolar_pullback_integrableOn_of_continuousOn_closedBall f ha hf 0 (2*Real.pi)
  have hneg := greenPolar_pullback_integrableOn_of_continuousOn_closedBall f ha hf (-Real.pi) Real.pi
  have hrect : (∫ p in Icc (a, (0 : ℝ)) (b, 2*Real.pi), Q p) =
      ∫ r in Icc a b, ∫ θ in Icc (0 : ℝ) (2*Real.pi), Q (r,θ) := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    simpa using setIntegral_prod Q hzero
  calc
    (∫ z in greenPolarRegion a b, f z) =
        ∫ p in Icc (a, (0 : ℝ)) (b, 2*Real.pi), Q p :=
      (greenPolarRegion_integral_positive_angle f a b ha hzero hneg).symm
    _ = ∫ r in Icc a b, ∫ θ in Icc (0 : ℝ) (2*Real.pi), Q (r,θ) := hrect
    _ = _ := by simp only [Q, greenPolar_angular_integral_eq_circleAverage]

theorem radial_circleAverage_integrableOn_of_continuousOn_closedBall
    (f : ℂ → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hf : ContinuousOn f (closedBall (0 : ℂ) b)) :
    IntegrableOn (fun r => r*(2*Real.pi)*Real.circleAverage f 0 r) (Icc a b) := by
  have hi := greenPolar_pullback_integrableOn_of_continuousOn_closedBall f ha hf 0 (2*Real.pi)
  rw [IntegrableOn, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at hi
  simpa only [IntegrableOn, greenPolar_angular_integral_eq_circleAverage] using hi.integral_prod_left

/-- A reusable annulus integration rule. The circle estimate is explicit
in this GENERAL interface; actual-map corollaries discharge it themselves. -/
theorem greenPolarRegion_integral_le_of_circleAverage_le
    (f g : ℂ → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hf : ContinuousOn f (closedBall (0 : ℂ) b))
    (hg : ContinuousOn g (closedBall (0 : ℂ) b))
    (hcirc : ∀ r ∈ Icc a b, Real.circleAverage f 0 r ≤ Real.circleAverage g 0 r) :
    (∫ z in greenPolarRegion a b, f z) ≤ ∫ z in greenPolarRegion a b, g z := by
  rw [greenPolarRegion_integral_eq_radial_circleAverage f ha hf,
    greenPolarRegion_integral_eq_radial_circleAverage g ha hg]
  apply setIntegral_mono_on
    (radial_circleAverage_integrableOn_of_continuousOn_closedBall f ha hf)
    (radial_circleAverage_integrableOn_of_continuousOn_closedBall g ha hg) measurableSet_Icc
  intro r hr
  exact mul_le_mul_of_nonneg_left (hcirc r hr) (mul_nonneg (ha.trans hr.1) (by positivity))

end SpringerLean

#print axioms SpringerLean.greenPolarRegion_integral_eq_radial_circleAverage
#print axioms SpringerLean.greenPolarRegion_integral_le_of_circleAverage_le
