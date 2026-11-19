import SpringerLean.Round1550ThinAnnulusRadialIntegral
import SpringerLean.Round746AnnulusCircleOrder

open MeasureTheory Set Metric

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Transfer a quantitative circle-average saving to an actual planar
annulus. The normalized radial Jacobian is `2r dr`, counted once. -/
theorem annulus_power_circle_gain_transfer
    (f : ℂ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ContinuousOn f (closedBall (0:ℂ) b))
    {m : ℕ} (hm : 2 ≤ m) (K : ℝ)
    (hcircle : ∀ r ∈ Icc a b,
      K*(2*r)^(m-2) ≤ Real.circleAverage f 0 r) :
    K*2^(m-1:ℕ)*((b^m-a^m)/(m:ℝ)) ≤
      Real.pi⁻¹*(∫ z in greenPolarRegion a b, f z) := by
  let g : ℝ → ℝ := fun r => r*(2*Real.pi)*K*(2*r)^(m-2)
  let j : ℝ → ℝ := fun r => r*(2*Real.pi)*Real.circleAverage f 0 r
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hgi : IntegrableOn g (Icc a b) :=
    hgc.continuousOn.integrableOn_compact isCompact_Icc
  have hji : IntegrableOn j (Icc a b) :=
    radial_circleAverage_integrableOn_of_continuousOn_closedBall f ha hf
  have hraw : (∫ r in Icc a b,g r) ≤ ∫ r in Icc a b,j r := by
    apply setIntegral_mono_on hgi hji measurableSet_Icc
    intro r hr
    have hr0 : 0 ≤ r := ha.trans hr.1
    have h := mul_le_mul_of_nonneg_left (hcircle r hr)
      (show 0 ≤ r*(2*Real.pi) by positivity)
    simpa only [g,j,mul_assoc] using h
  have hpolar : (∫ r in Icc a b,j r) =
      ∫ z in greenPolarRegion a b,f z := by
    exact (greenPolarRegion_integral_eq_radial_circleAverage f ha hf).symm
  have hL : (∫ r in Icc a b,g r) =
      Real.pi*K*2^(m-1:ℕ)*((b^m-a^m)/(m:ℝ)) := by
    rw [integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le hab]
    have hpoint (r : ℝ) : g r =
        (Real.pi*K)*(2*r*(2*r)^(m-2)) := by
      dsimp [g]
      ring
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const_mul,
      thinAnnulus_radial_power_integral hm]
    ring
  rw [hpolar,hL] at hraw
  have hscaled := mul_le_mul_of_nonneg_left hraw
    (show 0 ≤ Real.pi⁻¹ by positivity)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  convert hscaled using 1 <;> field_simp <;> ring

end SpringerLean

#print axioms SpringerLean.annulus_power_circle_gain_transfer
