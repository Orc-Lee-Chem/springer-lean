import SpringerLean.Round748UnitDiskLimit

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false

/-- All finite real convex tests on the ACTUAL harmonic filling, under
normalized disk area. The comparator is the disk variable2Re z. -/
theorem actualHarmonic_disk_convex_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ univ ψ) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, ψ ((conj ξ*actualHarmonic F z).re)) ≤
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, ψ (2*z.re)) := by
  have hψc : Continuous ψ := by
    simpa only [continuousOn_univ] using ConvexOn.continuousOn isOpen_univ hψ
  let X : ℂ → ℝ := fun z => (conj ξ*actualHarmonic F z).re
  let Y : ℂ → ℝ := fun z => 2*z.re
  have hX : ContinuousOn X (ball (0 : ℂ) 1) :=
    Complex.continuous_re.comp_continuousOn
      (continuousOn_const.mul (actualHarmonic_continuousOn_unitBall F hc))
  have hY : Continuous Y := by dsimp [Y]; fun_prop
  have hXr (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : X z ∈ Icc (-2) 2 := by
    have hn : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    have hb : |X z| ≤ 2 := by
      calc
        _ ≤ ‖conj ξ*actualHarmonic F z‖ := Complex.abs_re_le_norm _
        _ = ‖actualHarmonic F z‖ := by rw [norm_mul, Complex.norm_conj, hξ, one_mul]
        _ ≤ 2*‖z‖ := actualHarmonic_norm_le_two_norm F hc hn
        _ ≤ 2 := by linarith
    exact abs_le.mp hb
  have hYr (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : Y z ∈ Icc (-2) 2 := by
    have hn : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    have hb : |Y z| ≤ 2 := by
      calc
        _ = 2*|z.re| := by simp [Y]
        _ ≤ 2*‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (by norm_num)
        _ ≤ 2 := by linarith
    exact abs_le.mp hb
  obtain ⟨M,hM⟩ := ((isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).image hψc).isBounded.exists_norm_le
  have hfi : IntegrableOn (fun z => ψ (X z)) (ball (0 : ℂ) 1) :=
    integrableOn_unitDisk_of_continuousOn_bound _ (hψc.comp_continuousOn hX) M
      (fun z hz => hM _ ⟨X z,hXr z hz,rfl⟩)
  have hgi : IntegrableOn (fun z => ψ (Y z)) (ball (0 : ℂ) 1) :=
    integrableOn_unitDisk_of_continuousOn_bound _ (hψc.comp hY).continuousOn M
      (fun z hz => hM _ ⟨Y z,hYr z hz,rfl⟩)
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ Real.pi⁻¹)
  apply unitDisk_integral_le_of_innerBall_le _ _ hfi hgi
  intro b hb0 hb1
  have hv := actualHarmonic_annulus_convex_le F hc ξ hξ ψ hψ
    (a := 0) (b := b) le_rfl hb0.le hb1
  have hx := setIntegral_congr_set (f := fun z => ψ (X z)) (greenPolarRegion_zero_ae_ball b)
  have hy := setIntegral_congr_set (f := fun z => ψ (Y z)) (greenPolarRegion_zero_ae_ball b)
  change Real.pi⁻¹*(∫ z in greenPolarRegion 0 b, ψ (X z)) ≤
    Real.pi⁻¹*(∫ z in greenPolarRegion 0 b, ψ (Y z)) at hv
  rw [hx,hy] at hv
  exact le_of_mul_le_mul_left hv (inv_pos.mpr Real.pi_pos)

end SpringerLean

#print axioms SpringerLean.actualHarmonic_disk_convex_le
