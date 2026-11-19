import SpringerLean.Round1569PhasePotentialBound

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The actual phase potential is an L1 function on the open unit disk,
including the zero set of the harmonic filling. -/
theorem actualHarmonicPhasePotentialDensity_integrableOn_unitDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1) :
    IntegrableOn (actualHarmonicPhasePotentialDensity F k β)
      (ball (0:ℂ) 1) := by
  let D : Set ℂ := ball 0 1
  let μ : Measure ℂ := volume.restrict D
  have hD : MeasurableSet D := isOpen_ball.measurableSet
  have hDb : Bornology.IsBounded D :=
    (isCompact_closedBall (0:ℂ) 1).isBounded.subset ball_subset_closedBall
  haveI : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using hDb.measure_lt_top⟩
  have hH : AEStronglyMeasurable (actualHarmonic F) μ :=
    (actualHarmonic_continuousOn_unitBall F hc).aestronglyMeasurable hD
  have hUcont : ContinuousOn (actualHarmonicPhaseField F k β) D := by
    exact Complex.continuous_im.comp_continuousOn
      (continuousOn_const.mul
        ((actualHarmonic_continuousOn_unitBall F hc).pow k))
  have hU : AEStronglyMeasurable (actualHarmonicPhaseField F k β) μ :=
    hUcont.aestronglyMeasurable hD
  have hmeas : AEStronglyMeasurable
      (actualHarmonicPhasePotentialDensity F k β) μ := by
    change AEStronglyMeasurable (fun z : ℂ =>
      (actualHarmonicPhaseField F k β z)^2 / ‖actualHarmonic F z‖^2) μ
    simp only [div_eq_mul_inv]
    exact (hU.pow 2).mul (hH.norm.pow 2).inv₀
  have hbound : ∀ᵐ z ∂μ,
      ‖actualHarmonicPhasePotentialDensity F k β z‖ ≤
        (2:ℝ)^(2*k-2) := by
    filter_upwards [ae_restrict_mem hD] with z hz
    obtain ⟨h0,hM⟩ := actualHarmonicPhasePotentialDensity_pointwise_le
      F hc hk β hβ (by simpa only [D,mem_ball,dist_zero_right] using hz)
    simpa only [Real.norm_eq_abs,abs_of_nonneg h0] using hM
  exact (integrable_const ((2:ℝ)^(2*k-2)) :
    Integrable (fun _ : ℂ => (2:ℝ)^(2*k-2)) μ).mono' hmeas hbound

/-- The normalized potential term in the multiplier inequality. -/
noncomputable def actualHarmonicPhasePotential
    (F : ℂ → ℂ) (k : ℕ) (β : ℂ) : ℝ :=
  Real.pi⁻¹*(∫ z in ball (0:ℂ) 1,
    actualHarmonicPhasePotentialDensity F k β z)

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhasePotentialDensity_integrableOn_unitDisk
