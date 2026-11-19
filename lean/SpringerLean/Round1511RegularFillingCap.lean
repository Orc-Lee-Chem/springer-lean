import SpringerLean.Round1510CappedWeightedSplit

open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The explicit Poisson smoothing of the mean-preserving flattened
comparison circle at a point on the real source radius. -/
noncomputable def flattenedCosinePoissonAtReal (h r : ℝ) : ℝ :=
  (2*Real.pi)⁻¹ *
    (∫ θ : ℝ,
      cappedAngularCosine (2*Real.sin h/h) h θ *
        poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
      ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi))))

noncomputable def centeredPoissonRawMass (r : ℝ) : ℝ :=
  (2*Real.pi)⁻¹ *
    (∫ θ : ℝ,
      poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
      ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi))))

/-- The regularized actual filling has the sharpened cap plus an
explicit epsilon times the fixed kernel mass. -/
theorem regularHarmonic_flattened_cap_eventually
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {ε : ℝ} (hε : 0 < ε)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n : ℕ in atTop,
      (conj ξ*regularHarmonic (omittedScaleSeq n) F (r:ℂ)).re ≤
        flattenedCosinePoissonAtReal h r + ε*centeredPoissonRawMass r := by
  have he := regularExterior_capped_weighted_integral_le_eventually
    F hc ξ hξ h hh0 hhpi hcap hε hr0 hr1
  filter_upwards [he] with n hn
  let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) (2*Real.pi))
  let P : ℝ → ℝ := fun θ => poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
  let f : ℝ → ℝ := fun θ =>
    (conj ξ*rescaleExterior (omittedScaleSeq n) F
      (circleMap 0 1 θ)).re
  let u : ℝ → ℝ := cappedAngularCosine (2*Real.sin h/h) h
  have hz : (r:ℂ) ∈ Metric.ball (0:ℂ) 1 := by
    simp [Metric.mem_ball,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,hr1]
  have hrep := regularHarmonic_projected_poisson_circleAverage
    F hc (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
      ξ hz
  rw [circleAverage_eq_restrictedAngularIntegral] at hrep
  have hcomm : (∫ θ, P θ*f θ ∂μ) = (∫ θ, f θ*P θ ∂μ) := by
    apply integral_congr_ae
    filter_upwards [] with θ
    ring
  change (2*Real.pi)⁻¹*(∫ θ, P θ*f θ ∂μ) =
    (conj ξ*regularHarmonic (omittedScaleSeq n) F (r:ℂ)).re at hrep
  rw [hcomm] at hrep
  change (∫ θ, f θ*P θ ∂μ) ≤
    (∫ θ, u θ*P θ ∂μ)+ε*(∫ θ,P θ ∂μ) at hn
  rw [←hrep]
  change (2*Real.pi)⁻¹*(∫ θ, f θ*P θ ∂μ) ≤
    (2*Real.pi)⁻¹*(∫ θ,u θ*P θ ∂μ)+
      ε*((2*Real.pi)⁻¹*(∫ θ,P θ ∂μ))
  have h := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (2*Real.pi)⁻¹)
  nlinarith [h]

end SpringerLean

#print axioms SpringerLean.regularHarmonic_flattened_cap_eventually
