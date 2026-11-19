import SpringerLean.Round1497ActualInnerCaps
import SpringerLean.Round38CenteredWeighted

open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The original omitted-set cap and the already proved centered-cosine
comparison hold simultaneously on every superlevel set of a centered
Poisson kernel, uniformly on a late regularization tail. -/
theorem regularExterior_poisson_level_two_caps_eventually
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (R : ℝ)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ R)
    {ε : ℝ} (hε : 0 < ε)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0 < t →
      let E : Set ℝ :=
        {θ | t ≤ poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)}
      let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) (2*Real.pi))
      (∫ θ in E,
        (conj ξ*rescaleExterior (omittedScaleSeq n) F
          (circleMap 0 1 θ)).re ∂μ) ≤
        (∫ θ in E, 2*(circleMap 0 1 θ).re ∂μ) ∧
      (∫ θ in E,
        (conj ξ*rescaleExterior (omittedScaleSeq n) F
          (circleMap 0 1 θ)).re ∂μ) ≤
        (R+ε)*μ.real E := by
  let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) (2*Real.pi))
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have he := regularExterior_projection_cap_eventually_scaleSeq
    F hc ξ R hcap hε
  filter_upwards [he] with n hn t ht
  let E : Set ℝ :=
    {θ | t ≤ poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)}
  let f : ℝ → ℝ := fun θ =>
    (conj ξ*rescaleExterior (omittedScaleSeq n) F
      (circleMap 0 1 θ)).re
  have hs0 := omittedScaleSeq_pos n
  have hs1 := omittedScaleSeq_lt_one n
  have hE : MeasurableSet E :=
    measurableSet_le measurable_const
      (centeredPoisson_weight_continuous hr0 hr1).measurable
  have hfinite : μ E < ⊤ := measure_lt_top μ E
  obtain ⟨C,hC0,hC⟩ := regularExterior_projected_angle_bounded
    F hc hs0 hs1 ξ hξ
  have hfCont : Continuous f := by
    exact Complex.continuous_re.comp
      (regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ)
  have hfInt : Integrable f μ := by
    apply Integrable.mono' (g := fun _ : ℝ => C) (integrable_const C)
      hfCont.measurable.aestronglyMeasurable
    filter_upwards [] with θ
    simpa only [Real.norm_eq_abs] using hC θ
  have hmono : (∫ θ in E, f θ ∂μ) ≤ (∫ θ in E, R+ε ∂μ) := by
    apply integral_mono_ae hfInt.integrableOn integrableOn_const
    filter_upwards [] with θ
    exact hn _ (by simp [norm_circleMap_zero])
  have hbase := regularExterior_projected_poisson_level_le_comparator
    F hc hs0 hs1 ξ hξ hr0 hr1 ht
  dsimp only [E,μ] at hbase ⊢
  constructor
  · exact hbase
  · change (∫ θ in E, f θ ∂μ) ≤ (R+ε)*μ.real E
    rw [setIntegral_const] at hmono
    simpa only [smul_eq_mul, mul_comm (μ.real E) (R+ε)] using hmono

end SpringerLean

#print axioms SpringerLean.regularExterior_poisson_level_two_caps_eventually
