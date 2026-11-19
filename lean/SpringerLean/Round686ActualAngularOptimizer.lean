import SpringerLean.Round683FiniteTopSet
import SpringerLean.Round679ActualAngularLevels
import SpringerLean.Round39RotateExterior

open MeasureTheory Set
open scoped ComplexConjugate ENNReal

namespace SpringerLean
set_option Elab.async false

/-- A uniform angular bound from the already proved actual pointwise
estimate. No normalization of the direction is required. -/
theorem actualHarmonic_angular_projection_abs_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    |(c*actualHarmonic F (circleMap 0 r θ)).re| ≤ ‖c‖*(2*r) := by
  have hz : ‖circleMap 0 r θ‖ = r := by
    rw [norm_circleMap_zero, abs_of_nonneg hr0]
  have hz1 : ‖circleMap 0 r θ‖ < 1 := by simpa only [hz] using hr1
  have hActual := actualHarmonic_norm_le_two_norm F hc hz1
  rw [hz] at hActual
  calc
    |(c*actualHarmonic F (circleMap 0 r θ)).re| ≤
        ‖c*actualHarmonic F (circleMap 0 r θ)‖ := Complex.abs_re_le_norm _
    _ = ‖c‖*‖actualHarmonic F (circleMap 0 r θ)‖ := norm_mul _ _
    _ ≤ ‖c‖*(2*r) := mul_le_mul_of_nonneg_left hActual (norm_nonneg _)

/-- Every actual angular projection has a genuine maximizing set of each
positive mass below one full turn. The mass here is RAW ANGULAR LENGTH,
not normalized probability. The constant projection is handled separately.
No optimizer, boundary trace, or inner convex-order assumption is an input. -/
theorem actualHarmonic_angular_projection_exists_maximizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioc 0 (2*Real.pi) ∧
      volume E = ENNReal.ofReal (2*h) ∧
      ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioc 0 (2*Real.pi) →
        volume A = ENNReal.ofReal (2*h) →
        (∫ θ in A, (c*actualHarmonic F (circleMap 0 r θ)).re) ≤
          ∫ θ in E, (c*actualHarmonic F (circleMap 0 r θ)).re := by
  classical
  let f : ℝ → ℝ := fun θ => (c*actualHarmonic F (circleMap 0 r θ)).re
  let I : Set ℝ := Ioc 0 (2*Real.pi)
  let μ : Measure ℝ := volume.restrict I
  let B : ℝ := ‖c‖*(2*r)
  have hcont : Continuous f :=
    (actualHarmonic_angular_projection_analytic F hc c hr0 hr1).continuous
  have hbound (θ : ℝ) : |f θ| ≤ B := by
    exact actualHarmonic_angular_projection_abs_le F hc c hr0 hr1 θ
  have hInt : Integrable f μ :=
    (integrable_const B).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun θ => by simpa only [Real.norm_eq_abs] using hbound θ))
  have hmpos : 0 < ENNReal.ofReal (2*h) := ENNReal.ofReal_pos.mpr (by linarith)
  have hmass : ENNReal.ofReal (2*h) ≤ μ univ := by
    change ENNReal.ofReal (2*h) ≤ (volume.restrict (Ioc 0 (2*Real.pi))) univ
    rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rcases actualHarmonic_angular_projection_constant_or_level_null F hc c hr0 hr1 with
    hconstant | hlevels
  · obtain ⟨b, hb⟩ := hconstant
    let E : Set ℝ := Ioc 0 (2*h)
    have hEm : MeasurableSet E := measurableSet_Ioc
    have hEsub : E ⊆ I := by
      intro θ hθ
      exact ⟨hθ.1, le_trans hθ.2 (by linarith)⟩
    have hEmass : volume E = ENNReal.ofReal (2*h) := by
      simp only [E, Real.volume_Ioc, sub_zero]
    refine ⟨E, hEm, hEsub, hEmass, ?_⟩
    intro A hAm hAsub hAmass
    have hfc : f = fun _ => b := funext hb
    change (∫ θ in A, f θ) ≤ ∫ θ in E, f θ
    simp only [hfc, setIntegral_const, Measure.real_def, hAmass, hEmass]
    exact le_rfl
  · have hlevelsμ (a : ℝ) : μ {θ | f θ = a} = 0 := by
      apply le_antisymm _ bot_le
      calc
        μ {θ | f θ = a} ≤ volume {θ | f θ = a} := Measure.restrict_apply_le _ _
        _ = 0 := hlevels a
    have hfull : ∃ R : ℝ, ENNReal.ofReal (2*h) ≤ μ {θ | -f θ ≤ R} := by
      refine ⟨B, ?_⟩
      have heq : {θ | -f θ ≤ B} = univ := by
        ext θ
        simp only [mem_setOf_eq, mem_univ, iff_true]
        linarith [(abs_le.mp (hbound θ)).1]
      rwa [heq]
    obtain ⟨ell, hS, hSmass, hmax⟩ := finiteMeasure_exists_top_set μ f
      hcont.measurable hInt B (fun θ => (abs_le.mp (hbound θ)).2)
      hlevelsμ (ENNReal.ofReal (2*h)) hmpos hfull
    let S : Set ℝ := {θ | ell ≤ f θ}
    let E : Set ℝ := S ∩ I
    have hEm : MeasurableSet E := hS.inter measurableSet_Ioc
    have hEsub : E ⊆ I := inter_subset_right
    have hEmass : volume E = ENNReal.ofReal (2*h) := by
      simpa only [μ, Measure.restrict_apply hS] using hSmass
    refine ⟨E, hEm, hEsub, hEmass, ?_⟩
    intro A hAm hAsub hAmass
    have hAμ : μ A = ENNReal.ofReal (2*h) := by
      change (volume.restrict I) A = _
      rw [Measure.restrict_apply hAm, inter_eq_left.mpr hAsub]
      exact hAmass
    have hle := hmax A hAm hAμ
    change (∫ θ, f θ ∂(μ.restrict A)) ≤ ∫ θ, f θ ∂(μ.restrict S) at hle
    have hAmeasure : μ.restrict A = volume.restrict A :=
      Measure.restrict_restrict_of_subset hAsub
    have hSmeasure : μ.restrict S = volume.restrict E :=
      Measure.restrict_restrict hS
    rw [hAmeasure, hSmeasure] at hle
    exact hle

end SpringerLean
