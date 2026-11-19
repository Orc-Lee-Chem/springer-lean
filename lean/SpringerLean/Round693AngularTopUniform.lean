import SpringerLean.Round690ActualAngularTopValue

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- Stability of actual top values under a uniform change of their
angular integrands. The uniform-difference premise is displayed: it is
an interface estimate, not an assumed rearrangement theorem. -/
theorem actualAngularTopValue_sub_le_uniform
    (F F' : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hc' : CenteredExteriorUnivalent F') (c c' : ℂ)
    {r r' : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hr'0 : 0 ≤ r') (hr'1 : r' < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) (ε : ℝ)
    (hdiff : ∀ θ ∈ Ioc 0 (2*Real.pi),
      |(c*actualHarmonic F (circleMap 0 r θ)).re-
        (c'*actualHarmonic F' (circleMap 0 r' θ)).re| ≤ ε) :
    actualAngularTopValue F c r h-actualAngularTopValue F' c' r' h ≤ 2*h*ε := by
  obtain ⟨E, hE, hval, hmax⟩ := actualAngularTopValue_attained F hc c hr0 hr1 hh0 hhpi
  let f : ℝ → ℝ := fun θ => (c*actualHarmonic F (circleMap 0 r θ)).re
  let g : ℝ → ℝ := fun θ => (c'*actualHarmonic F' (circleMap 0 r' θ)).re
  have hsub : E ⊆ Icc 0 (2*Real.pi) := hE.2.1.trans Ioc_subset_Icc_self
  have hCF : Continuous f :=
    (actualHarmonic_angular_projection_analytic F hc c hr0 hr1).continuous
  have hCG : Continuous g :=
    (actualHarmonic_angular_projection_analytic F' hc' c' hr'0 hr'1).continuous
  have hIntF : IntegrableOn f E :=
    (hCF.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have hIntG : IntegrableOn g E :=
    (hCG.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have hfin : volume E < ∞ := by rw [hE.2.2]; finiteness
  have hreal : volume.real E = 2*h := by
    rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)]
  have hn := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := E)
    (f := fun θ => f θ-g θ) hfin (fun θ hθ => by
      simpa only [Real.norm_eq_abs] using hdiff θ (hE.2.1 hθ))
  rw [integral_sub hIntF hIntG] at hn
  simp only [Real.norm_eq_abs, hreal] at hn
  have hcand := actualAngularTopValue_candidate_le F' hc' c' hr'0 hr'1 hh0 hhpi E hE
  change (∫ θ in E, g θ) ≤ actualAngularTopValue F' c' r' h at hcand
  rw [hval]
  change (∫ θ in E, f θ)-actualAngularTopValue F' c' r' h ≤ 2*h*ε
  have habs := le_abs_self ((∫ θ in E, f θ)-(∫ θ in E, g θ))
  nlinarith

theorem actualAngularTopValue_abs_sub_le_uniform
    (F F' : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hc' : CenteredExteriorUnivalent F') (c c' : ℂ)
    {r r' : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hr'0 : 0 ≤ r') (hr'1 : r' < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) (ε : ℝ)
    (hdiff : ∀ θ ∈ Ioc 0 (2*Real.pi),
      |(c*actualHarmonic F (circleMap 0 r θ)).re-
        (c'*actualHarmonic F' (circleMap 0 r' θ)).re| ≤ ε) :
    |actualAngularTopValue F c r h-actualAngularTopValue F' c' r' h| ≤ 2*h*ε := by
  have hf := actualAngularTopValue_sub_le_uniform F F' hc hc' c c'
    hr0 hr1 hr'0 hr'1 hh0 hhpi ε hdiff
  have hb := actualAngularTopValue_sub_le_uniform F' F hc' hc c' c
    hr'0 hr'1 hr0 hr1 hh0 hhpi ε (fun θ hθ => by
      simpa only [abs_sub_comm] using hdiff θ hθ)
  exact abs_le.mpr ⟨by linarith, hf⟩

/-- Here the interface premise is discharged using the same actual F:
top values are Lipschitz in an arbitrary complex direction. -/
theorem actualAngularTopValue_direction_lipschitz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c d : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    |actualAngularTopValue F c r h-actualAngularTopValue F d r h| ≤
      4*‖c-d‖*r*h := by
  have hdiff (θ : ℝ) (_ : θ ∈ Ioc 0 (2*Real.pi)) :
      |(c*actualHarmonic F (circleMap 0 r θ)).re-
        (d*actualHarmonic F (circleMap 0 r θ)).re| ≤ ‖c-d‖*(2*r) := by
    have heq : (c*actualHarmonic F (circleMap 0 r θ)).re-
        (d*actualHarmonic F (circleMap 0 r θ)).re =
        ((c-d)*actualHarmonic F (circleMap 0 r θ)).re := by
      simp only [sub_mul, Complex.sub_re]
    rw [heq]
    exact actualHarmonic_angular_projection_abs_le F hc (c-d) hr0 hr1 θ
  have hb := actualAngularTopValue_abs_sub_le_uniform F F hc hc c d
    hr0 hr1 hr0 hr1 hh0 hhpi (‖c-d‖*(2*r)) hdiff
  convert hb using 1 <;> ring

end SpringerLean
