import SpringerLean.Round721RegularRadialTrace
import SpringerLean.Round690ActualAngularTopValue
import SpringerLean.Round33ActualArcBound

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A genuine quantitative right trace for the actual regularized top
function.  The error tends to zero uniformly in angular half-mass; the
boundary sine estimate is PROVED from the actual boundary comparison. -/
theorem regularExterior_actualAngularTopValue_le_sine_add_radial_error
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (c : ℂ), ‖c‖ = 1 →
      ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ h : ℝ, 0 < h → h < Real.pi →
        actualAngularTopValue (rescaleExterior s F) c r h ≤
          4*Real.sin h+2*h*L*(1-r) := by
  obtain ⟨L, hL0, hL⟩ := regularHarmonic_angular_boundary_exists_lipschitz F hc hs0 hs1
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  refine ⟨L, hL0, ?_⟩
  intro c hcn r hr0 hr1 h hh0 hhpi
  obtain ⟨E, hE, hval, hmax⟩ :=
    actualAngularTopValue_attained (rescaleExterior s F) hcG c hr0 hr1 hh0 hhpi
  let f : ℝ → ℝ := fun θ => (c*actualHarmonic (rescaleExterior s F) (circleMap 0 r θ)).re
  let g : ℝ → ℝ := fun θ => (c*rescaleExterior s F (circleMap 0 1 θ)).re
  have hf : Continuous f :=
    (actualHarmonic_angular_projection_analytic (rescaleExterior s F) hcG c hr0 hr1).continuous
  have hg : Continuous g := by
    simpa only [g, Function.comp_def, Complex.conj_conj] using Complex.continuous_re.comp
      (regularExterior_rotated_angle_continuous F hc hs0 hs1 (conj c))
  have hsub : E ⊆ Icc 0 (2*Real.pi) := hE.2.1.trans Ioc_subset_Icc_self
  have hfi : IntegrableOn f E := (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have hgi : IntegrableOn g E := (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have hreal : volume.real E = 2*h := by
    rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)]
  have hmass : (volume.restrict (Ioc (0 : ℝ) (2*Real.pi))).real E = 2*h := by
    rw [Measure.real_def, Measure.restrict_apply hE.1, inter_eq_left.mpr hE.2.1,
      hE.2.2, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)]
  have hb := regularExterior_projected_set_le_sine_of_raw_mass F hc hs0 hs1
    (conj c) (by simpa using hcn) h hh0.le hhpi E hE.1 hmass
  have hmeasure : (volume.restrict (Ioc (0 : ℝ) (2*Real.pi))).restrict E = volume.restrict E :=
    Measure.restrict_restrict_of_subset hE.2.1
  change (∫ θ, (conj (conj c)*rescaleExterior s F (circleMap 0 1 θ)).re
    ∂((volume.restrict (Ioc (0 : ℝ) (2*Real.pi))).restrict E)) ≤ 4*Real.sin h at hb
  rw [hmeasure] at hb
  simp only [Complex.conj_conj] at hb
  have hdiff (θ : ℝ) : |f θ-g θ| ≤ L*(1-r) := by
    simpa only [f, g, actualHarmonic_rescale_eq_regular s hs0 F, hcn, one_mul] using
      hL c r ⟨hr0, hr1.le⟩ θ
  have hn := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := E)
    (f := fun θ => f θ-g θ)
    (by rw [hE.2.2]; finiteness : volume E < ∞)
    (fun θ hθ => by simpa only [Real.norm_eq_abs] using hdiff θ)
  rw [integral_sub hfi hgi] at hn
  simp only [Real.norm_eq_abs, hreal] at hn
  rw [hval]
  change (∫ θ in E, f θ) ≤ 4*Real.sin h+2*h*L*(1-r)
  change (∫ θ in E, g θ) ≤ 4*Real.sin h at hb
  have hle := (le_abs_self ((∫ θ in E, f θ)-(∫ θ in E, g θ))).trans hn
  nlinarith

end SpringerLean

#print axioms SpringerLean.regularExterior_actualAngularTopValue_le_sine_add_radial_error
