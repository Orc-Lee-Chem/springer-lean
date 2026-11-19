import SpringerLean.Round690ActualAngularTopValue
import SpringerLean.Round689PeriodicThreshold

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- A dual upper bound, valid at EVERY threshold. No optimum threshold
is assumed here. Raw angular length is used throughout. -/
theorem actualAngularTopValue_le_threshold
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) (ell : ℝ) :
    actualAngularTopValue F c r h ≤ 2*h*ell +
      ∫ t in Ioc 0 (2*Real.pi),
        max ((c*actualHarmonic F (circleMap 0 r t)).re-ell) 0 := by
  obtain ⟨E, hE, hval, hmax⟩ := actualAngularTopValue_attained F hc c hr0 hr1 hh0 hhpi
  have hreal : volume.real E = 2*h := by
    rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)]
  have hs : E ⊆ Ioc 0 (0+2*Real.pi) := by simpa only [zero_add] using hE.2.1
  have hu := actualHarmonic_angular_setIntegral_le_threshold F hc c hr0 hr1 ell 0 E hE.1 hs
  rw [hreal] at hu
  rw [hval]
  convert hu using 1 <;> ring

/-- An exact top-level mass gives equality in the dual bound. This is an
interface lemma; the next theorem constructs that threshold for actual F. -/
theorem actualAngularTopValue_eq_threshold_of_mass
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) (ell : ℝ)
    (hmass : volume ({t : ℝ | ell ≤ (c*actualHarmonic F (circleMap 0 r t)).re} ∩
      Ioc 0 (2*Real.pi)) = ENNReal.ofReal (2*h)) :
    actualAngularTopValue F c r h = 2*h*ell +
      ∫ t in Ioc 0 (2*Real.pi),
        max ((c*actualHarmonic F (circleMap 0 r t)).re-ell) 0 := by
  let f : ℝ → ℝ := fun t => (c*actualHarmonic F (circleMap 0 r t)).re
  let I : Set ℝ := Ioc 0 (2*Real.pi)
  let μ : Measure ℝ := volume.restrict I
  let C : Set ℝ := {t | ell ≤ f t}
  let E : Set ℝ := C ∩ I
  have hcF : Continuous f :=
    (actualHarmonic_angular_projection_analytic F hc c hr0 hr1).continuous
  have hInt : Integrable f μ :=
    (hcF.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hPos : Integrable (fun t => max (f t-ell) 0) μ :=
    (((hcF.sub continuous_const).max continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hCm : MeasurableSet C := measurableSet_le measurable_const hcF.measurable
  have hEm : MeasurableSet E := hCm.inter measurableSet_Ioc
  have hE : E ∈ angularTopFeasible h := ⟨hEm, inter_subset_right, hmass⟩
  have hCmeasure : μ.restrict C = volume.restrict E := Measure.restrict_restrict hCm
  have hCmass : μ C = ENNReal.ofReal (2*h) := by
    simpa only [μ, Measure.restrict_apply hCm] using hmass
  have hCreal : μ.real C = 2*h := by
    rw [Measure.real_def, hCmass, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)]
  have hp := integral_positivePart_eq_superlevel_sub f ell hCm hInt hPos
  change (∫ t in I, max (f t-ell) 0) =
    (∫ t, f t ∂(μ.restrict C))-ell*μ.real C at hp
  rw [hCmeasure, hCreal] at hp
  have hcost : (∫ t in E, f t) =
      2*h*ell + ∫ t in I, max (f t-ell) 0 := by linarith
  apply le_antisymm (actualAngularTopValue_le_threshold F hc c hr0 hr1 hh0 hhpi ell)
  rw [← hcost]
  exact actualAngularTopValue_candidate_le F hc c hr0 hr1 hh0 hhpi E hE

/-- A bounded dual optimizer for the SAME actual F exists at every
interior angular mass. Its threshold is bounded by the already proved
pointwise estimate. Constant projections are handled without a false
null-level premise. -/
theorem actualAngularTopValue_exists_bounded_threshold
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    ∃ ell : ℝ, |ell| ≤ ‖c‖*(2*r) ∧
      actualAngularTopValue F c r h = 2*h*ell +
        ∫ t in Ioc 0 (2*Real.pi),
          max ((c*actualHarmonic F (circleMap 0 r t)).re-ell) 0 := by
  let f : ℝ → ℝ := fun t => (c*actualHarmonic F (circleMap 0 r t)).re
  let B : ℝ := ‖c‖*(2*r)
  let I : Set ℝ := Ioc 0 (2*Real.pi)
  let μ : Measure ℝ := volume.restrict I
  have hcont : Continuous f :=
    (actualHarmonic_angular_projection_analytic F hc c hr0 hr1).continuous
  have hbound (t : ℝ) : |f t| ≤ B :=
    actualHarmonic_angular_projection_abs_le F hc c hr0 hr1 t
  have hInt : Integrable f μ :=
    (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hmpos : 0 < ENNReal.ofReal (2*h) := ENNReal.ofReal_pos.mpr (by linarith)
  have htotal : μ univ = ENNReal.ofReal (2*Real.pi) := by
    simp only [μ, I, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  have hmlt : ENNReal.ofReal (2*h) < μ univ := by
    rw [htotal]
    by_contra hn
    have hle := ENNReal.toReal_mono
      (by finiteness : ENNReal.ofReal (2*h) ≠ ∞) (le_of_not_gt hn)
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.pi),
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)] at hle
    linarith
  rcases actualHarmonic_angular_projection_constant_or_level_null F hc c hr0 hr1 with
    hconstant | hlevels
  · obtain ⟨b, hb⟩ := hconstant
    have hfun : f = fun _ => b := funext hb
    have hbnd : |b| ≤ B := by simpa only [hfun] using hbound 0
    obtain ⟨E, hE, hval, hmax⟩ := actualAngularTopValue_attained F hc c hr0 hr1 hh0 hhpi
    have hreal : volume.real E = 2*h := by
      rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)]
    have hcost : actualAngularTopValue F c r h = 2*h*b := by
      rw [hval]
      change (∫ t in E, f t) = _
      rw [hfun, setIntegral_const]
      simp only [smul_eq_mul, hreal]
    refine ⟨b, hbnd, ?_⟩
    change actualAngularTopValue F c r h = 2*h*b + ∫ t in I, max (f t-b) 0
    simp only [hfun, sub_self, max_self, integral_zero, add_zero, hcost]
  · have hlevelsμ (a : ℝ) : μ {t | f t = a} = 0 := by
      apply le_antisymm _ bot_le
      calc
        μ {t | f t = a} ≤ volume {t | f t = a} := Measure.restrict_apply_le _ _
        _ = 0 := hlevels a
    have hfull : ∃ R : ℝ, ENNReal.ofReal (2*h) ≤ μ {t | -f t ≤ R} := by
      refine ⟨B, ?_⟩
      have heq : {t | -f t ≤ B} = univ := by
        ext t
        simp only [mem_setOf_eq, mem_univ, iff_true]
        linarith [(abs_le.mp (hbound t)).1]
      rw [heq]
      exact hmlt.le
    obtain ⟨ell, hCm, hCmass, hmax⟩ := finiteMeasure_exists_top_set μ f
      hcont.measurable hInt B (fun t => (abs_le.mp (hbound t)).2)
      hlevelsμ (ENNReal.ofReal (2*h)) hmpos hfull
    have hellhi : ell ≤ B := by
      by_contra hn
      have heq : {t | ell ≤ f t} = ∅ := by
        ext t
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact not_le.mpr (lt_of_le_of_lt (abs_le.mp (hbound t)).2 (lt_of_not_ge hn))
      rw [heq, measure_empty] at hCmass
      exact (ne_of_gt hmpos) hCmass.symm
    have helllo : -B ≤ ell := by
      by_contra hn
      have heq : {t | ell ≤ f t} = univ := by
        ext t
        simp only [mem_setOf_eq, mem_univ, iff_true]
        linarith [(abs_le.mp (hbound t)).1]
      rw [heq] at hCmass
      exact (ne_of_lt hmlt) hCmass.symm
    refine ⟨ell, abs_le.mpr ⟨helllo, hellhi⟩, ?_⟩
    apply actualAngularTopValue_eq_threshold_of_mass F hc c hr0 hr1 hh0 hhpi ell
    simpa only [μ, Measure.restrict_apply hCm] using hCmass

end SpringerLean
