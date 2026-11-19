import SpringerLean.Round703PeriodicGappedTop
import SpringerLean.Round691AngularTopDual

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- A maximizing representative for the SAME actual projection has a
genuine included interval and a genuine gap at the angular cut. One delta
works for every sufficiently small paired shift. Constant projections are
handled separately, so no false null-level assertion is needed. -/
theorem actualAngularTopValue_exists_gapped_optimizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    ∃ (q p δ : ℝ) (E : Set ℝ), 0 < δ ∧ MeasurableSet E ∧
      volume E = ENNReal.ofReal (2*h) ∧
      Icc (p-δ) (p+δ) ⊆ E ∧ E ⊆ Icc (q+δ) (q+2*Real.pi-δ) ∧
      actualAngularTopValue F c r h =
        ∫ t in E, (c*actualHarmonic F (circleMap 0 r t)).re := by
  classical
  let f : ℝ → ℝ := fun t => (c*actualHarmonic F (circleMap 0 r t)).re
  have hf : Continuous f :=
    (actualHarmonic_angular_projection_analytic F hc c hr0 hr1).continuous
  have hp : Function.Periodic f (2*Real.pi) :=
    actualHarmonic_angular_projection_periodic F c r
  rcases actualHarmonic_angular_projection_constant_or_level_null F hc c hr0 hr1 with
    hconstant | hlevels
  · obtain ⟨b, hb⟩ := hconstant
    let E : Set ℝ := Icc (Real.pi-h) (Real.pi+h)
    let δ : ℝ := min (h/2) ((Real.pi-h)/2)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (by linarith) (by linarith)
    have hδh : δ ≤ h/2 := min_le_left _ _
    have hδpi : δ ≤ (Real.pi-h)/2 := min_le_right _ _
    have hEm : MeasurableSet E := measurableSet_Icc
    have hmass : volume E = ENNReal.ofReal (2*h) := by
      rw [Real.volume_Icc]
      congr 1
      ring
    have hsub : E ⊆ Ioc 0 (2*Real.pi) := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨0, Real.pi, δ, E, hδ, hEm, hmass, ?_, ?_, ?_⟩
    · intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · obtain ⟨A, hA, hval, hmax⟩ :=
        actualAngularTopValue_attained F hc c hr0 hr1 hh0 hhpi
      have hfun : f = fun _ => b := funext hb
      rw [hval]
      change (∫ t in A, f t) = ∫ t in E, f t
      simp only [hfun, setIntegral_const, Measure.real_def, hA.2.2, hmass]
  · let I : Set ℝ := Ioc 0 (2*Real.pi)
    let μ : Measure ℝ := volume.restrict I
    let B : ℝ := ‖c‖*(2*r)
    have hbound (t : ℝ) : |f t| ≤ B :=
      actualHarmonic_angular_projection_abs_le F hc c hr0 hr1 t
    have hInt : Integrable f μ :=
      (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hlevelsμ (ell : ℝ) : μ {t | f t = ell} = 0 := by
      exact le_antisymm ((Measure.restrict_apply_le _ _).trans (le_of_eq (hlevels ell))) bot_le
    have hmassFull : ENNReal.ofReal (2*h) ≤ μ univ := by
      change ENNReal.ofReal (2*h) ≤ (volume.restrict (Ioc 0 (2*Real.pi))) univ
      rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hfull : ∃ R : ℝ, ENNReal.ofReal (2*h) ≤ μ {t | -f t ≤ R} := by
      refine ⟨B, ?_⟩
      have heq : {t | -f t ≤ B} = univ := by
        ext t
        simp only [mem_setOf_eq, mem_univ, iff_true]
        linarith [(abs_le.mp (hbound t)).1]
      rwa [heq]
    obtain ⟨ell, hCm, hCmass, hmax⟩ := finiteMeasure_exists_top_set μ f
      hf.measurable hInt B (fun t => (abs_le.mp (hbound t)).2)
      hlevelsμ (ENNReal.ofReal (2*h)) (ENNReal.ofReal_pos.mpr (by linarith)) hfull
    have hmass0 : volume ({t | ell ≤ f t} ∩ I) = ENNReal.ofReal (2*h) := by
      simpa only [μ, Measure.restrict_apply hCm] using hCmass
    obtain ⟨q, p, δ, E, hδ, hEeq, hEm, hmass, hin, hout⟩ :=
      periodic_superlevel_exists_gapped_representative f hf (by positivity : 0 < 2*Real.pi)
        (by linarith : 0 < 2*h) (by linarith : 2*h < 2*Real.pi) hp ell
        (hlevels ell) hmass0
    refine ⟨q, p, δ, E, hδ, hEm, hmass, hin, hout, ?_⟩
    let Iq : Set ℝ := Ioc q (q+2*Real.pi)
    let μq : Measure ℝ := volume.restrict Iq
    let C : Set ℝ := {t | ell ≤ f t}
    have hIntq : Integrable f μq :=
      (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hPosq : Integrable (fun t => max (f t-ell) 0) μq :=
      (((hf.sub continuous_const).max continuous_const).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hCmeasure : μq.restrict C = volume.restrict E := by
      rw [show μq = volume.restrict Iq from rfl, Measure.restrict_restrict hCm]
      exact congrArg volume.restrict hEeq.symm
    have hCmassi : μq C = ENNReal.ofReal (2*h) := by
      change (volume.restrict Iq) C = _
      rw [Measure.restrict_apply hCm]
      simpa only [hEeq] using hmass
    have hCreal : μq.real C = 2*h := by
      rw [Measure.real_def, hCmassi, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)]
    have hpos := integral_positivePart_eq_superlevel_sub f ell hCm hIntq hPosq
    change (∫ t in Iq, max (f t-ell) 0) =
      (∫ t, f t ∂(μq.restrict C))-ell*μq.real C at hpos
    rw [hCmeasure, hCreal,
      periodic_positivePart_turn_integral f (by positivity : 0 < 2*Real.pi) hp ell q] at hpos
    have hval := actualAngularTopValue_eq_threshold_of_mass F hc c hr0 hr1 hh0 hhpi ell hmass0
    change actualAngularTopValue F c r h = ∫ t in E, f t
    change actualAngularTopValue F c r h = 2*h*ell +
      ∫ t in I, max (f t-ell) 0 at hval
    linarith

end SpringerLean

#print axioms SpringerLean.actualAngularTopValue_exists_gapped_optimizer
