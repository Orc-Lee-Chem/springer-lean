import SpringerLean.Round704ActualGappedOptimizer
import SpringerLean.Round713AngularCandidateTurn
import SpringerLean.Round27ShiftIntegral

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- An included interval controls the two masses; the excluded cut
margins keep both candidates inside the SAME angular turn. -/
theorem actualAngularTopValue_pair_ge_of_gapped_set
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r h q p δ ε : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hε0 : 0 ≤ ε) (hεδ : ε < δ) (hεh : ε < h) (hεpi : ε < Real.pi-h)
    (E : Set ℝ) (hEm : MeasurableSet E)
    (hmass : volume E = ENNReal.ofReal (2*h))
    (hin : Icc (p-δ) (p+δ) ⊆ E)
    (hout : E ⊆ Icc (q+δ) (q+2*Real.pi-δ)) :
    (∫ t in E, (c*actualHarmonic F (circleMap 0 r (t-ε))).re) +
      (∫ t in E, (c*actualHarmonic F (circleMap 0 r (t+ε))).re) ≤
      actualAngularTopValue F c r (h+ε) +
        actualAngularTopValue F c r (h-ε) := by
  let f : ℝ → ℝ := fun t => (c*actualHarmonic F (circleMap 0 r t)).re
  let W := verticalShiftWide E ε p
  let N := verticalShiftNarrow E ε p
  let M := verticalShiftMinus E ε
  let P := verticalShiftPlus E ε
  have hEb : Bornology.IsBounded E := (Metric.isBounded_Icc _ _).subset hout
  have hδ0 : 0 < δ := lt_of_le_of_lt hε0 hεδ
  have hMs : M ⊆ Ioc q (q+2*Real.pi) := by
    intro t ht
    have he := hout ht
    change q+δ ≤ t+ε ∧ t+ε ≤ q+2*Real.pi-δ at he
    exact ⟨by linarith [he.1], by linarith [he.2]⟩
  have hPs : P ⊆ Ioc q (q+2*Real.pi) := by
    intro t ht
    have he := hout ht
    change q+δ ≤ t-ε ∧ t-ε ≤ q+2*Real.pi-δ at he
    exact ⟨by linarith [he.1], by linarith [he.2]⟩
  have hWs : W ⊆ Ioc q (q+2*Real.pi) := by
    intro t ht
    rcases ht with ht | ht
    · exact hMs ht.1
    · exact hPs ht.1
  have hNs : N ⊆ Ioc q (q+2*Real.pi) := by
    intro t ht
    rcases ht with ht | ht
    · exact hPs ht.1
    · exact hMs ht.1
  have hWm : MeasurableSet W := verticalShiftWide_measurable hEm ε p
  have hNm : MeasurableSet N := verticalShiftNarrow_measurable hEm ε p
  have hMm : MeasurableSet M := verticalShiftMinus_measurable hEm ε
  have hPm : MeasurableSet P := verticalShiftPlus_measurable hEm ε
  have hreal : volume.real E = 2*h := by
    rw [Measure.real_def, hmass, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)]
  have hWreal := verticalShiftWide_measure E hEm hEb p δ ε hε0 hεδ hin
  have hNreal := verticalShiftNarrow_measure E hEm hEb p δ ε hε0 hεδ hin
  have hfin (S : Set ℝ) (hs : S ⊆ Ioc q (q+2*Real.pi)) : volume S ≠ ∞ :=
    ((Metric.isBounded_Ioc _ _).subset hs).measure_lt_top.ne
  have hWmass : volume W = ENNReal.ofReal (2*(h+ε)) := by
    apply (ENNReal.toReal_eq_toReal_iff' (hfin W hWs) (by finiteness)).mp
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*(h+ε))]
    change volume.real W = _
    change volume.real W = volume.real E+2*ε at hWreal
    linarith
  have hNmass : volume N = ENNReal.ofReal (2*(h-ε)) := by
    apply (ENNReal.toReal_eq_toReal_iff' (hfin N hNs) (by finiteness)).mp
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*(h-ε))]
    change volume.real N = _
    change volume.real N+2*ε = volume.real E at hNreal
    linarith
  have hf : Continuous f :=
    (actualHarmonic_angular_projection_analytic F hc c hr0 hr1).continuous
  have hi (S : Set ℝ) (hs : S ⊆ Ioc q (q+2*Real.pi)) : IntegrableOn f S :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (hs.trans Ioc_subset_Icc_self)
  have hpair : (∫ t in W, f t)+(∫ t in N, f t) =
      (∫ t in M, f t)+(∫ t in P, f t) :=
    setIntegral_pair_eq_of_indicator_count f W N M P hWm hNm hMm hPm
      (hi W hWs) (hi N hNs) (hi M hMs) (hi P hPs)
      (verticalShift_indicator_add E ε p)
  have hWbound := actualAngularTopValue_candidate_le_any_turn F hc c hr0 hr1
    (by linarith : 0 < h+ε) (by linarith : h+ε < Real.pi) q W hWm hWs hWmass
  have hNbound := actualAngularTopValue_candidate_le_any_turn F hc c hr0 hr1
    (by linarith : 0 < h-ε) (by linarith : h-ε < Real.pi) q N hNm hNs hNmass
  calc
    (∫ t in E, f (t-ε))+(∫ t in E, f (t+ε)) =
        (∫ t in M, f t)+(∫ t in P, f t) := by
      rw [setIntegral_verticalShiftMinus f E hEm ε,
        setIntegral_verticalShiftPlus f E hEm ε]
    _ = (∫ t in W, f t)+(∫ t in N, f t) := hpair.symm
    _ ≤ actualAngularTopValue F c r (h+ε)+actualAngularTopValue F c r (h-ε) :=
      add_le_add hWbound hNbound

/-- One optimizer and one positive radius work for EVERY small paired
shift and EVERY other interior radius.  All geometric premises of the
previous lemma are discharged for the SAME actual F. -/
theorem actualAngularTopValue_exists_uniform_paired_optimizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r h : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hh0 : 0 < h) (hhpi : h < Real.pi) :
    ∃ (E : Set ℝ) (δ : ℝ), MeasurableSet E ∧ Bornology.IsBounded E ∧
      0 < δ ∧ actualAngularTopValue F c r h =
        (∫ t in E, (c*actualHarmonic F (circleMap 0 r t)).re) ∧
      ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ r' : ℝ, 0 ≤ r' → r' < 1 →
        (∫ t in E, (c*actualHarmonic F (circleMap 0 r' (t-ε))).re) +
          (∫ t in E, (c*actualHarmonic F (circleMap 0 r' (t+ε))).re) ≤
          actualAngularTopValue F c r' (h+ε) +
            actualAngularTopValue F c r' (h-ε) := by
  obtain ⟨q, p, d, E, hd, hEm, hmass, hin, hout, hval⟩ :=
    actualAngularTopValue_exists_gapped_optimizer F hc c hr0 hr1 hh0 hhpi
  let δ := min d (min h (Real.pi-h))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨E, δ, hEm, (Metric.isBounded_Icc _ _).subset hout, hδ, hval, ?_⟩
  intro ε hε hεδ r' hr'0 hr'1
  have hεd : ε < d := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεh : ε < h := lt_of_lt_of_le hεδ
    ((min_le_right _ _).trans (min_le_left _ _))
  have hεpi : ε < Real.pi-h := lt_of_lt_of_le hεδ
    ((min_le_right _ _).trans (min_le_right _ _))
  exact actualAngularTopValue_pair_ge_of_gapped_set F hc c hr'0 hr'1 hh0 hhpi
    hε hεd hεh hεpi E hEm hmass hin hout

end SpringerLean

#print axioms SpringerLean.actualAngularTopValue_pair_ge_of_gapped_set
#print axioms SpringerLean.actualAngularTopValue_exists_uniform_paired_optimizer
