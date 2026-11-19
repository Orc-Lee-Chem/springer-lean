import SpringerLean.Round12Projection

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- Directional projection support for the actual harmonic filling and the
actual omitted set. The witness is obtained by compactness of the nested
unscaled omitted sets, not by assuming radial boundary values. -/
theorem actualHarmonic_projection_omitted_witness
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ w ∈ exteriorOmitted F,
      (c * actualHarmonic F z).re ≤ (c * w).re := by
  classical
  let witness (n : ℕ) :=
    regular_projection_omittedAtScale_witness F hc
      (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) c hz
  let w : ℕ → ℂ := fun n => (witness n).choose
  have hwmem (n : ℕ) :
      w n ∈ exteriorOmittedAtScale F (omittedScaleSeq n) :=
    (witness n).choose_spec.1
  have hwle (n : ℕ) :
      (c * regularHarmonic (omittedScaleSeq n) F z).re ≤
        omittedScaleSeq n * (c * w n).re :=
    (witness n).choose_spec.2
  have hw0 (n : ℕ) :
      w n ∈ exteriorOmittedAtScale F (omittedScaleSeq 0) :=
    exteriorOmittedAtScale_antitone F (omittedScaleSeq_pos 0)
      (omittedScaleSeq_mono (Nat.zero_le n)) (hwmem n)
  obtain ⟨v, hv0, φ, hφmono, hφlim⟩ :=
    (exteriorOmittedAtScale_isCompact F hc
      (omittedScaleSeq_pos 0) (omittedScaleSeq_lt_one 0)).tendsto_subseq hw0
  have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hvin (j : ℕ) :
      v ∈ exteriorOmittedAtScale F (omittedScaleSeq j) := by
    have htail : ∀ᶠ n in atTop,
        w (φ n) ∈ exteriorOmittedAtScale F (omittedScaleSeq j) := by
      filter_upwards [hφtop.eventually (eventually_ge_atTop j)] with n hn
      exact exteriorOmittedAtScale_antitone F
        (omittedScaleSeq_pos j) (omittedScaleSeq_mono hn) (hwmem (φ n))
    exact (exteriorOmittedAtScale_isCompact F hc
      (omittedScaleSeq_pos j) (omittedScaleSeq_lt_one j)).isClosed.mem_of_tendsto
        hφlim htail
  have hv : v ∈ exteriorOmitted F := by
    rw [← exteriorOmitted_eq_iInter_scaleSeq F]
    exact Set.mem_iInter.mpr hvin
  refine ⟨v, hv, ?_⟩
  have hScale : Tendsto omittedScaleSeq atTop (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨omittedScaleSeq_tendsto_one,
      Filter.Eventually.of_forall (fun n => omittedScaleSeq_lt_one n)⟩
  have hReg : Tendsto
      (fun n => regularHarmonic (omittedScaleSeq (φ n)) F z)
      atTop (𝓝 (actualHarmonic F z)) :=
    (regularHarmonic_tendsto F hc hz).comp (hScale.comp hφtop)
  have hLeft : Tendsto
      (fun n => (c * regularHarmonic (omittedScaleSeq (φ n)) F z).re)
      atTop (𝓝 ((c * actualHarmonic F z).re)) := by
    exact Complex.continuous_re.tendsto _ |>.comp
      ((tendsto_const_nhds (x := c)).mul hReg)
  have hRight : Tendsto
      (fun n => omittedScaleSeq (φ n) * (c * w (φ n)).re)
      atTop (𝓝 ((c * v).re)) := by
    have hscale' := omittedScaleSeq_tendsto_one.comp hφtop
    have hproj : Tendsto (fun n => (c * w (φ n)).re)
        atTop (𝓝 ((c * v).re)) :=
      Complex.continuous_re.tendsto _ |>.comp
        ((tendsto_const_nhds (x := c)).mul hφlim)
    simpa only [Function.comp_def, one_mul] using hscale'.mul hproj
  exact le_of_tendsto_of_tendsto hLeft hRight
    (Filter.Eventually.of_forall (fun n => hwle (φ n)))

/-- The actual omitted set has a point; no boundary extension of `F` is assumed. -/
theorem exteriorOmitted_nonempty (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) : (exteriorOmitted F).Nonempty := by
  obtain ⟨w, hw, _⟩ :=
    actualHarmonic_projection_omitted_witness F hc (0 : ℂ)
      (z := 0) (by simp)
  exact ⟨w, hw⟩

end SpringerLean
