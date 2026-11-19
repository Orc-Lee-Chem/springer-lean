import SpringerLean.Round23Threshold

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- Cut the threshold level to the exact requested mass, retaining all
strictly cheaper points. -/
theorem measurable_threshold_candidate
    (f : ℝ → ℝ) (hf : Measurable f)
    (m : ℝ) (hm0 : 0 ≤ m) (ell : ℝ)
    (hUb : Bornology.IsBounded {t : ℝ | f t ≤ ell})
    (hLmass : volume {t : ℝ | f t < ell} ≤ ENNReal.ofReal m)
    (hUmass : ENNReal.ofReal m ≤ volume {t : ℝ | f t ≤ ell}) :
    ∃ E : Set ℝ, MeasurableSet E ∧ Bornology.IsBounded E ∧
      volume E = ENNReal.ofReal m ∧
      {t : ℝ | f t < ell} ⊆ E ∧ E ⊆ {t : ℝ | f t ≤ ell} := by
  let L : Set ℝ := {t | f t < ell}
  let U : Set ℝ := {t | f t ≤ ell}
  let S : Set ℝ := U \ L
  have hLmeas : MeasurableSet L := hf measurableSet_Iio
  have hUmeas : MeasurableSet U := hf measurableSet_Iic
  have hSmeas : MeasurableSet S := hUmeas.diff hLmeas
  have hLU : L ⊆ U := by
    intro t ht
    change f t < ell at ht
    change f t ≤ ell
    exact le_of_lt ht
  have hLb : Bornology.IsBounded L := hUb.subset hLU
  have hSb : Bornology.IsBounded S := hUb.subset diff_subset
  have hUfin : volume U ≠ ∞ := hUb.measure_lt_top.ne
  have hLfin : volume L ≠ ∞ := hLb.measure_lt_top.ne
  have hSfin : volume S ≠ ∞ := hSb.measure_lt_top.ne
  have hdisj : Disjoint L S := by
    apply disjoint_left.mpr
    intro t htL htS
    exact htS.2 htL
  have hunion : L ∪ S = U := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact hLU ht
      · exact ht.1
    · intro ht
      by_cases h : t ∈ L
      · exact Or.inl h
      · exact Or.inr ⟨ht, h⟩
  have hadd : volume.real U = volume.real L + volume.real S := by
    rw [← hunion]
    exact measureReal_union hdisj hSmeas hLfin hSfin
  have hmL : volume.real L ≤ m := by
    have h := (ENNReal.toReal_le_toReal hLfin
      (ENNReal.ofReal_ne_top)).2 hLmass
    simpa [Measure.real_def, ENNReal.toReal_ofReal hm0] using h
  have hmU : m ≤ volume.real U := by
    have h := (ENNReal.toReal_le_toReal
      (ENNReal.ofReal_ne_top) hUfin).2 hUmass
    simpa [Measure.real_def, ENNReal.toReal_ofReal hm0] using h
  let q : ℝ := m - volume.real L
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hqS : q ≤ volume.real S := by dsimp [q]; linarith
  obtain ⟨T, hTmeas, hTS, hTmass⟩ :=
    bounded_measurable_exists_subset_volume_eq S hSmeas hSb q hq0 hqS
  let E : Set ℝ := L ∪ T
  have hTE : T ⊆ U := hTS.trans diff_subset
  have hEb : Bornology.IsBounded E := hUb.subset (union_subset hLU hTE)
  have hETdisj : Disjoint L T := by
    apply disjoint_left.mpr
    intro t htL htT
    exact (hTS htT).2 htL
  have hTfin : volume T ≠ ∞ :=
    ((measure_mono hTS).trans_lt (lt_top_iff_ne_top.mpr hSfin)).ne
  have hEreal : volume.real E = m := by
    dsimp [E]
    rw [measureReal_union hETdisj hTmeas hLfin hTfin]
    have hTreal : volume.real T = q := by
      rw [Measure.real_def, hTmass, ENNReal.toReal_ofReal hq0]
    rw [hTreal]
    dsimp [q]
    ring
  refine ⟨E, hLmeas.union hTmeas, hEb, ?_, ?_, union_subset hLU hTE⟩
  · have hEfin : volume E ≠ ∞ := hEb.measure_lt_top.ne
    calc
      volume E = ENNReal.ofReal (volume.real E) := by
        exact (ENNReal.ofReal_toReal hEfin).symm
      _ = ENNReal.ofReal m := congrArg ENNReal.ofReal hEreal
  · exact subset_union_left

/-- A genuine bounded measurable vertical set of mass `2h` is obtained by
filling the actual potential's critical level, with all smaller values
included and no larger values included. -/
theorem regularExterior_vertical_threshold_candidate
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ (ell : ℝ) (E : Set ℝ), E ∈ verticalFeasible h ∧
      {t : ℝ | regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I) < ell} ⊆ E ∧
      E ⊆ {t : ℝ | regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I) ≤ ell} := by
  obtain ⟨ell, hL, hU⟩ :=
    regularExterior_vertical_threshold F hc hs0 hs1 ξ hξ a h hh
  let f : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  have hline : Measurable (fun t : ℝ =>
      (a : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hf : Measurable f :=
    (regularExterior_rotated_potential_measurable F hc hs0 hs1 ξ hξ).comp hline
  obtain ⟨E, hEmeas, hEb, hEmass, hLE, hEU⟩ :=
    measurable_threshold_candidate f hf (2 * h) (by linarith) ell
      (regularExterior_vertical_sublevel_measurable_bounded
        F hc hs0 hs1 ξ hξ a ell).2 hL hU
  exact ⟨ell, E, ⟨hEmeas, hEb, hEmass⟩, hLE, hEU⟩

end SpringerLean
