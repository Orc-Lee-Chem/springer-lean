import SpringerLean.Round23Minimum

open MeasureTheory Set
open scoped ENNReal Classical

namespace SpringerLean

/-- If two bounded measurable sets have equal mass and their difference
contains at least `d` mass, redistribute exactly `d` mass between them.
The multiplicity identity holds pointwise. -/
theorem equal_mass_sets_redistribute
    (P Q : Set ℝ) (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (hPb : Bornology.IsBounded P) (hQb : Bornology.IsBounded Q)
    (m d : ℝ) (hmP : volume.real P = m) (hmQ : volume.real Q = m)
    (hd0 : 0 ≤ d) (hd : d ≤ volume.real (Q \ P)) :
    ∃ A B : Set ℝ,
      MeasurableSet A ∧ MeasurableSet B ∧
      Bornology.IsBounded A ∧ Bornology.IsBounded B ∧
      volume.real A = m + d ∧ volume.real B = m - d ∧
      ∀ t : ℝ,
        (if t ∈ A then (1 : ℕ) else 0) +
          (if t ∈ B then (1 : ℕ) else 0) =
        (if t ∈ P then (1 : ℕ) else 0) +
          (if t ∈ Q then (1 : ℕ) else 0) := by
  let S : Set ℝ := Q \ P
  have hSmeas : MeasurableSet S := hQ.diff hP
  have hSb : Bornology.IsBounded S := hQb.subset sdiff_subset
  obtain ⟨T, hTmeas, hTS, hTmass⟩ :=
    bounded_measurable_exists_subset_volume_eq S hSmeas hSb d hd0 hd
  let A : Set ℝ := P ∪ T
  let B : Set ℝ := Q \ T
  have hTQ : T ⊆ Q := hTS.trans sdiff_subset
  have hTP : Disjoint P T := by
    apply disjoint_left.mpr
    intro t htP htT
    exact (hTS htT).2 htP
  have hTfin : volume T ≠ ∞ :=
    ((measure_mono hTS).trans_lt hSb.measure_lt_top).ne
  have hPfin : volume P ≠ ∞ := hPb.measure_lt_top.ne
  have hQfin : volume Q ≠ ∞ := hQb.measure_lt_top.ne
  have hTreal : volume.real T = d := by
    rw [Measure.real_def, hTmass, ENNReal.toReal_ofReal hd0]
  refine ⟨A, B, hP.union hTmeas, hQ.diff hTmeas,
    hPb.union (hQb.subset hTQ), hQb.subset sdiff_subset, ?_, ?_, ?_⟩
  · dsimp [A]
    rw [measureReal_union hTP hTmeas hPfin hTfin, hmP, hTreal]
  · dsimp [B]
    rw [measureReal_sdiff hTQ hTmeas hQfin, hmQ, hTreal]
  · intro t
    by_cases htT : t ∈ T
    · have htQ : t ∈ Q := hTQ htT
      have htP : t ∉ P := (hTS htT).2
      simp [A, B, htT, htQ, htP]
    · simp [A, B, htT]

end SpringerLean
