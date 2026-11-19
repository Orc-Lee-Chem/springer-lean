import SpringerLean.Round28AuxHorizontal

open MeasureTheory Set Metric
open scoped ENNReal

namespace SpringerLean

/-- Enlarge a bounded feasible vertical set to a larger prescribed mass
inside one fixed interval, using the exact measurable mass-cut lemma. -/
theorem verticalFeasible_extend_inside_Icc
    (T h h' : ℝ) (hT : 0 ≤ T) (hh : 0 ≤ h)
    (hhh' : h ≤ h') (hh'T : h' ≤ T)
    (E : Set ℝ) (hE : E ∈ verticalFeasible h)
    (hET : E ⊆ Icc (-T) T) :
    ∃ D ∈ verticalFeasible h', E ⊆ D ∧ D ⊆ Icc (-T) T := by
  let J : Set ℝ := Icc (-T) T
  let S : Set ℝ := J \ E
  let q : ℝ := 2 * (h' - h)
  have hJfin : volume J ≠ ∞ := (isBounded_Icc (-T) T).measure_lt_top.ne
  have hEfin : volume E ≠ ∞ := by rw [hE.2.2]; finiteness
  have hJreal : volume.real J = 2 * T := by
    dsimp [J]
    rw [Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hEreal : volume.real E = 2 * h := by
    rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith)]
  have hSreal : volume.real S = 2 * (T - h) := by
    dsimp [S]
    rw [measureReal_sdiff hET hE.1 hJfin, hJreal, hEreal]
    ring
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hqS : q ≤ volume.real S := by rw [hSreal]; dsimp [q]; linarith
  have hSm : MeasurableSet S := measurableSet_Icc.diff hE.1
  have hSb : Bornology.IsBounded S :=
    (isBounded_Icc (-T) T).subset diff_subset
  obtain ⟨Z, hZm, hZS, hZmass⟩ :=
    bounded_measurable_exists_subset_volume_eq S hSm hSb q hq0 hqS
  let D : Set ℝ := E ∪ Z
  have hZfin : volume Z ≠ ∞ := by rw [hZmass]; finiteness
  have hDisj : Disjoint E Z := by
    apply disjoint_left.mpr
    intro t htE htZ
    exact (hZS htZ).2 htE
  have hDsub : D ⊆ J := by
    dsimp [D]
    exact union_subset hET (hZS.trans diff_subset)
  have hDb : Bornology.IsBounded D := (isBounded_Icc (-T) T).subset hDsub
  have hDreal : volume.real D = 2 * h' := by
    dsimp [D]
    rw [measureReal_union hDisj hZm hEfin hZfin, hEreal,
      Measure.real_def, hZmass, ENNReal.toReal_ofReal hq0]
    dsimp [q]
    ring
  have hDfin : volume D ≠ ∞ := hDb.measure_lt_top.ne
  have hDmass : volume D = ENNReal.ofReal (2 * h') := by
    calc
      volume D = ENNReal.ofReal (volume.real D) :=
        (ENNReal.ofReal_toReal hDfin).symm
      _ = ENNReal.ofReal (2 * h') := by rw [hDreal]
  refine ⟨D, ⟨hE.1.union hZm, hDb, hDmass⟩, ?_, hDsub⟩
  exact subset_union_left

/-- Reduce a feasible vertical set to any smaller nonnegative height by
an exact measurable cut. -/
theorem verticalFeasible_shrink
    (h h' : ℝ) (hh' : 0 ≤ h') (hhh' : h' ≤ h)
    (E : Set ℝ) (hE : E ∈ verticalFeasible h) :
    ∃ D ∈ verticalFeasible h', D ⊆ E := by
  have hEb : Bornology.IsBounded E := hE.2.1
  have hEreal : volume.real E = 2 * h := by
    rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith)]
  obtain ⟨D, hDm, hDE, hDmass⟩ :=
    bounded_measurable_exists_subset_volume_eq E hE.1 hEb (2 * h')
      (by linarith) (by rw [hEreal]; linarith)
  exact ⟨D, ⟨hDm, hEb.subset hDE, hDmass⟩, hDE⟩

end SpringerLean