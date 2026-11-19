import SpringerLean.Round20Auxiliary

open MeasureTheory Set
open scoped Classical ENNReal

namespace SpringerLean

/-- The two translates of a vertical set, written as preimages. -/
def verticalShiftMinus (E : Set ℝ) (ε : ℝ) : Set ℝ :=
  {t | t + ε ∈ E}

def verticalShiftPlus (E : Set ℝ) (ε : ℝ) : Set ℝ :=
  {t | t - ε ∈ E}

/-- Give the left half-line to the negative translate and the right half-
line to the positive translate. -/
def verticalShiftWide (E : Set ℝ) (ε c : ℝ) : Set ℝ :=
  (verticalShiftMinus E ε ∩ Iio c) ∪
    (verticalShiftPlus E ε ∩ Ici c)

/-- The complementary split of the same two translates. -/
def verticalShiftNarrow (E : Set ℝ) (ε c : ℝ) : Set ℝ :=
  (verticalShiftPlus E ε ∩ Iio c) ∪
    (verticalShiftMinus E ε ∩ Ici c)

theorem verticalShiftMinus_measurable {E : Set ℝ} (hE : MeasurableSet E)
    (ε : ℝ) : MeasurableSet (verticalShiftMinus E ε) := by
  exact hE.preimage (measurable_id.add measurable_const)

theorem verticalShiftPlus_measurable {E : Set ℝ} (hE : MeasurableSet E)
    (ε : ℝ) : MeasurableSet (verticalShiftPlus E ε) := by
  exact hE.preimage (measurable_id.sub measurable_const)

theorem verticalShiftWide_measurable {E : Set ℝ} (hE : MeasurableSet E)
    (ε c : ℝ) : MeasurableSet (verticalShiftWide E ε c) := by
  exact ((verticalShiftMinus_measurable hE ε).inter measurableSet_Iio).union
    ((verticalShiftPlus_measurable hE ε).inter measurableSet_Ici)

theorem verticalShiftNarrow_measurable {E : Set ℝ} (hE : MeasurableSet E)
    (ε c : ℝ) : MeasurableSet (verticalShiftNarrow E ε c) := by
  exact ((verticalShiftPlus_measurable hE ε).inter measurableSet_Iio).union
    ((verticalShiftMinus_measurable hE ε).inter measurableSet_Ici)

/-- The two split sets have exactly the same pointwise multiplicity as
the two translates. This part needs no interval hypothesis. -/
theorem verticalShift_indicator_add (E : Set ℝ) (ε c t : ℝ) :
    (if t ∈ verticalShiftWide E ε c then (1 : ℕ) else 0) +
      (if t ∈ verticalShiftNarrow E ε c then (1 : ℕ) else 0) =
    (if t ∈ verticalShiftMinus E ε then (1 : ℕ) else 0) +
      (if t ∈ verticalShiftPlus E ε then (1 : ℕ) else 0) := by
  classical
  by_cases htc : t < c
  · have hnotge : ¬ c ≤ t := not_le_of_gt htc
    simp [verticalShiftWide, verticalShiftNarrow,
      verticalShiftMinus, verticalShiftPlus, htc, hnotge]
    rfl
  · have hge : c ≤ t := le_of_not_gt htc
    simp [verticalShiftWide, verticalShiftNarrow,
      verticalShiftMinus, verticalShiftPlus, htc, hge, add_comm]
    rfl

theorem verticalShiftMinus_left_measure (E : Set ℝ) (ε c : ℝ) :
    volume (verticalShiftMinus E ε ∩ Iio c) =
      volume (E ∩ Iio (c + ε)) := by
  have hset : verticalShiftMinus E ε ∩ Iio c =
      (fun t : ℝ => ε + t) ⁻¹' (E ∩ Iio (c + ε)) := by
    ext t
    constructor
    · rintro ⟨htE, htc⟩
      constructor
      · simpa [verticalShiftMinus, add_comm] using htE
      · change ε + t < c + ε
        change t < c at htc
        linarith
    · rintro ⟨htE, htc⟩
      constructor
      · simpa [verticalShiftMinus, add_comm] using htE
      · change ε + t < c + ε at htc
        change t < c
        linarith
  rw [hset, measure_preimage_add]

theorem verticalShiftPlus_left_measure (E : Set ℝ) (ε c : ℝ) :
    volume (verticalShiftPlus E ε ∩ Iio c) =
      volume (E ∩ Iio (c - ε)) := by
  have hset : verticalShiftPlus E ε ∩ Iio c =
      (fun t : ℝ => -ε + t) ⁻¹' (E ∩ Iio (c - ε)) := by
    ext t
    constructor
    · rintro ⟨htE, htc⟩
      constructor
      · simpa [verticalShiftPlus, sub_eq_add_neg, add_comm] using htE
      · change -ε + t < c - ε
        change t < c at htc
        linarith
    · rintro ⟨htE, htc⟩
      constructor
      · simpa [verticalShiftPlus, sub_eq_add_neg, add_comm] using htE
      · change -ε + t < c - ε at htc
        change t < c
        linarith
  rw [hset, measure_preimage_add]

/-- Under an actual interval-occupancy hypothesis, the negative translate
has exactly `2ε` more mass to the left of the split point. -/
theorem verticalShift_left_mass_gap
    (E : Set ℝ) (_hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c δ ε : ℝ) (hε : 0 ≤ ε) (hεδ : ε < δ)
    (hcore : Icc (c - δ) (c + δ) ⊆ E) :
    volume.real (verticalShiftMinus E ε ∩ Iio c) =
      volume.real (verticalShiftPlus E ε ∩ Iio c) + 2 * ε := by
  have hset : E ∩ Iio (c + ε) =
      (E ∩ Iio (c - ε)) ∪ Ico (c - ε) (c + ε) := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_union, mem_Ico]
    constructor
    · rintro ⟨htE, htU⟩
      by_cases htL : t < c - ε
      · exact Or.inl ⟨htE, htL⟩
      · exact Or.inr ⟨le_of_not_gt htL, htU⟩
    · rintro (ht | ht)
      · exact ⟨ht.1, by linarith [ht.2]⟩
      · refine ⟨hcore ?_, ht.2⟩
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hdisj : Disjoint (E ∩ Iio (c - ε)) (Ico (c - ε) (c + ε)) := by
    apply disjoint_left.mpr
    intro t ht₁ ht₂
    have hlt : t < c - ε := ht₁.2
    have hge : c - ε ≤ t := ht₂.1
    linarith
  have hfinite₁ : volume (E ∩ Iio (c - ε)) ≠ ∞ :=
    ((hEb.subset inter_subset_left).measure_lt_top).ne
  have hfinite₂ : volume (Ico (c - ε) (c + ε)) ≠ ∞ :=
    (Metric.isBounded_Ico _ _).measure_lt_top.ne
  have hsplit : volume.real (E ∩ Iio (c + ε)) =
      volume.real (E ∩ Iio (c - ε)) +
        volume.real (Ico (c - ε) (c + ε)) := by
    rw [hset]
    exact measureReal_union hdisj measurableSet_Ico hfinite₁ hfinite₂
  have hinterval : volume.real (Ico (c - ε) (c + ε)) = 2 * ε := by
    rw [Measure.real_def, Real.volume_Ico]
    have hnonneg : 0 ≤ (c + ε) - (c - ε) := by linarith
    rw [ENNReal.toReal_ofReal hnonneg]
    ring
  rw [Measure.real_def, verticalShiftMinus_left_measure,
    Measure.real_def, verticalShiftPlus_left_measure]
  rw [hinterval] at hsplit
  exact hsplit

/-- Splitting a finite real measure at a point, with the point assigned to
the right half-line. -/
private theorem verticalShift_split_measure
    (S : Set ℝ) (hS : MeasurableSet S) (hfin : volume S ≠ ∞) (c : ℝ) :
    volume.real S = volume.real (S ∩ Iio c) + volume.real (S ∩ Ici c) := by
  have hsplit : S = (S ∩ Iio c) ∪ (S ∩ Ici c) := by
    ext t
    simp only [mem_inter_iff, mem_union, mem_Iio, mem_Ici]
    constructor
    · intro ht
      rcases lt_or_ge t c with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hd : Disjoint (S ∩ Iio c) (S ∩ Ici c) := by
    apply disjoint_left.mpr
    intro t ht₁ ht₂
    exact (not_le_of_gt (show t < c from ht₁.2)) (show c ≤ t from ht₂.2)
  have hunion := measureReal_union hd (hS.inter measurableSet_Ici)
    ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfin)).ne
    ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfin)).ne
  rw [← hsplit] at hunion
  exact hunion

private theorem verticalShiftMinus_measure (E : Set ℝ) (ε : ℝ) :
    volume (verticalShiftMinus E ε) = volume E := by
  have hset : verticalShiftMinus E ε = (fun t : ℝ => ε + t) ⁻¹' E := by
    ext t
    simp [verticalShiftMinus, add_comm]
  rw [hset, measure_preimage_add]

private theorem verticalShiftPlus_measure (E : Set ℝ) (ε : ℝ) :
    volume (verticalShiftPlus E ε) = volume E := by
  have hset : verticalShiftPlus E ε = (fun t : ℝ => -ε + t) ⁻¹' E := by
    ext t
    simp [verticalShiftPlus, sub_eq_add_neg, add_comm]
  rw [hset, measure_preimage_add]

/-- The wide rearrangement has `2ε` more measure than the original set. -/
theorem verticalShiftWide_measure
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c δ ε : ℝ) (hε : 0 ≤ ε) (hεδ : ε < δ)
    (hcore : Icc (c - δ) (c + δ) ⊆ E) :
    volume.real (verticalShiftWide E ε c) = volume.real E + 2 * ε := by
  let Lm := verticalShiftMinus E ε ∩ Iio c
  let Lp := verticalShiftPlus E ε ∩ Iio c
  let Rm := verticalShiftMinus E ε ∩ Ici c
  let Rp := verticalShiftPlus E ε ∩ Ici c
  have hfin : volume E ≠ ∞ := hEb.measure_lt_top.ne
  have hfinm : volume (verticalShiftMinus E ε) ≠ ∞ := by
    rw [verticalShiftMinus_measure]
    exact hfin
  have hfinp : volume (verticalShiftPlus E ε) ≠ ∞ := by
    rw [verticalShiftPlus_measure]
    exact hfin
  have hgap : volume.real Lm = volume.real Lp + 2 * ε :=
    verticalShift_left_mass_gap E hE hEb c δ ε hε hεδ hcore
  have htotal : volume.real Lp + volume.real Rp = volume.real E := by
    have h := verticalShift_split_measure (verticalShiftPlus E ε)
      (verticalShiftPlus_measurable hE ε) hfinp c
    simp only [Measure.real_def, verticalShiftPlus_measure] at h
    exact h.symm
  have hd : Disjoint Lm Rp := by
    apply disjoint_left.mpr
    intro t ht₁ ht₂
    exact (not_le_of_gt (show t < c from ht₁.2)) (show c ≤ t from ht₂.2)
  have hwide : volume.real (verticalShiftWide E ε c) =
      volume.real Lm + volume.real Rp := by
    change volume.real (Lm ∪ Rp) = _
    exact measureReal_union hd ((verticalShiftPlus_measurable hE ε).inter measurableSet_Ici)
      ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfinm)).ne
      ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfinp)).ne
  rw [hwide, hgap]
  linarith

/-- The narrow rearrangement has `2ε` less measure than the original set. -/
theorem verticalShiftNarrow_measure
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c δ ε : ℝ) (hε : 0 ≤ ε) (hεδ : ε < δ)
    (hcore : Icc (c - δ) (c + δ) ⊆ E) :
    volume.real (verticalShiftNarrow E ε c) + 2 * ε = volume.real E := by
  let Lm := verticalShiftMinus E ε ∩ Iio c
  let Lp := verticalShiftPlus E ε ∩ Iio c
  let Rm := verticalShiftMinus E ε ∩ Ici c
  have hfin : volume E ≠ ∞ := hEb.measure_lt_top.ne
  have hfinm : volume (verticalShiftMinus E ε) ≠ ∞ := by
    rw [verticalShiftMinus_measure]
    exact hfin
  have hfinp : volume (verticalShiftPlus E ε) ≠ ∞ := by
    rw [verticalShiftPlus_measure]
    exact hfin
  have hgap : volume.real Lm = volume.real Lp + 2 * ε :=
    verticalShift_left_mass_gap E hE hEb c δ ε hε hεδ hcore
  have htotal : volume.real Lm + volume.real Rm = volume.real E := by
    have h := verticalShift_split_measure (verticalShiftMinus E ε)
      (verticalShiftMinus_measurable hE ε) hfinm c
    simp only [Measure.real_def, verticalShiftMinus_measure] at h
    exact h.symm
  have hd : Disjoint Lp Rm := by
    apply disjoint_left.mpr
    intro t ht₁ ht₂
    exact (not_le_of_gt (show t < c from ht₁.2)) (show c ≤ t from ht₂.2)
  have hnarrow : volume.real (verticalShiftNarrow E ε c) =
      volume.real Lp + volume.real Rm := by
    change volume.real (Lp ∪ Rm) = _
    exact measureReal_union hd ((verticalShiftMinus_measurable hE ε).inter measurableSet_Ici)
      ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfinp)).ne
      ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfinm)).ne
  rw [hnarrow]
  linarith

end SpringerLean
