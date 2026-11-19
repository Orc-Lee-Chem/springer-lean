import SpringerLean.Round27ShiftIntegral

open MeasureTheory Set
open scoped Classical

namespace SpringerLean

private theorem verticalShiftMinus_Icc (h ε : ℝ) :
    verticalShiftMinus (Icc (-h) h) ε = Icc (-h - ε) (h - ε) := by
  ext t
  simp only [verticalShiftMinus, mem_setOf_eq, mem_Icc]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩

private theorem verticalShiftPlus_Icc (h ε : ℝ) :
    verticalShiftPlus (Icc (-h) h) ε = Icc (-h + ε) (h + ε) := by
  ext t
  simp only [verticalShiftPlus, mem_setOf_eq, mem_Icc]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩

/-- The two translates of a centered interval have the same pointwise
multiplicity as the wider and narrower centered intervals. -/
theorem centered_interval_shift_indicator_count
    (h ε t : ℝ) (hε : 0 ≤ ε) (hεh : ε ≤ h) :
    (if t ∈ verticalShiftMinus (Icc (-h) h) ε then (1 : ℕ) else 0) +
      (if t ∈ verticalShiftPlus (Icc (-h) h) ε then 1 else 0) =
    (if t ∈ Icc (-(h + ε)) (h + ε) then 1 else 0) +
      (if t ∈ Icc (-(h - ε)) (h - ε) then 1 else 0) := by
  rw [verticalShiftMinus_Icc, verticalShiftPlus_Icc]
  have hwide :
      (t ∈ Icc (-h - ε) (h - ε) ∨ t ∈ Icc (-h + ε) (h + ε)) ↔
        t ∈ Icc (-(h + ε)) (h + ε) := by
    constructor
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      by_cases ht : t ≤ h - ε
      · left
        exact ⟨by linarith, ht⟩
      · right
        exact ⟨by linarith, h₂⟩
  have hnarrow :
      (t ∈ Icc (-h - ε) (h - ε) ∧ t ∈ Icc (-h + ε) (h + ε)) ↔
        t ∈ Icc (-(h - ε)) (h - ε) := by
    constructor
    · rintro ⟨⟨_, hu⟩, ⟨hl, _⟩⟩
      exact ⟨by linarith, hu⟩
    · rintro ⟨hl, hu⟩
      exact ⟨⟨by linarith, hu⟩, ⟨by linarith, by linarith⟩⟩
  by_cases hm : t ∈ Icc (-h - ε) (h - ε)
  · by_cases hp : t ∈ Icc (-h + ε) (h + ε)
    · have hw := hwide.mp (Or.inl hm)
      have hn := hnarrow.mp ⟨hm, hp⟩
      simp only [if_pos hm, if_pos hp, if_pos hw, if_pos hn]
    · have hw := hwide.mp (Or.inl hm)
      have hn : t ∉ Icc (-(h - ε)) (h - ε) := by
        intro ht
        exact hp (hnarrow.mpr ht).2
      simp only [if_pos hm, if_neg hp, if_pos hw, if_neg hn, add_zero]
  · by_cases hp : t ∈ Icc (-h + ε) (h + ε)
    · have hw := hwide.mp (Or.inr hp)
      have hn : t ∉ Icc (-(h - ε)) (h - ε) := by
        intro ht
        exact hm (hnarrow.mpr ht).1
      simp only [if_neg hm, if_pos hp, if_pos hw, if_neg hn, zero_add, add_zero]
    · have hw : t ∉ Icc (-(h + ε)) (h + ε) := by
        intro ht
        rcases hwide.mpr ht with ht | ht
        · exact hm ht
        · exact hp ht
      have hn : t ∉ Icc (-(h - ε)) (h - ε) := by
        intro ht
        exact hm (hnarrow.mpr ht).1
      simp only [if_neg hm, if_neg hp, if_neg hw, if_neg hn, add_zero]

/-- The interval multiplicity identity after integrating a function that
is integrable on every compact real interval. -/
theorem centered_interval_shift_integral_pair
    (f : ℝ → ℝ) (h ε : ℝ) (hε : 0 ≤ ε) (hεh : ε ≤ h)
    (hf : ∀ a b : ℝ, IntegrableOn f (Icc a b)) :
    (∫ t in verticalShiftMinus (Icc (-h) h) ε, f t) +
      (∫ t in verticalShiftPlus (Icc (-h) h) ε, f t) =
    (∫ t in Icc (-(h + ε)) (h + ε), f t) +
      (∫ t in Icc (-(h - ε)) (h - ε), f t) := by
  have hPm : MeasurableSet (verticalShiftMinus (Icc (-h) h) ε) :=
    verticalShiftMinus_measurable measurableSet_Icc ε
  have hQm : MeasurableSet (verticalShiftPlus (Icc (-h) h) ε) :=
    verticalShiftPlus_measurable measurableSet_Icc ε
  apply setIntegral_pair_eq_of_indicator_count f
    (verticalShiftMinus (Icc (-h) h) ε)
    (verticalShiftPlus (Icc (-h) h) ε)
    (Icc (-(h + ε)) (h + ε)) (Icc (-(h - ε)) (h - ε))
    hPm hQm measurableSet_Icc measurableSet_Icc
  · rw [verticalShiftMinus_Icc]
    exact hf _ _
  · rw [verticalShiftPlus_Icc]
    exact hf _ _
  · exact hf _ _
  · exact hf _ _
  · intro t
    have hc := centered_interval_shift_indicator_count h ε t hε hεh
    by_cases hm : t ∈ verticalShiftMinus (Icc (-h) h) ε <;>
      by_cases hp : t ∈ verticalShiftPlus (Icc (-h) h) ε <;>
      by_cases hw : t ∈ Icc (-(h + ε)) (h + ε) <;>
      by_cases hn : t ∈ Icc (-(h - ε)) (h - ε) <;>
      simp only [hm, hp, hw, hn, ↓reduceIte] at hc ⊢ <;> exact hc

end SpringerLean
