import SpringerLean.Round25Optimizer

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- Two finite equal-mass sets lose the same mass in either difference
direction. -/
theorem measureReal_sdiff_eq_sdiff_of_eq_measureReal
    (P Q : Set ℝ) (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (hPfin : volume P ≠ ∞) (hQfin : volume Q ≠ ∞)
    (heq : volume.real P = volume.real Q) :
    volume.real (P \ Q) = volume.real (Q \ P) := by
  rw [measureReal_sdiff' hQ hPfin hQfin,
    measureReal_sdiff' hP hQfin hPfin, union_comm, heq]

/-- The left translate minus the right translate is exactly the translated
version of `E \ (E+d)`, with `d=2ε`. -/
theorem verticalShiftMinus_sdiff_verticalShiftPlus_volume
    (E : Set ℝ) (ε : ℝ) :
    volume (verticalShiftMinus E ε \ verticalShiftPlus E ε) =
      volume (E \ verticalShiftPlus E (2 * ε)) := by
  have hset : verticalShiftMinus E ε \ verticalShiftPlus E ε =
      (fun t : ℝ => ε + t) ⁻¹' (E \ verticalShiftPlus E (2 * ε)) := by
    ext t
    simp only [mem_diff, mem_preimage]
    constructor
    · rintro ⟨htP, htQ⟩
      refine ⟨?_, ?_⟩
      · simpa only [verticalShiftMinus, mem_setOf_eq, add_comm] using htP
      · change ¬ε + t - 2 * ε ∈ E
        have hne : ¬t - ε ∈ E := htQ
        convert hne using 1 <;> ring
    · rintro ⟨htE, htPlus⟩
      refine ⟨?_, ?_⟩
      · simpa only [verticalShiftMinus, mem_setOf_eq, add_comm] using htE
      · change ¬t - ε ∈ E
        have hne : ¬ε + t - 2 * ε ∈ E := htPlus
        convert hne using 1 <;> ring
  rw [hset, measure_preimage_add]

/-- The Round24 difference is the right-shift difference of the original
set; this fixes the sign and factor two in the small-shift estimate. -/
theorem verticalShiftPlus_sdiff_verticalShiftMinus_measureReal
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (ε : ℝ) :
    volume.real (verticalShiftPlus E ε \ verticalShiftMinus E ε) =
      volume.real (E \ verticalShiftPlus E (2 * ε)) := by
  have hPfin : volume (verticalShiftMinus E ε) ≠ ∞ := by
    rw [verticalShiftMinus_volume]
    exact hEb.measure_lt_top.ne
  have hQfin : volume (verticalShiftPlus E ε) ≠ ∞ := by
    rw [verticalShiftPlus_volume]
    exact hEb.measure_lt_top.ne
  have hmass : volume.real (verticalShiftMinus E ε) =
      volume.real (verticalShiftPlus E ε) := by
    simp only [Measure.real_def, verticalShiftMinus_volume,
      verticalShiftPlus_volume]
  have hsym := measureReal_sdiff_eq_sdiff_of_eq_measureReal
    (verticalShiftMinus E ε) (verticalShiftPlus E ε)
    (verticalShiftMinus_measurable hE ε)
    (verticalShiftPlus_measurable hE ε) hPfin hQfin hmass
  rw [← hsym, Measure.real_def,
    verticalShiftMinus_sdiff_verticalShiftPlus_volume]
  rfl

end SpringerLean
