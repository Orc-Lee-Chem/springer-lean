import SpringerLean.Round24SetSplit

open MeasureTheory Set
open scoped ENNReal Classical

namespace SpringerLean

theorem verticalShiftMinus_bounded
    (E : Set ℝ) (hEb : Bornology.IsBounded E) (ε : ℝ) :
    Bornology.IsBounded (verticalShiftMinus E ε) := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hEb
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + |ε|, ?_⟩
  intro t ht
  have hte : t + ε ∈ E := ht
  have hbound := hM (t + ε) hte
  have hnorm : ‖t‖ ≤ ‖t + ε‖ + |ε| := by
    calc
      ‖t‖ = ‖(t + ε) - ε‖ := by congr 1; ring
      _ ≤ ‖t + ε‖ + ‖ε‖ := norm_sub_le _ _
      _ = _ := by simp
  linarith

theorem verticalShiftPlus_bounded
    (E : Set ℝ) (hEb : Bornology.IsBounded E) (ε : ℝ) :
    Bornology.IsBounded (verticalShiftPlus E ε) := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hEb
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + |ε|, ?_⟩
  intro t ht
  have hte : t - ε ∈ E := ht
  have hbound := hM (t - ε) hte
  have hnorm : ‖t‖ ≤ ‖t - ε‖ + |ε| := by
    calc
      ‖t‖ = ‖(t - ε) + ε‖ := by congr 1; ring
      _ ≤ ‖t - ε‖ + ‖ε‖ := norm_add_le _ _
      _ = _ := by simp
  linarith

theorem verticalShiftMinus_volume
    (E : Set ℝ) (ε : ℝ) :
    volume (verticalShiftMinus E ε) = volume E := by
  have hset : verticalShiftMinus E ε = (fun t : ℝ => ε + t) ⁻¹' E := by
    ext t
    simp [verticalShiftMinus, add_comm]
  rw [hset, measure_preimage_add]

theorem verticalShiftPlus_volume
    (E : Set ℝ) (ε : ℝ) :
    volume (verticalShiftPlus E ε) = volume E := by
  have hset : verticalShiftPlus E ε = (fun t : ℝ => -ε + t) ⁻¹' E := by
    ext t
    simp [verticalShiftPlus, sub_eq_add_neg, add_comm]
  rw [hset, measure_preimage_add]

/-- Precise reduction of the general small-shift decomposition to its
only missing quantitative estimate. -/
theorem verticalFeasible_shift_redistribute_of_diff_mass
    (E : Set ℝ) (h : ℝ) (hE : E ∈ verticalFeasible h)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hεh : ε < h)
    (hdiff : 2 * ε ≤
      volume.real (verticalShiftPlus E ε \ verticalShiftMinus E ε)) :
    ∃ A ∈ verticalFeasible (h + ε),
      ∃ B ∈ verticalFeasible (h - ε),
        ∀ t : ℝ,
          (if t ∈ A then (1 : ℕ) else 0) +
            (if t ∈ B then (1 : ℕ) else 0) =
          (if t ∈ verticalShiftMinus E ε then (1 : ℕ) else 0) +
            (if t ∈ verticalShiftPlus E ε then (1 : ℕ) else 0) := by
  obtain ⟨hEmeas, hEb, hEmass⟩ := hE
  have hm : volume.real E = 2 * h := by
    rw [Measure.real_def, hEmass, ENNReal.toReal_ofReal (by linarith)]
  have hmP : volume.real (verticalShiftMinus E ε) = 2 * h := by
    rw [Measure.real_def, verticalShiftMinus_volume]
    exact hm
  have hmQ : volume.real (verticalShiftPlus E ε) = 2 * h := by
    rw [Measure.real_def, verticalShiftPlus_volume]
    exact hm
  obtain ⟨A, B, hAmeas, hBmeas, hAb, hBb, hAmass, hBmass, hcount⟩ :=
    equal_mass_sets_redistribute
      (verticalShiftMinus E ε) (verticalShiftPlus E ε)
      (verticalShiftMinus_measurable hEmeas ε)
      (verticalShiftPlus_measurable hEmeas ε)
      (verticalShiftMinus_bounded E hEb ε)
      (verticalShiftPlus_bounded E hEb ε)
      (2 * h) (2 * ε) hmP hmQ (by positivity) hdiff
  have hAvol : volume A = ENNReal.ofReal (2 * (h + ε)) := by
    have hAfin : volume A ≠ ∞ := hAb.measure_lt_top.ne
    calc
      volume A = ENNReal.ofReal (volume.real A) :=
        (ENNReal.ofReal_toReal hAfin).symm
      _ = ENNReal.ofReal (2 * (h + ε)) := by
        rw [hAmass]
        congr 1
        ring
  have hBvol : volume B = ENNReal.ofReal (2 * (h - ε)) := by
    have hBfin : volume B ≠ ∞ := hBb.measure_lt_top.ne
    calc
      volume B = ENNReal.ofReal (volume.real B) :=
        (ENNReal.ofReal_toReal hBfin).symm
      _ = ENNReal.ofReal (2 * (h - ε)) := by
        rw [hBmass]
        congr 1
        ring
  exact ⟨A, ⟨hAmeas, hAb, hAvol⟩,
    B, ⟨hBmeas, hBb, hBvol⟩, hcount⟩

end SpringerLean
