import SpringerLean.Round26GoodPoints

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace SpringerLean

/-- If no nonempty interval is filled modulo null sets, two separated
indicator transitions are available at differentiability points of its
primitive. This yields the required small-translation estimate. -/
theorem realSet_shift_sdiff_lower_of_no_ae_interval
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (hEpos : 0 < volume.real E)
    (hgap : ∀ a b : ℝ, a < b →
      0 < volume.real (Ioo a b \ E)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ, 0 < d → d < δ →
      d ≤ volume.real (E \ verticalShiftPlus E d) := by
  let p : ℝ → Prop := fun x =>
    HasDerivAt (realSetPrimitive E) (realSetIndicator E x) x
  have hgood : ∀ᵐ x : ℝ, p x :=
    realSetPrimitive_ae_hasDerivAt E hE hEb
  have hEne : volume E ≠ 0 :=
    (measureReal_ne_zero_iff hEb.measure_lt_top.ne).mp (ne_of_gt hEpos)
  obtain ⟨b₁, b₂, hb₁E, hb₂E, hb₁b₂, hb₁good, hb₂good⟩ :=
    positive_measure_exists_two_good_points E hEne p hgood
  have hb₁deriv : HasDerivAt (realSetPrimitive E) 1 b₁ := by
    simpa [p, realSetIndicator, hb₁E] using hb₁good
  have hb₂deriv : HasDerivAt (realSetPrimitive E) 1 b₂ := by
    simpa [p, realSetIndicator, hb₂E] using hb₂good
  let C : Set ℝ := Ioo b₁ b₂ \ E
  have hCb : Bornology.IsBounded C :=
    (Metric.isBounded_Ioo b₁ b₂).subset sdiff_subset
  have hCne : volume C ≠ 0 :=
    (measureReal_ne_zero_iff hCb.measure_lt_top.ne).mp (ne_of_gt (hgap b₁ b₂ hb₁b₂))
  obtain ⟨a₂, ha₂C, ha₂good⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hCne (ae_restrict_of_ae hgood)
  have hb₁a₂ : b₁ < a₂ := ha₂C.1.1
  have ha₂b₂ : a₂ < b₂ := ha₂C.1.2
  have ha₂deriv : HasDerivAt (realSetPrimitive E) 0 a₂ := by
    simpa [p, realSetIndicator, ha₂C.2] using ha₂good
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hEb
  let M₀ : ℝ := max M 0
  let L : ℝ := -M₀ - 2
  let U : ℝ := -M₀ - 1
  have hLU : L < U := by dsimp [L, U]; linarith
  have hIne : volume (Ioo L U) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hLU))
  obtain ⟨a₁, ha₁I, ha₁good⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIne (ae_restrict_of_ae hgood)
  have ha₁notE : a₁ ∉ E := by
    intro ha₁E
    have hbound : |a₁| ≤ M₀ :=
      (show |a₁| ≤ M from by simpa [Real.norm_eq_abs] using hM a₁ ha₁E).trans
        (le_max_left _ _)
    have hleft := (abs_le.mp hbound).1
    have ha₁U : a₁ < U := ha₁I.2
    dsimp [U] at ha₁U
    linarith
  have ha₁b₁ : a₁ < b₁ := by
    have hbound : |b₁| ≤ M₀ :=
      (show |b₁| ≤ M from by simpa [Real.norm_eq_abs] using hM b₁ hb₁E).trans
        (le_max_left _ _)
    have hb₁lower := (abs_le.mp hbound).1
    have ha₁U : a₁ < U := ha₁I.2
    dsimp [U] at ha₁U
    linarith
  have ha₁deriv : HasDerivAt (realSetPrimitive E) 0 a₁ := by
    simpa [p, realSetIndicator, ha₁notE] using ha₁good
  exact realSet_shift_sdiff_lower_of_two_derivative_pairs
    E hE hEb a₁ b₁ a₂ b₂ ha₁b₁ hb₁a₂ ha₂b₂
    ha₁deriv hb₁deriv ha₂deriv hb₂deriv

end SpringerLean
