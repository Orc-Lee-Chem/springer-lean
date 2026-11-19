import SpringerLean.Round28AuxClosed
import SpringerLean.Round23Minimum

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- The common radial logarithmic reference kernel used to compare the two potentials. -/
noncomputable def verticalReferenceKernel (a t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + a ^ 2 + t ^ 2)

theorem verticalReferenceKernel_continuous (a : ℝ) :
    Continuous (verticalReferenceKernel a) := by
  apply continuous_const.mul
  have harg : Continuous (fun t : ℝ => 1 + a ^ 2 + t ^ 2) := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro t
  have hp : 0 < 1 + a ^ 2 + t ^ 2 := by positivity
  exact ContinuousAt.comp (f := fun q : ℝ => 1 + a ^ 2 + q ^ 2)
    (x := t) (Real.continuousAt_log (ne_of_gt hp)) harg.continuousAt

theorem verticalReferenceKernel_le_of_sq_le
    (a t u : ℝ) (htu : t ^ 2 ≤ u ^ 2) :
    verticalReferenceKernel a t ≤ verticalReferenceKernel a u := by
  dsimp [verticalReferenceKernel]
  have hp : 0 < 1 + a ^ 2 + t ^ 2 := by positivity
  have hle : 1 + a ^ 2 + t ^ 2 ≤ 1 + a ^ 2 + u ^ 2 := by linarith
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hp hle) (by norm_num)

/-- Among all bounded measurable sets of vertical length 2h, the centered
interval minimizes the actual reference-kernel integral. -/
theorem verticalReferenceKernel_centered_interval_minimizes
    (a h : ℝ) (hh : 0 ≤ h) (E : Set ℝ) (hE : E ∈ verticalFeasible h) :
    (∫ t in Icc (-h) h, verticalReferenceKernel a t) ≤
      ∫ t in E, verticalReferenceKernel a t := by
  let I : Set ℝ := Icc (-h) h
  let f : ℝ → ℝ := verticalReferenceKernel a
  have hI : I ∈ verticalFeasible h := by
    simpa [I] using centered_interval_verticalFeasible h 0
  have hIint : IntegrableOn f I := by
    exact (verticalReferenceKernel_continuous a).integrableOn_Icc
  obtain ⟨T, hT⟩ := isBounded_iff_forall_norm_le.mp hE.2.1
  have hET : E ⊆ Icc (-T) T := by
    intro t ht
    have htT : |t| ≤ T := by simpa [Real.norm_eq_abs] using hT t ht
    exact abs_le.mp htT
  have hTInt : IntegrableOn f (Icc (-T) T) := by
    exact (verticalReferenceKernel_continuous a).integrableOn_Icc
  have hEint : IntegrableOn f E := hTInt.mono_set hET
  have hUpper (t : ℝ) (ht : t ∈ I) : f t ≤ f h := by
    have hsq : t ^ 2 ≤ h ^ 2 := (sq_le_sq).2 (by
      rw [abs_of_nonneg hh]
      exact abs_le.mpr ht)
    exact verticalReferenceKernel_le_of_sq_le a t h hsq
  have hLower (t : ℝ) (ht : t ∉ I) : f h ≤ f t := by
    have hsq : h ^ 2 ≤ t ^ 2 := (sq_le_sq).2 (by
      rw [abs_of_nonneg hh]
      by_contra hnot
      have habs : |t| < h := lt_of_not_ge hnot
      exact ht (abs_le.mp habs.le))
    exact verticalReferenceKernel_le_of_sq_le a h t hsq
  apply threshold_candidate_integral_le f (f h) I E
    hI.1 hE.1
  · rw [hI.2.2]; finiteness
  · rw [hE.2.2]; finiteness
  · rw [hI.2.2, hE.2.2]
  · intro t ht
    by_contra hnot
    exact (not_lt_of_ge (hLower t hnot)) ht
  · exact hUpper
  · exact hIint
  · exact hEint
end SpringerLean