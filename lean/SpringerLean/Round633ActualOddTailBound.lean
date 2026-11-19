import SpringerLean.Round621FiniteOddRootTail
import SpringerLean.Round624ActualOddTailSeries

open Filter
open scoped Topology

namespace SpringerLean
set_option Elab.async false

/-- The actual convergent odd tail satisfies the area/Cauchy estimate.
Both the sum and the coefficients belong to the same actual exterior map. -/
theorem exterior_odd_tail_norm_sq_le
    (H : ℂ → ℂ) (hc : CenteredExteriorUnivalent H)
    (hodd : ∀ z, H (-z) = -H z)
    {r : ℝ} (hr : 1 < r) {z : ℂ} (hz : ‖z‖ = r) :
    ‖H z-z-exteriorForwardCoeff H 1*z⁻¹‖^2 ≤
      (1-‖exteriorForwardCoeff H 1‖^2)*exteriorStripLogKernel r := by
  have hzE : z ∈ exteriorDisk := by
    change 1 < ‖z‖
    rwa [hz]
  have hs := exterior_odd_tail_hasSum H hc hodd hzE
  have ht := hs.tendsto_sum_nat.norm.pow 2
  apply le_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro M
  simpa only [mul_comm] using
    exteriorForwardCoeff_finite_odd_tail_sq_le H hc hr hz M

theorem exterior_odd_tail_norm_le
    (H : ℂ → ℂ) (hc : CenteredExteriorUnivalent H)
    (hodd : ∀ z, H (-z) = -H z)
    {r : ℝ} (hr : 1 < r) {z : ℂ} (hz : ‖z‖ = r) :
    ‖H z-z-exteriorForwardCoeff H 1*z⁻¹‖ ≤
      Real.sqrt ((1-‖exteriorForwardCoeff H 1‖^2)*exteriorStripLogKernel r) :=
  Real.le_sqrt_of_sq_le (exterior_odd_tail_norm_sq_le H hc hodd hr hz)

end SpringerLean
