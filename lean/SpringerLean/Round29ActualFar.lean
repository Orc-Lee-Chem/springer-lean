import SpringerLean.Round29MeanZeroLog
import SpringerLean.Round14BoundaryMean
import SpringerLean.Round22Costs

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual regularized rotated boundary potential has a quadratic
far-field error after its complex first moment cancels. -/
theorem regularExterior_rotated_potential_far_quadratic
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 2 * M < ‖z‖ →
      |regularExteriorRotatedPotential F s ξ z - Real.log ‖z‖| ≤
        M ^ 2 / ‖z‖ ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := regularExterior_boundary_curve_norm_bounded
    F hc hs0 hs1
  let W : ℂ → ℂ := fun ζ => conj ξ * rescaleExterior s F ζ
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : ContinuousOn (rescaleExterior s F) (sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hζ
    have hz : ζ ∈ exteriorAbove s := by
      change s < ‖ζ‖
      rw [hnorm]
      exact hs1
    exact (rescaleExterior_analyticAt hs0 hF hz).continuousAt.continuousWithinAt
  have hW : ContinuousOn W (sphere (0 : ℂ) 1) :=
    continuousOn_const.mul hG
  have hmean : Real.circleAverage W 0 1 = 0 := by
    calc
      Real.circleAverage W 0 1 =
        conj ξ • Real.circleAverage (rescaleExterior s F) 0 1 := by
          simpa only [W, smul_eq_mul] using
            (Real.circleAverage_fun_smul (a := conj ξ)
              (f := rescaleExterior s F) (c := 0) (R := 1))
      _ = 0 := by
        rw [rescaleExterior_boundary_circleAverage_zero F hc hs0 hs1]
        simp
  have hWbound : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖W ζ‖ ≤ M := by
    intro ζ hζ
    rw [show ‖W ζ‖ = ‖rescaleExterior s F ζ‖ from by
      simp [W, norm_mul, hξ]]
    exact hM ζ hζ
  refine ⟨M, hM0, ?_⟩
  intro z hz
  exact circleAverage_log_norm_sub_far_of_mean_zero W hW hmean M hM0
    hWbound z hz
end SpringerLean