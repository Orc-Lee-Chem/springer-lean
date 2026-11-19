import SpringerLean.Round17ActualCurve
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Every rotated actual regularized boundary logarithm is integrable
around the unit circle, even when its target lies on the boundary curve. -/
theorem regularExterior_rotated_log_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ w : ℂ) :
    CircleIntegrable
      (fun ζ : ℂ => Real.log ‖conj ξ * rescaleExterior s F ζ - w‖) 0 1 := by
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hAnal : AnalyticOnNhd ℂ
      (fun ζ : ℂ => conj ξ * rescaleExterior s F ζ - w)
      (sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hζ
    have hext : ζ ∈ exteriorAbove s := by
      change s < ‖ζ‖
      rw [hnorm]
      exact hs1
    exact (analyticAt_const.mul (rescaleExterior_analyticAt hs0 hF hext)).sub
      analyticAt_const
  have hMer : MeromorphicOn
      (fun ζ : ℂ => conj ξ * rescaleExterior s F ζ - w)
      (sphere (0 : ℂ) |(1 : ℝ)|) := by
    simpa only [abs_one] using hAnal.meromorphicOn
  exact hMer.circleIntegrable_log_norm

/-- On the unit circle, the comparison projection is exactly the boundary
value of the actual normalized slit map `z + 1/z`. -/
theorem comparisonCircle_eq_slitMap_one
    {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) :
    ((2 * ζ.re : ℝ) : ℂ) = slitMap 1 ζ := by
  have hnorm : ‖ζ‖ = 1 := by
    simpa [mem_sphere, dist_zero_right] using hζ
  rw [slitMap, div_eq_mul_inv, one_mul, Complex.inv_eq_conj hnorm,
    Complex.add_conj]

/-- The comparison logarithm is circle integrable for every complex target,
including a target on its real slit. -/
theorem comparisonCircle_log_circleIntegrable (w : ℂ) :
    CircleIntegrable
      (fun ζ : ℂ => Real.log ‖((2 * ζ.re : ℝ) : ℂ) - w‖) 0 1 := by
  have hAnal : AnalyticOnNhd ℂ (fun ζ : ℂ => slitMap 1 ζ - w)
      (sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hζ
    have hz : ζ ≠ 0 := by
      intro heq
      simp [heq] at hnorm
    exact (slitMap_analyticAt 1 ζ hz).sub analyticAt_const
  have hMer : MeromorphicOn (fun ζ : ℂ => slitMap 1 ζ - w)
      (sphere (0 : ℂ) |(1 : ℝ)|) := by
    simpa only [abs_one] using hAnal.meromorphicOn
  have hEq : Set.EqOn
      (fun ζ : ℂ => Real.log ‖((2 * ζ.re : ℝ) : ℂ) - w‖)
      (fun ζ : ℂ => Real.log ‖slitMap 1 ζ - w‖)
      (sphere (0 : ℂ) |(1 : ℝ)|) := by
    intro ζ hζ
    change Real.log ‖((2 * ζ.re : ℝ) : ℂ) - w‖ =
      Real.log ‖slitMap 1 ζ - w‖
    rw [comparisonCircle_eq_slitMap_one (by simpa only [abs_one] using hζ)]
  exact (circleIntegrable_congr hEq).2 hMer.circleIntegrable_log_norm

end SpringerLean
