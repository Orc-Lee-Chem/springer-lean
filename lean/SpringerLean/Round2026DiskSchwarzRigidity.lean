import SpringerLean.Round2025RotatedExteriorImage
import Mathlib.Analysis.Complex.Schwarz

namespace SpringerLean

theorem unitDisk_selfMap_deriv_one_eq_id
    (H : ℂ → ℂ)
    (hDiff : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hMap : Set.MapsTo H (Metric.ball (0:ℂ) 1) (Metric.ball 0 1))
    (h0 : H 0 = 0) (hDeriv : deriv H 0 = 1) :
    Set.EqOn H id (Metric.ball (0:ℂ) 1) := by
  have hMapClosed : Set.MapsTo H (Metric.ball (0:ℂ) 1)
      (Metric.closedBall (H 0) 1) := by
    intro z hz
    simpa [h0] using Metric.ball_subset_closedBall (hMap hz)
  have hzero : (0:ℂ) ∈ Metric.ball 0 1 := by simp
  have hSlope : ‖dslope H 0 0‖ = (1:ℝ) / 1 := by
    rw [dslope_same, hDeriv]
    norm_num
  have hAffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    hDiff hMapClosed hzero hSlope
  intro z hz
  have h := hAffine hz
  simpa [h0, dslope_same, hDeriv, id_eq] using h

end SpringerLean

#print axioms SpringerLean.unitDisk_selfMap_deriv_one_eq_id
