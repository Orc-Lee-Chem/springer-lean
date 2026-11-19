import SpringerLean.AreaLinear
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace SpringerLean

/-- The corrected image of a large annulus lies in an explicit closed disk,
and its measure is exactly the original image area times the correction
determinant. This keeps the area constant sharp before taking limits. -/
theorem exteriorAnnulus_image_area_corrected_upper
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr : 1 < r) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ r < R₀ ∧
      ∀ R : ℝ, R₀ ≤ R →
        ENNReal.ofReal
          |1 - ‖exteriorForwardCoeff F 1 / (R : ℂ) ^ 2‖ ^ 2| *
          MeasureTheory.volume (F '' exteriorAnnulus r R) ≤
        ENNReal.ofReal (R + C / R ^ 2) ^ 2 * NNReal.pi := by
  obtain ⟨C, R₀, hC, hrR₀, hbound⟩ :=
    exteriorLinearCorrection_large_annulus_norm_bound F hc hr
  refine ⟨C, R₀, hC, hrR₀, ?_⟩
  intro R hR
  let S : ℝ := R + C / R ^ 2
  have hsubset :
      exteriorLinearCorrection F R ''
        (F '' exteriorAnnulus r R) ⊆
          Metric.closedBall (0 : ℂ) S := by
    rintro w ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    change dist (exteriorLinearCorrection F R (F z)) 0 ≤ S
    rw [dist_zero_right]
    exact hbound R z hR hz
  have hmeasure :
      MeasureTheory.volume
        (exteriorLinearCorrection F R ''
          (F '' exteriorAnnulus r R)) ≤
      MeasureTheory.volume (Metric.closedBall (0 : ℂ) S) :=
    MeasureTheory.measure_mono hsubset
  rw [exteriorLinearCorrection_image_area,
    Complex.volume_closedBall] at hmeasure
  simpa only [S] using hmeasure

end SpringerLean
