import SpringerLean.Round11Jacobian

open MeasureTheory

namespace SpringerLean

/-- The four actual Green rectangles cancel on their common unit circle and
outer homotopy. This is the full signed partition in polar *parameter*
measure. Its conversion to plane area is a separate measure-theoretic step. -/
theorem regular_signed_polar_parameter_partition
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    ∃ R : ℝ, 1 < R ∧
      (∀ z : ℂ, R ≤ ‖z‖ →
        evenWeightCutoff T hT k z = 0) ∧
      (∀ z : ℂ, R ≤ ‖z‖ →
        evenWeightCutoff T hT k (rescaleExterior s F z) = 0) ∧
      (∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 2 * Real.pi),
        p.1 * evenWeightCutoff T hT k
            (regularHarmonic s F (greenPolar p.1 p.2)) *
          (fderiv ℝ (regularHarmonic s F) (greenPolar p.1 p.2)).det
          ∂volume) +
      (∫ p in Set.Icc ((1 : ℝ), (0 : ℝ)) (R, 2 * Real.pi),
        p.1 * evenWeightCutoff T hT k
            (rescaleExterior s F (greenPolar p.1 p.2)) *
          (fderiv ℝ (rescaleExterior s F) (greenPolar p.1 p.2)).det
          ∂volume) =
      ∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (R, 2 * Real.pi),
        p.1 * evenWeightCutoff T hT k (greenPolar p.1 p.2) ∂volume := by
  obtain ⟨R, hR, hφfar, hfar, houter⟩ :=
    regular_greenBoundary_outer_eq F hc hs0 hs1 T hT k
  let φ : ℂ → ℝ := evenWeightCutoff T hT k
  have hφ : ContDiff ℝ 1 φ := evenWeightCutoff_contDiff T hT k
  have hcompact : HasCompactSupport φ :=
    evenWeightCutoff_hasCompactSupport T hT k
  have hD := regular_green_parameter_disk_signed
    F hc hs0 hs1 φ hφ hcompact
  have hA := regular_green_parameter_annulus_signed
    F hc hs0 hs1 hR φ hφ hcompact
  have hS := green_parameter_standard_disk_radial
    φ hφ hcompact R (le_trans (by norm_num) hR.le)
  have hunit := regular_greenBoundary_unit_eq F hs0 φ
  refine ⟨R, hR, hφfar, hfar, ?_⟩
  dsimp only [φ] at hD hA hS hunit
  linarith

end SpringerLean
