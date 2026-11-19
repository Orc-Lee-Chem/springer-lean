import SpringerLean.Round1913ActualProjectionFirstMode
import SpringerLean.Round1898InterpolationCurvatureBridge

namespace SpringerLean

/-- The 3D/8 correction in real-exponent interpolation now holds for the
same actual radial trace and the first Laurent coefficient of F. -/
theorem actualBoundaryProjectionSecondMoment_deficit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      1 / 2 - actualBoundaryProjectionSecondMoment F c ≤
        3 * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 8 := by
  obtain ⟨c, hcunit, hmode⟩ :=
    actualBoundaryProjectionSecondMoment_phase_bound F hc
  have hx : ‖exteriorForwardCoeff F 1‖ ≤ 1 := by
    have h := exteriorInverseCoeff_one_norm_le F hc
    rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] at h
    exact h
  refine ⟨c, hcunit, ?_⟩
  exact interpolation_projection_secondMoment_scalar
    (norm_nonneg _) hx hmode

end SpringerLean

#print axioms SpringerLean.actualBoundaryProjectionSecondMoment_deficit
