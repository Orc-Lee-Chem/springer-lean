import SpringerLean.Round1922ActualSixToEight

namespace SpringerLean

/-- Actual continuous real-exponent boundary moments on the full interval
from four to eight, in the normalized cosine scale. -/
theorem normalized_actual_radial_moment_four_to_eight
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {p : ℝ} (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    normalizedActualRadialMoment F p ≤
      normalizedCosineMoment p *
        (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 80) := by
  by_cases hp6 : p ≤ 6
  · let θ := (p - 4) / 2
    have hθ0 : 0 ≤ θ := by dsimp [θ]; linarith
    have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
    have h := normalized_actual_radial_moment_four_to_six F hc hθ0 hθ1
    have hp : 4 + 2 * θ = p := by dsimp [θ]; ring
    rwa [hp] at h
  · let θ := (p - 6) / 2
    have hθ0 : 0 ≤ θ := by dsimp [θ]; linarith
    have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
    have h := normalized_actual_radial_moment_six_to_eight F hc hθ0 hθ1
    have hp : 6 + 2 * θ = p := by dsimp [θ]; ring
    rwa [hp] at h

end SpringerLean

#print axioms SpringerLean.normalized_actual_radial_moment_four_to_eight
