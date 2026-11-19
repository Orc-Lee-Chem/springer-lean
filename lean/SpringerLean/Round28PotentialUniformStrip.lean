import SpringerLean.Round28UniformOptimizer

open MeasureTheory Set Metric

namespace SpringerLean

/-- Actual boundary potential values on any finite vertical strip vary
uniformly continuously with the horizontal coordinate. -/
theorem regularExterior_rotated_potential_uniform_horizontal_on_strip
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (A T : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (a b t : ℝ), |a| ≤ A → |b| ≤ A → |t| ≤ T → |a - b| < δ →
        |regularExteriorRotatedPotential F s ξ ((a : ℂ) + (t : ℂ) * Complex.I) -
         regularExteriorRotatedPotential F s ξ ((b : ℂ) + (t : ℂ) * Complex.I)| < ε := by
  let R : ℝ := A + T + 1
  have hK : IsCompact (closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  have hUC : UniformContinuousOn (regularExteriorRotatedPotential F s ξ)
      (closedBall (0 : ℂ) R) :=
    hK.uniformContinuousOn_of_continuous
      (regularExterior_rotated_potential_continuous F hc hs0 hs1 ξ hξ).continuousOn
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro a b t ha hb ht hab
  let za : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let zb : ℂ := (b : ℂ) + (t : ℂ) * Complex.I
  have hmem (x : ℝ) (hx : |x| ≤ A) :
      ((x : ℂ) + (t : ℂ) * Complex.I) ∈ closedBall (0 : ℂ) R := by
    simp only [mem_closedBall, dist_zero_right]
    have htri := norm_add_le (x : ℂ) ((t : ℂ) * Complex.I)
    have hnorm : ‖(x : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ = |x| + |t| := by simp
    rw [hnorm] at htri
    dsimp [R]
    linarith
  have hdist : dist za zb = |a - b| := by
    dsimp [za, zb]
    rw [dist_eq_norm]
    have heq : ((a : ℂ) + (t : ℂ) * Complex.I) -
        ((b : ℂ) + (t : ℂ) * Complex.I) = ((a - b : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq]
    norm_cast
  have h := hclose za (hmem a ha) zb (hmem b hb) (by rwa [hdist])
  simpa only [Real.dist_eq, za, zb] using h

end SpringerLean