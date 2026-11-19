import SpringerLean.Round27RotatedHarmonic

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean

/-- Local circular submean for the actual unit-rotated regularized boundary
logarithmic potential. This is the potential used in the vertical cost
functional, with no external subharmonicity premise. -/
theorem regularExterior_rotated_potential_local_circle_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (z : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
      regularExteriorRotatedPotential F s ξ z ≤
        Real.circleAverage (regularExteriorRotatedPotential F s ξ) z ρ := by
  let P := regularExteriorRotatedPotential F s ξ
  by_cases hzpos : 0 < P z
  · have hH : InnerProductSpace.HarmonicAt P z :=
      regularExterior_rotated_potential_harmonicAt_of_pos F hc hs0 hs1 ξ hξ hzpos
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hH.eventually
    refine ⟨δ, hδ, ?_⟩
    intro ρ hρ hρδ
    have hOn : InnerProductSpace.HarmonicOnNhd P (closedBall z |ρ|) := by
      intro u hu
      apply hball
      change dist u z < δ
      have hdist : dist u z ≤ |ρ| := hu
      rw [abs_of_pos hρ] at hdist
      exact lt_of_le_of_lt hdist hρδ
    change P z ≤ Real.circleAverage P z ρ
    rw [hOn.circleAverage_eq]
  · have hnonneg : 0 ≤ P z :=
      regularExterior_rotated_boundary_potential_nonneg F hc hs0 hs1 ξ hξ z
    have hzero : P z = 0 := le_antisymm (le_of_not_gt hzpos) hnonneg
    refine ⟨1, by norm_num, ?_⟩
    intro ρ hρ hρ1
    change P z ≤ Real.circleAverage P z ρ
    rw [hzero]
    apply Real.circleAverage_nonneg_of_nonneg
    intro u hu
    exact regularExterior_rotated_boundary_potential_nonneg F hc hs0 hs1 ξ hξ u

end SpringerLean
