import SpringerLean.AnnulusBoundaries
import Mathlib.Analysis.Complex.AbsMax

namespace SpringerLean

/-- Every closure point of an open annulus lies between its two boundary
radii. No Jordan-curve regularity is used. -/
theorem exteriorAnnulus_closure_radius_bounds (r R : ℝ) :
    closure (exteriorAnnulus r R) ⊆
      {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  apply closure_minimal
  · intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

/-- The frontier of the open annulus consists only of its two norm-level
circles, even when no boundary extension of `F` is assumed. -/
theorem exteriorAnnulus_frontier_radius
    (r R : ℝ) {z : ℂ} (hz : z ∈ frontier (exteriorAnnulus r R)) :
    ‖z‖ = r ∨ ‖z‖ = R := by
  have hclose : r ≤ ‖z‖ ∧ ‖z‖ ≤ R :=
    exteriorAnnulus_closure_radius_bounds r R hz.1
  have hnot : z ∉ exteriorAnnulus r R := by
    have h := hz.2
    simpa only [(exteriorAnnulus_isOpen r R).interior_eq] using h
  change ¬(r < ‖z‖ ∧ ‖z‖ < R) at hnot
  rcases not_and_or.mp hnot with hleft | hright
  · exact Or.inl (le_antisymm hclose.1 (le_of_not_gt hleft)).symm
  · exact Or.inr (le_antisymm hclose.2 (le_of_not_gt hright))

/-- All points of the closed annulus remain in the exterior domain once
the inner radius exceeds one. -/
theorem exteriorAnnulus_closure_subset_exteriorDisk
    {r R : ℝ} (hr : 1 < r) :
    closure (exteriorAnnulus r R) ⊆ exteriorDisk := by
  intro z hz
  have h := (exteriorAnnulus_closure_radius_bounds r R hz).1
  exact lt_of_lt_of_le hr h

end SpringerLean
