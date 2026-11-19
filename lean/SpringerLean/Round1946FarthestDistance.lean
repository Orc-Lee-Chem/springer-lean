import SpringerLean.Round1945OddStarActualContinuum

open Polynomial

namespace SpringerLean

/-- The farthest-point distance from an actual plane set. -/
noncomputable def continuumFarthestDistance
    (K : Set ℂ) (z : ℂ) : ℝ :=
  sSup ((fun w : ℂ => ‖z - w‖) '' K)

/-- The farthest-point function is exactly the polynomial uniform norm
of a linear factor. This is the elementary bridge used in the sharp
factor-constant formula of Pritsker and Ruscheweyh. -/
theorem continuumFarthestDistance_eq_linear_norm
    (K : Set ℂ) (z : ℂ) :
    continuumFarthestDistance K z =
      continuumPolynomialNorm K (X - C z) := by
  unfold continuumFarthestDistance continuumPolynomialNorm
  congr 1
  ext r
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, hw, ?_⟩
    simp [norm_sub_rev]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, hw, ?_⟩
    simp [norm_sub_rev]

/-- Compact nonempty sets attain every farthest-point distance. -/
theorem continuumFarthestDistance_attained
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (z : ℂ) :
    ∃ w ∈ K, ∀ v ∈ K, ‖z - v‖ ≤ ‖z - w‖ := by
  have hcont : Continuous (fun w : ℂ => ‖z - w‖) := by fun_prop
  obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
  exact ⟨w, hw, fun v hv => hmax hv⟩

end SpringerLean

#print axioms SpringerLean.continuumFarthestDistance_eq_linear_norm
#print axioms SpringerLean.continuumFarthestDistance_attained
