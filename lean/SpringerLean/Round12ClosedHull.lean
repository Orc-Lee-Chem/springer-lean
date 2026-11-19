import SpringerLean.Round12ProjectionLimit
import Mathlib.Analysis.LocallyConvex.Separation

open scoped Topology ComplexConjugate

namespace SpringerLean

/-- Every continuous real-linear functional on the complex plane is a
directional real-part projection, with no normalization of the direction. -/
theorem complex_realLinearFunctional_projection
    (L : ℂ →L[ℝ] ℝ) :
    ∃ c : ℂ, ∀ w : ℂ, L w = (c * w).re := by
  let c : ℂ := ⟨L 1, -(L Complex.I)⟩
  refine ⟨c, ?_⟩
  intro w
  have hdecomp : w = (w.re : ℝ) • (1 : ℂ) +
      (w.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  calc
    L w = L ((w.re : ℝ) • (1 : ℂ) +
        (w.im : ℝ) • Complex.I) := congrArg L hdecomp
    _ = w.re * L 1 + w.im * L Complex.I := by
      simp only [map_add, map_smul, smul_eq_mul]
    _ = (c * w).re := by
      simp [c, Complex.mul_re]
      ring

/-- The first direct consequence of the actual directional witnesses is
membership in the closed convex hull of the actual omitted set. -/
theorem actualHarmonic_mem_closedConvexHull_omitted
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    actualHarmonic F z ∈ closedConvexHull ℝ (exteriorOmitted F) := by
  by_contra hnot
  obtain ⟨L, u, hbelow, habove⟩ :=
    geometric_hahn_banach_closed_point
      (convex_closedConvexHull (𝕜 := ℝ) (s := exteriorOmitted F))
      (isClosed_closedConvexHull (𝕜 := ℝ) (s := exteriorOmitted F)) hnot
  obtain ⟨c, hcL⟩ := complex_realLinearFunctional_projection L
  obtain ⟨w, hw, hproj⟩ :=
    actualHarmonic_projection_omitted_witness F hc c hz
  have hwHull : w ∈ closedConvexHull ℝ (exteriorOmitted F) :=
    subset_closedConvexHull (𝕜 := ℝ) hw
  have hwBelow := hbelow w hwHull
  rw [← hcL, ← hcL] at hproj
  linarith

end SpringerLean
