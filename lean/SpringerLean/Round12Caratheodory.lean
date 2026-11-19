import SpringerLean.Round12ClosedHull
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace SpringerLean

/-- Every point of a planar convex hull already lies in the hull of at most
three points of the original set. This is the finite-dimensional input needed
to turn the closed-hull conclusion into ordinary convex-hull membership. -/
theorem complex_mem_convexHull_three_points {K : Set ℂ} {x : ℂ}
    (hx : x ∈ convexHull ℝ K) :
    ∃ t : Finset ℂ, (t : Set ℂ) ⊆ K ∧ t.card ≤ 3 ∧
      x ∈ convexHull ℝ (t : Set ℂ) := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have hind : AffineIndependent ℝ ((↑) : t → ℂ) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hcard := hind.card_le_finrank_succ
  have hdim : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → ℂ))) ≤ 2 := by
    simpa [Complex.finrank_real_complex] using
      (Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → ℂ))))
  refine ⟨t, Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx, ?_,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  simpa only [Fintype.card_coe] using hcard.trans (by omega)

end SpringerLean
