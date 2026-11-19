import SpringerLean.Round1946FarthestDistance

open Polynomial

namespace SpringerLean

/-- Every admissible factor constant controls a finite family of actual
linear factors by their farthest-point distances. -/
theorem FactorInequality_linear_family
    (K : Set ℂ) (c : ℝ) (hc : FactorInequality K c)
    (r : ℕ) (a : Fin r → ℂ) :
    (∏ i : Fin r, continuumFarthestDistance K (a i)) ≤
      c ^ r *
        continuumPolynomialNorm K
          (∏ i : Fin r, (X - C (a i) : ℂ[X])) := by
  have h := hc r (fun i : Fin r => X - C (a i))
  simpa [← continuumFarthestDistance_eq_linear_norm] using h

end SpringerLean

#print axioms SpringerLean.FactorInequality_linear_family
