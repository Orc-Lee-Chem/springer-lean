import SpringerLean.Round1950RegularStarRays

open Polynomial

namespace SpringerLean

/-- The actual uniform norm scales exactly with a constant polynomial
factor on every nonempty compact set. -/
theorem continuumPolynomialNorm_C_mul
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (a : ℂ) (P : ℂ[X]) :
    continuumPolynomialNorm K (C a * P) =
      ‖a‖ * continuumPolynomialNorm K P := by
  obtain ⟨z, hz, hmax⟩ := continuumPolynomialNorm_attained K hK hne P
  have hmax' : ∀ w ∈ K,
      ‖(C a * P).eval w‖ ≤ ‖(C a * P).eval z‖ := by
    intro w hw
    simpa [eval_mul, eval_C, norm_mul] using
      mul_le_mul_of_nonneg_left (hmax w hw) (norm_nonneg a)
  rw [continuumPolynomialNorm_eq_at_max K hK hne (C a * P) hz hmax',
    continuumPolynomialNorm_eq_at_max K hK hne P hz hmax]
  simp [eval_mul, norm_mul]

/-- The supremum norm of a product is at most the product of the
supremum norms. This direction is elementary and is kept separate from
the reverse factor inequality defining `factorConstant`. -/
theorem continuumPolynomialNorm_mul_le
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (P Q : ℂ[X]) :
    continuumPolynomialNorm K (P * Q) ≤
      continuumPolynomialNorm K P * continuumPolynomialNorm K Q := by
  obtain ⟨z, hz, hmaxPQ⟩ := continuumPolynomialNorm_attained K hK hne (P * Q)
  obtain ⟨u, hu, hmaxP⟩ := continuumPolynomialNorm_attained K hK hne P
  obtain ⟨v, hv, hmaxQ⟩ := continuumPolynomialNorm_attained K hK hne Q
  rw [continuumPolynomialNorm_eq_at_max K hK hne (P * Q) hz hmaxPQ,
    continuumPolynomialNorm_eq_at_max K hK hne P hu hmaxP,
    continuumPolynomialNorm_eq_at_max K hK hne Q hv hmaxQ]
  rw [eval_mul, norm_mul]
  calc
    ‖P.eval z‖ * ‖Q.eval z‖ ≤
        ‖P.eval u‖ * ‖Q.eval z‖ :=
      mul_le_mul_of_nonneg_right (hmaxP z hz) (norm_nonneg _)
    _ ≤ ‖P.eval u‖ * ‖Q.eval v‖ :=
      mul_le_mul_of_nonneg_left (hmaxQ z hz) (norm_nonneg _)

end SpringerLean

#print axioms SpringerLean.continuumPolynomialNorm_C_mul
#print axioms SpringerLean.continuumPolynomialNorm_mul_le
