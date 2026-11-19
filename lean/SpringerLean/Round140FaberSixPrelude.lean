import SpringerLean.Round114FaberFivePrelude

set_option maxHeartbeats 1000000

namespace SpringerLean

/-- The centered sixth Faber polynomial, from the same actual forward
coefficients. The constant Laurent mode is cancelled. -/
noncomputable def sixthFaberPolynomial (F : ℂ → ℂ) : Polynomial ℂ :=
  let b := exteriorForwardCoeff F
  Polynomial.X ^ 6 -
    Polynomial.C (6 * b 1) * Polynomial.X ^ 4 -
    Polynomial.C (6 * b 2) * Polynomial.X ^ 3 +
    Polynomial.C (9 * b 1 ^ 2 - 6 * b 3) * Polynomial.X ^ 2 +
    Polynomial.C (12 * b 1 * b 2 - 6 * b 4) * Polynomial.X +
    Polynomial.C (-2 * b 1 ^ 3 + 6 * b 1 * b 3 +
      3 * b 2 ^ 2 - 6 * b 5)

noncomputable def sixthFaberFactor (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  let b := exteriorForwardCoeff F
  exteriorPhi F u ^ 6 -
    6 * b 1 * u ^ 2 * exteriorPhi F u ^ 4 -
    6 * b 2 * u ^ 3 * exteriorPhi F u ^ 3 +
    (9 * b 1 ^ 2 - 6 * b 3) * u ^ 4 * exteriorPhi F u ^ 2 +
    (12 * b 1 * b 2 - 6 * b 4) * u ^ 5 * exteriorPhi F u +
    (-2 * b 1 ^ 3 + 6 * b 1 * b 3 +
      3 * b 2 ^ 2 - 6 * b 5) * u ^ 6

/-- The sixth Faber polynomial's reciprocal analytic factor belongs to
the same actual exterior F, with no boundary extension assumption. -/
theorem sixthFaberPolynomial_reciprocal_factor
    (F : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    u ^ 6 * (sixthFaberPolynomial F).eval (F u⁻¹) =
      sixthFaberFactor F u := by
  simp only [sixthFaberPolynomial, sixthFaberFactor,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [exteriorF_reciprocal_phi F hu]
  field_simp [hu]

theorem sixthFaberPolynomial_boundary_factor
    (F : ℂ → ℂ) (θ : AddCircle (2 * Real.pi)) :
    (sixthFaberPolynomial F).eval (F (fourier 1 θ)) =
      fourier 6 θ * sixthFaberFactor F (fourier (-1) θ) := by
  simpa only [Nat.cast_ofNat] using
    reciprocal_factor_to_fourier_boundary F (sixthFaberPolynomial F) 6
      (sixthFaberFactor F)
      (fun {u : ℂ} hu => sixthFaberPolynomial_reciprocal_factor F hu) θ

end SpringerLean
