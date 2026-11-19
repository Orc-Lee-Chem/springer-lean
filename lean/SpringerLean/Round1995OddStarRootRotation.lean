import SpringerLean.Round1994OddStarLogIntegrability

open MeasureTheory Set

namespace SpringerLean

theorem unit_complex_eq_polar_arg (η : ℂ) (hη : ‖η‖ = 1) :
    η = Complex.polarCoord.symm (1, Complex.arg η) := by
  have h := Complex.norm_mul_exp_arg_mul_I η
  rw [hη, Complex.ofReal_one, one_mul] at h
  simpa only [Complex.polarCoord_symm_apply, Complex.ofReal_one,
    one_mul, ← Complex.exp_ofReal_mul_I] using h.symm

/-- Rotation invariance of the actual odd-star radial boundary law for
an arbitrary complex m-th root of unity. -/
theorem oddStarActualBoundaryProbability_map_root_rotation
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (η : ℂ) (hη : η ^ m = 1) :
    (oddStarActualBoundaryProbability m t).map (fun u : ℂ => η * u) =
      oddStarActualBoundaryProbability m t := by
  have hnorm : ‖η‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hη (by omega)
  have heq := unit_complex_eq_polar_arg η hnorm
  rw [heq] at hη ⊢
  exact oddStarActualBoundaryProbability_map_rotation
    m hm t ht (Complex.arg η) hη

end SpringerLean

#print axioms SpringerLean.oddStarActualBoundaryProbability_map_root_rotation
