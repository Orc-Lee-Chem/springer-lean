import SpringerLean.Round1932OddStarPerturbationInjective

namespace SpringerLean

/-- The explicit exterior perturbation has exact rotational symmetry. -/
theorem oddStarPerturbation_rotation
    (m : ℕ) (t : ℝ) (η z : ℂ) (hη : η ^ m = 1) :
    oddStarPerturbation m t (η * z) =
      η * oddStarPerturbation m t z := by
  unfold oddStarPerturbation
  rw [mul_pow, hη, one_mul]
  ring

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_rotation
