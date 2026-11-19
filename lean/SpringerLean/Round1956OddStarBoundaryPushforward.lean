import SpringerLean.Round1955OddStarBoundaryPower

open MeasureTheory Set

namespace SpringerLean

/-- For every real test function, the power pushforward of the actual
radial boundary trace is represented by the continuous seed boundary
values at the m-fold circular parameter. No integrability hypothesis is
needed for the equality of the two Lebesgue integrals. -/
theorem oddStarPerturbation_radial_power_integral_eq
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (φ : ℂ → ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      φ ((actualExteriorRadialTrace (oddStarPerturbation m t) θ) ^ m)) =
    ∫ θ in Ioo (-Real.pi) Real.pi,
      φ (oddStarSeed t ((Complex.polarCoord.symm (1, θ)) ^ m)) := by
  apply integral_congr_ae
  filter_upwards [oddStarPerturbation_actual_radialTrace_pow m hm t ht] with θ hθ
  rw [hθ]

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_radial_power_integral_eq
