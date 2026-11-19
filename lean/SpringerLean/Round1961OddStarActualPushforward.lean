import SpringerLean.Round1960CenteredAngleAverage

open MeasureTheory Set

namespace SpringerLean

/-- The m-th power pushes the actual radial boundary distribution of
the star perturbation to the ordinary angular boundary distribution of
the seed. The equality is tested against every continuous real function
on the complex plane, with the actual a.e. radial trace on the left. -/
theorem oddStarPerturbation_actual_radial_power_pushforward
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (φ : ℂ → ℝ) (hφ : Continuous φ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      φ ((actualExteriorRadialTrace (oddStarPerturbation m t) θ) ^ m)) =
    ∫ θ in Ioo (-Real.pi) Real.pi,
      φ (oddStarSeed t (Complex.polarCoord.symm (1, θ))) := by
  exact (oddStarPerturbation_radial_power_integral_eq m hm t ht φ).trans
    (oddStarSeed_boundary_power_setIntegral_eq m (by omega) t ht φ hφ)

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_actual_radial_power_pushforward
