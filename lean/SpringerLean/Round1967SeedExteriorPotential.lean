import SpringerLean.Round1966SeedJensenFactors

open MeasureTheory Metric Set

namespace SpringerLean

/-- The explicit rational seed has logarithmic boundary potential
`log ‖z‖` at every exterior image point `G_t(z)`. This is the
potential-theoretic bridge needed before identifying its boundary law
with the equilibrium measure. -/
theorem oddStarSeed_boundary_log_potential_exterior
    (t : ℝ) (ht : |t| < 1) (z : ℂ) (hz : 1 < ‖z‖) :
    Real.circleAverage
      (fun u : ℂ => Real.log ‖oddStarSeed t u - oddStarSeed t z‖)
      0 1 = Real.log ‖z‖ := by
  let a : ℂ := (t : ℂ) * Complex.I
  let p : ℂ := oddStarSeedPartner t z
  have hp : ‖p‖ < 1 := oddStarSeedPartner_norm_lt_one t ht z hz
  have hz0 : z - a ≠ 0 := by
    intro heq
    have hz' : z = a := sub_eq_zero.mp heq
    have hnorm : ‖z‖ = |t| := by
      rw [hz']
      dsimp [a]
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      rfl
    rw [hnorm] at hz
    linarith
  have hpoint : Set.EqOn
      (fun u : ℂ => Real.log ‖oddStarSeed t u - oddStarSeed t z‖)
      (fun u : ℂ => Real.log ‖u - z‖ + Real.log ‖u - p‖ -
        Real.log ‖u - a‖)
      (sphere (0 : ℂ) 1) := by
    intro u hu
    have hnorm : ‖u‖ = 1 := by simpa using hu
    have hu0 : u - a ≠ 0 := by
      apply oddStarSeed_denominator_ne_zero_on_circle t ht
      simpa [oddStarSeedUnitCircle] using hu
    have huz : u - z ≠ 0 := by
      intro heq
      have : u = z := sub_eq_zero.mp heq
      rw [this] at hnorm
      linarith
    have hup : u - p ≠ 0 := by
      intro heq
      have : u = p := sub_eq_zero.mp heq
      rw [this] at hnorm
      linarith
    change Real.log ‖oddStarSeed t u - oddStarSeed t z‖ =
      Real.log ‖u - z‖ + Real.log ‖u - p‖ - Real.log ‖u - a‖
    rw [oddStarSeed_difference_factor t ht z u hz0 hu0]
    rw [norm_div, norm_mul]
    rw [Real.log_div
      (mul_ne_zero (norm_ne_zero_iff.mpr huz) (norm_ne_zero_iff.mpr hup))
      (norm_ne_zero_iff.mpr hu0)]
    rw [Real.log_mul (norm_ne_zero_iff.mpr huz) (norm_ne_zero_iff.mpr hup)]
  have h1 : CircleIntegrable (fun u : ℂ => Real.log ‖u - z‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  have h2 : CircleIntegrable (fun u : ℂ => Real.log ‖u - p‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  have h3 : CircleIntegrable (fun u : ℂ => Real.log ‖u - a‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  calc
    Real.circleAverage
        (fun u : ℂ => Real.log ‖oddStarSeed t u - oddStarSeed t z‖) 0 1 =
      Real.circleAverage
        (fun u : ℂ => Real.log ‖u - z‖ + Real.log ‖u - p‖ -
          Real.log ‖u - a‖) 0 1 :=
      Real.circleAverage_congr_sphere (by simpa only [abs_one] using hpoint)
    _ = Real.log ‖z‖ := by
      simp only [← Pi.add_def, ← Pi.sub_def]
      rw [Real.circleAverage_sub (h1.add h2) h3,
        Real.circleAverage_add h1 h2,
        exterior_circleAverage_log_factor z hz,
        oddStarSeedPartner_circleAverage_log_zero t ht z hz,
        oddStarSeedPole_circleAverage_log_zero t ht]
      ring

end SpringerLean

#print axioms SpringerLean.oddStarSeed_boundary_log_potential_exterior
