import SpringerLean.Round1958UnitCirclePower

open MeasureTheory

namespace SpringerLean

/-- The seed boundary curve admits continuous real tests in the angular
parameter, even at its two critical points. -/
theorem oddStarSeed_boundary_test_continuous
    (t : ℝ) (ht : |t| < 1) (φ : ℂ → ℝ) (hφ : Continuous φ) :
    Continuous (fun θ : ℝ =>
      φ (oddStarSeed t (Complex.polarCoord.symm (1, θ)))) := by
  apply hφ.comp
  let g : ℝ → ℂ := fun θ => Complex.polarCoord.symm (1, θ)
  have hpolar : Continuous g := by
    dsimp [g]
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hden : ∀ θ : ℝ, g θ - (t : ℂ) * Complex.I ≠ 0 := by
    intro θ
    have hnorm : ‖g θ‖ = 1 := by simp [g]
    apply oddStarSeed_denominator_ne_zero_on_circle t ht
    simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using hnorm
  change Continuous (fun θ : ℝ =>
    (g θ - (t : ℂ) * Complex.I +
      (Real.sqrt (1 - t ^ 2) : ℂ)) ^ 2 /
      (g θ - (t : ℂ) * Complex.I))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact hden

theorem oddStarSeed_boundary_test_periodic
    (t : ℝ) (φ : ℂ → ℝ) :
    Function.Periodic
      (fun θ : ℝ => φ (oddStarSeed t (Complex.polarCoord.symm (1, θ))))
      (2 * Real.pi) := by
  intro θ
  change φ (oddStarSeed t (Complex.polarCoord.symm (1, θ + 2 * Real.pi))) =
    φ (oddStarSeed t (Complex.polarCoord.symm (1, θ)))
  exact congrArg (fun z : ℂ => φ (oddStarSeed t z)) (unitPolar_periodic θ)

/-- The m-fold angle on the seed boundary gives the same integral over
one full circle as the ordinary angular parameter. -/
theorem oddStarSeed_boundary_power_integral_zero_two_pi
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : |t| < 1)
    (φ : ℂ → ℝ) (hφ : Continuous φ) :
    (∫ θ in 0..2 * Real.pi,
      φ (oddStarSeed t ((Complex.polarCoord.symm (1, θ)) ^ m))) =
    ∫ θ in 0..2 * Real.pi,
      φ (oddStarSeed t (Complex.polarCoord.symm (1, θ))) := by
  let f : ℝ → ℝ := fun θ =>
    φ (oddStarSeed t (Complex.polarCoord.symm (1, θ)))
  have hfperiod := oddStarSeed_boundary_test_periodic t φ
  have hfcont := oddStarSeed_boundary_test_continuous t ht φ hφ
  have h := periodic_integral_comp_nat_mul f (2 * Real.pi)
    hfperiod hfcont m hm
  simpa only [f, unitPolar_pow] using h

end SpringerLean

#print axioms SpringerLean.oddStarSeed_boundary_power_integral_zero_two_pi
