import SpringerLean.Round1959SeedAngleAverage

open MeasureTheory Set

namespace SpringerLean

/-- The integer-angle invariance over the centered full-circle interval,
in the exact set-integral form used by the actual radial trace. -/
theorem periodic_setIntegral_comp_nat_mul_centered
    (f : ℝ → ℝ) (hf : Function.Periodic f (2 * Real.pi))
    (hcont : Continuous f) (m : ℕ) (hm : 0 < m) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f ((m : ℝ) * θ)) =
      ∫ θ in Ioo (-Real.pi) Real.pi, f θ := by
  have hfm : Function.Periodic (fun θ : ℝ => f ((m : ℝ) * θ))
      (2 * Real.pi) := by
    intro θ
    have h := (hf.nsmul m) ((m : ℝ) * θ)
    simpa [nsmul_eq_mul, mul_add, mul_assoc] using h
  have hshift (g : ℝ → ℝ) (hg : Function.Periodic g (2 * Real.pi)) :
      (∫ θ in -Real.pi..Real.pi, g θ) =
        ∫ θ in 0..2 * Real.pi, g θ := by
    convert hg.intervalIntegral_add_eq (-Real.pi) 0 using 1 <;> ring
  have hcenter :
      (∫ θ in -Real.pi..Real.pi, f ((m : ℝ) * θ)) =
        ∫ θ in -Real.pi..Real.pi, f θ := by
    calc
      _ = ∫ θ in 0..2 * Real.pi, f ((m : ℝ) * θ) :=
        hshift _ hfm
      _ = ∫ θ in 0..2 * Real.pi, f θ :=
        periodic_integral_comp_nat_mul f (2 * Real.pi) hf hcont m hm
      _ = ∫ θ in -Real.pi..Real.pi, f θ :=
        (hshift _ hf).symm
  have hset (g : ℝ → ℝ) :
      (∫ θ in Ioo (-Real.pi) Real.pi, g θ) =
        ∫ θ in -Real.pi..Real.pi, g θ := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
  rw [hset, hset]
  exact hcenter

/-- The continuous seed boundary test has the same centered angular
integral after the m-th power of the unit-circle point. -/
theorem oddStarSeed_boundary_power_setIntegral_eq
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : |t| < 1)
    (φ : ℂ → ℝ) (hφ : Continuous φ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      φ (oddStarSeed t ((Complex.polarCoord.symm (1, θ)) ^ m))) =
    ∫ θ in Ioo (-Real.pi) Real.pi,
      φ (oddStarSeed t (Complex.polarCoord.symm (1, θ))) := by
  let f : ℝ → ℝ := fun θ =>
    φ (oddStarSeed t (Complex.polarCoord.symm (1, θ)))
  have h := periodic_setIntegral_comp_nat_mul_centered f
    (oddStarSeed_boundary_test_periodic t φ)
    (oddStarSeed_boundary_test_continuous t ht φ hφ) m hm
  simpa only [f, unitPolar_pow] using h

end SpringerLean

#print axioms SpringerLean.periodic_setIntegral_comp_nat_mul_centered
#print axioms SpringerLean.oddStarSeed_boundary_power_setIntegral_eq
