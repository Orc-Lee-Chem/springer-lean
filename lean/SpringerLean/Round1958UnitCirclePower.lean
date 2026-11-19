import SpringerLean.Round1957PeriodicPowerAverage

namespace SpringerLean

/-- The polar unit-circle parametrization is the complex exponential. -/
theorem unitPolar_eq_exp (θ : ℝ) :
    Complex.polarCoord.symm (1, θ) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
  simp [Complex.polarCoord_symm_apply, Complex.exp_mul_I]

/-- Integer powers multiply the circular angle exactly. -/
theorem unitPolar_pow (m : ℕ) (θ : ℝ) :
    (Complex.polarCoord.symm (1, θ)) ^ m =
      Complex.polarCoord.symm (1, (m : ℝ) * θ) := by
  rw [unitPolar_eq_exp, unitPolar_eq_exp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem unitPolar_periodic :
    Function.Periodic
      (fun θ : ℝ => Complex.polarCoord.symm (1, θ))
      (2 * Real.pi) := by
  intro θ
  simp only [unitPolar_eq_exp]
  convert Complex.exp_mul_I_periodic (θ : ℂ) using 1 <;>
    push_cast <;> ring

end SpringerLean

#print axioms SpringerLean.unitPolar_pow
#print axioms SpringerLean.unitPolar_periodic
