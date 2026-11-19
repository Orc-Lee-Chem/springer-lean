import SpringerLean.Round1592ActualAntiholomorphicSecondDerivative

open scoped ComplexConjugate

namespace SpringerLean

/-- The actual first derivative of `beta * H^(k-1)`, the coefficient
appearing in both Cartesian derivatives of the phase field. -/
theorem actualHarmonic_phasePower_hasFDerivAt_real
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasFDerivAt
      (fun w : ℂ => beta * (actualHarmonic F w)^(k-1))
      (((((k-1:ℕ):ℂ) * beta *
        (actualHarmonic F z)^((k-1)-1)) •
          ((1 : ℂ →L[ℝ] ℂ) +
            ((deriv (exteriorForwardGerm F) (conj z)) •
              (1 : ℂ →L[ℝ] ℂ)).comp
                Complex.conjCLE.toContinuousLinearMap))) z := by
  have hH := actualHarmonic_hasFDerivAt_real F hc hz
  have hpow := hH.pow (k-1)
  have hphase := hpow.const_mul beta
  convert hphase using 1
  ext w
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- Its horizontal and vertical derivatives have exactly the phases
needed for the Laplacian calculation. -/
theorem actualHarmonic_phasePower_gradient_coordinates
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (fderiv ℝ (fun w : ℂ => beta*(actualHarmonic F w)^(k-1)) z)
        (1:ℂ) =
      beta*((k:ℂ)-1)*(actualHarmonic F z)^(k-2)*
        (1+deriv (exteriorForwardGerm F) (conj z)) ∧
    (fderiv ℝ (fun w : ℂ => beta*(actualHarmonic F w)^(k-1)) z)
        Complex.I =
      beta*((k:ℂ)-1)*(actualHarmonic F z)^(k-2)*
        (Complex.I*(1-deriv (exteriorForwardGerm F) (conj z))) := by
  have h :=
    (actualHarmonic_phasePower_hasFDerivAt_real F hc k beta hz).fderiv
  have hidx : (k-1:ℕ)-1 = k-2 := by omega
  have hcast : (((k-1:ℕ):ℂ)) = (k:ℂ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    simp
  constructor
  · rw [h]
    simp [hidx, hcast, mul_assoc, mul_comm, mul_left_comm]
    ring
  · rw [h]
    simp [hidx, hcast, Complex.conj_I, mul_assoc, mul_comm,
      mul_left_comm]
    ring

end SpringerLean

#print axioms SpringerLean.actualHarmonic_phasePower_hasFDerivAt_real
#print axioms SpringerLean.actualHarmonic_phasePower_gradient_coordinates
