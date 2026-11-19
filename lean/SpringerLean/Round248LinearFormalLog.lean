import SpringerLean.Round247FormalFaberKernel

namespace SpringerLean
open PowerSeries

/-- Exact coefficients of the linear logarithmic factor, without
expanding a separate logarithmic polynomial at each order. -/
theorem formal_linear_log_coeff_succ
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (p : A) (n : ℕ) :
    ((n + 1 : ℕ) : A) *
        PowerSeries.coeff (n + 1)
          (-PowerSeries.logOf (1 - PowerSeries.C p * PowerSeries.X)) =
      p ^ (n + 1) := by
  let Q := -PowerSeries.logOf
    (1 - PowerSeries.C p * PowerSeries.X : PowerSeries A)
  have h := formal_negative_log_derivative_mul
    (PowerSeries.C p * PowerSeries.X) (by simp)
  change PowerSeries.derivative Q *
    (1 - PowerSeries.C p * PowerSeries.X) = _ at h
  have hlin : PowerSeries.derivative
      (PowerSeries.C p * PowerSeries.X) = PowerSeries.C p := by
    rw [Derivation.leibniz]
    simp [smul_eq_mul]
  rw [hlin] at h
  have hD : PowerSeries.derivative Q =
      PowerSeries.C p + PowerSeries.C p *
        (PowerSeries.X * PowerSeries.derivative Q) := by
    calc
      _ = PowerSeries.derivative Q *
            (1 - PowerSeries.C p * PowerSeries.X) +
          PowerSeries.C p * (PowerSeries.X * PowerSeries.derivative Q) := by ring
      _ = _ := by rw [h]
  change ((n + 1 : ℕ) : A) * PowerSeries.coeff (n + 1) Q = _
  induction n with
  | zero =>
      have hc := congrArg (PowerSeries.coeff 0) hD
      simpa [PowerSeries.coeff_C_mul,
        PowerSeries.coeff_derivative] using hc
  | succ n ih =>
      have hc := congrArg (PowerSeries.coeff (n + 1)) hD
      simp only [map_add, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_derivative] at hc
      simp [PowerSeries.coeff_C] at hc
      calc
        _ = p * (((n + 1 : ℕ) : A) * PowerSeries.coeff (n + 1) Q) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hc
        _ = p * p ^ (n + 1) := by rw [ih]
        _ = _ := by rw [pow_succ]; ring

end SpringerLean
