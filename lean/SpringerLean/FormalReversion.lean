import SpringerLean.FormalResidue
import Mathlib.RingTheory.PowerSeries.Derivative

namespace SpringerLean

open PowerSeries

/-- The algebraic cancellation in the induction step of Lagrange inversion. -/
theorem formal_reversion_derivative_identity (phi q : PowerSeries ℂ) (k : ℕ) :
    PowerSeries.derivative (q * phi ^ (k + 2)) +
        (k + 1 : PowerSeries ℂ) *
          (PowerSeries.derivative q * phi ^ (k + 2)) =
      (k + 2 : PowerSeries ℂ) *
        (PowerSeries.derivative (phi * q) * phi ^ (k + 1)) := by
  rw [PowerSeries.derivative.leibniz, PowerSeries.derivative_pow,
    PowerSeries.derivative.leibniz]
  push_cast
  ring

/-- The coefficient identity used to pass from order k+1 to order k+2. -/
theorem formal_reversion_induction_algebra (phi q : PowerSeries ℂ) (k : ℕ) :
    (k + 1 : ℂ) * PowerSeries.coeff (k + 1)
      ((q + PowerSeries.X * PowerSeries.derivative q) * phi ^ (k + 2)) =
    (k + 2 : ℂ) * PowerSeries.coeff k
      (PowerSeries.derivative (phi * q) * phi ^ (k + 1)) := by
  have hid := congrArg (PowerSeries.coeff k)
    (formal_reversion_derivative_identity phi q k)
  simp only [map_add, PowerSeries.coeff_derivative] at hid
  simp only [add_mul, map_add,
    PowerSeries.coeff_natCast_mul, one_mul] at hid
  have hshift :
      PowerSeries.coeff (k + 1)
        ((PowerSeries.X * PowerSeries.derivative q) * phi ^ (k + 2)) =
      PowerSeries.coeff k (PowerSeries.derivative q * phi ^ (k + 2)) := by
    rw [mul_assoc]
    exact PowerSeries.coeff_succ_X_mul k _
  simp only [add_mul, map_add, hshift]
  ring_nf at hid ⊢
  simp only [PowerSeries.coeff_mul_ofNat] at hid ⊢
  simpa only [mul_comm] using hid

end SpringerLean