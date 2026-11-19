import SpringerLean.GeneralInverse
import Mathlib.RingTheory.PowerSeries.Derivative

namespace SpringerLean

open PowerSeries

/-- The formal factor corresponding to F(z)=z+f(1/z). -/
noncomputable def formalExteriorPhi (f : PowerSeries ℂ) : PowerSeries ℂ :=
  1 + PowerSeries.X * f

private theorem formalExteriorPhi_derivative (f : PowerSeries ℂ) :
    PowerSeries.derivative (formalExteriorPhi f) =
      f + PowerSeries.X * PowerSeries.derivative f := by
  unfold formalExteriorPhi
  rw [map_add, PowerSeries.derivative_one, zero_add]
  rw [PowerSeries.derivative.leibniz]
  simp [PowerSeries.derivative_X, smul_eq_mul]
  ring

/-- The coefficient cancellation in the second half of Lagrange inversion. -/
theorem formalExteriorPhi_residue_identity (f : PowerSeries ℂ) (k : ℕ) :
    PowerSeries.coeff k
        (PowerSeries.derivative f * (formalExteriorPhi f) ^ (k + 1)) =
      PowerSeries.coeff (k + 2) ((formalExteriorPhi f) ^ (k + 1)) := by
  let φ := formalExteriorPhi f
  have hdphi : PowerSeries.derivative φ =
      f + PowerSeries.X * PowerSeries.derivative f :=
    formalExteriorPhi_derivative f
  have hring : PowerSeries.X ^ 2 * (PowerSeries.derivative f * φ ^ (k + 1)) =
      PowerSeries.X * (PowerSeries.derivative φ * φ ^ (k + 1)) -
        φ ^ (k + 2) + φ ^ (k + 1) := by
    rw [hdphi]
    dsimp [φ, formalExteriorPhi]
    ring
  have hder : PowerSeries.coeff (k + 1)
      (PowerSeries.derivative φ * φ ^ (k + 1)) =
      PowerSeries.coeff (k + 2) (φ ^ (k + 2)) := by
    have h := congrArg (PowerSeries.coeff (k + 1))
      (PowerSeries.derivative_pow φ (k + 2))
    simp only [PowerSeries.coeff_derivative] at h
    have hk : (k + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 2 ≠ 0)
    have h' :
        (k + 2 : ℂ) * PowerSeries.coeff (k + 2) (φ ^ (k + 2)) =
        (k + 2 : ℂ) * PowerSeries.coeff (k + 1)
          (PowerSeries.derivative φ * φ ^ (k + 1)) := by
      convert h using 1
      · have hidx : k + 1 + 1 = k + 2 := by omega
        rw [hidx]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      · have hidx : k + 2 - 1 = k + 1 := by omega
        have heq :
            ((k + 2 : PowerSeries ℂ) * φ ^ (k + 2 - 1) *
              PowerSeries.derivative φ) =
              (k + 2 : PowerSeries ℂ) *
                (PowerSeries.derivative φ * φ ^ (k + 1)) := by
          rw [hidx]
          ring
        have hcast : ((k + 2 : ℕ) : PowerSeries ℂ) = (k : PowerSeries ℂ) + 2 := by norm_cast
        rw [← hcast] at heq
        rw [heq, PowerSeries.coeff_natCast_mul]
        norm_cast
    exact (mul_left_cancel₀ hk h').symm
  have hc := congrArg (PowerSeries.coeff (k + 2)) hring
  simp only [map_add, map_sub] at hc
  have hleft : PowerSeries.coeff (k + 2)
      (PowerSeries.X ^ 2 * (PowerSeries.derivative f * φ ^ (k + 1))) =
      PowerSeries.coeff k (PowerSeries.derivative f * φ ^ (k + 1)) := by
    simpa only [show k + 2 = k + 2 by rfl] using
      (PowerSeries.coeff_X_pow_mul
        (PowerSeries.derivative f * φ ^ (k + 1)) 2 k)
  have hright : PowerSeries.coeff (k + 2)
      (PowerSeries.X * (PowerSeries.derivative φ * φ ^ (k + 1))) =
      PowerSeries.coeff (k + 1)
        (PowerSeries.derivative φ * φ ^ (k + 1)) := by
    exact (PowerSeries.coeff_succ_X_mul (k + 1)
        (PowerSeries.derivative φ * φ ^ (k + 1)))
  rw [hleft, hright, hder] at hc
  simpa using hc

/-- Formal forward Laurent correction, with coefficients independently read
from the actual function F at infinity. -/
noncomputable def exteriorFormalForward (F : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (exteriorForwardCoeff F)

theorem exteriorFormalForward_coeff (F : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (exteriorFormalForward F) = exteriorForwardCoeff F n := by
  simp [exteriorFormalForward]

/-- The formal expression for the z⁻¹ coefficient of F(z)^n. -/
noncomputable def exteriorFormalResidue (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  PowerSeries.coeff (n + 1)
    ((formalExteriorPhi (exteriorFormalForward F)) ^ n)

theorem formalExteriorPhi_coeff_two (f : PowerSeries ℂ) :
    PowerSeries.coeff 2 (formalExteriorPhi f) = PowerSeries.coeff 1 f := by
  simp [formalExteriorPhi, PowerSeries.coeff_succ_X_mul]

theorem exteriorFormalResidue_one (F : ℂ → ℂ) :
    exteriorFormalResidue F 1 = exteriorForwardCoeff F 1 := by
  simpa [exteriorFormalResidue, exteriorFormalForward_coeff] using
    (formalExteriorPhi_coeff_two (exteriorFormalForward F))

/-- The n=1 case of the inverse/residue formula for every paper-class map. -/
theorem exteriorInverseCoeff_one_eq_formalResidue (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 1 = exteriorFormalResidue F 1 := by
  rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc, exteriorFormalResidue_one]
end SpringerLean