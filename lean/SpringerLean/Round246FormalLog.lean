import Mathlib.RingTheory.PowerSeries.Log

namespace SpringerLean

open PowerSeries

/-- Coefficient-ring maps preserve the formal logarithm at normalized
units. This permits polynomial-valued Faber identities to be evaluated
in the same actual forward formal series. -/
theorem formal_logOf_map
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (h : A →+* B) (f : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1) :
    PowerSeries.map h (PowerSeries.logOf f) =
      PowerSeries.logOf (PowerSeries.map h f) := by
  have hsubst : PowerSeries.HasSubst (f - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hf])
  have hm : PowerSeries.map h ((PowerSeries.log A).subst (f - 1)) =
      (PowerSeries.map h (PowerSeries.log A)).subst
        (PowerSeries.map h (f - 1)) :=
    PowerSeries.map_subst hsubst (PowerSeries.log A)
  rw [PowerSeries.logOf_eq, hm,
    PowerSeries.map_log, PowerSeries.logOf_eq]
  congr 1
  simp

/-- Formal logarithmic differentiation at a series with constant term one.
This is used to identify Faber generating series uniformly in the order. -/
theorem formal_logOf_derivative_mul
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) :
    PowerSeries.derivative (PowerSeries.logOf f) * f =
      PowerSeries.derivative f := by
  have hsubst : PowerSeries.HasSubst (f - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hf])
  have hlog :
      (PowerSeries.derivative (PowerSeries.log A)).subst (f - 1) * f = 1 := by
    have h := congrArg (PowerSeries.substAlgHom hsubst)
      (PowerSeries.derivative_log_mul_one_add_X (A := A))
    rw [map_mul, map_add, map_one, PowerSeries.substAlgHom_X] at h
    rw [show (1 : PowerSeries A) + (f - 1) = f by ring] at h
    simpa only [PowerSeries.coe_substAlgHom] using h
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst hsubst]
  simp only [map_sub, PowerSeries.derivative_one, sub_zero]
  calc
    _ = ((PowerSeries.derivative (PowerSeries.log A)).subst (f - 1) * f) *
        PowerSeries.derivative f := by ring
    _ = _ := by rw [hlog]; simp

/-- Multiplicativity of the formal logarithm at units normalized to one.
No convergence or analytic hypothesis is encoded in this algebraic lemma. -/
theorem formal_logOf_mul
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (f g : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.logOf (f * g) =
      PowerSeries.logOf f + PowerSeries.logOf g := by
  haveI : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  have hfg : PowerSeries.constantCoeff (f * g) = 1 := by simp [hf, hg]
  have hunit : IsUnit (f * g) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hfg])
  apply PowerSeries.derivative.ext
  · apply hunit.mul_left_cancel
    have hF := formal_logOf_derivative_mul f hf
    have hG := formal_logOf_derivative_mul g hg
    have hFG := formal_logOf_derivative_mul (f * g) hfg
    calc
      _ = PowerSeries.derivative (PowerSeries.logOf (f * g)) * (f * g) := by ring
      _ = PowerSeries.derivative (f * g) := hFG
      _ = PowerSeries.derivative f * g + f * PowerSeries.derivative g := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
        ring
      _ = (PowerSeries.derivative (PowerSeries.logOf f) * f) * g +
          f * (PowerSeries.derivative (PowerSeries.logOf g) * g) := by rw [hF, hG]
      _ = (f * g) *
          PowerSeries.derivative (PowerSeries.logOf f + PowerSeries.logOf g) := by
        rw [map_add]
        ring
  · simp [PowerSeries.constantCoeff_logOf hf,
      PowerSeries.constantCoeff_logOf hg,
      PowerSeries.constantCoeff_logOf hfg]

/-- The common logarithmic-kernel differential identity, valid at every
order, rather than a separately expanded finite matrix row. -/
theorem formal_negative_log_derivative_mul
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (T : PowerSeries A) (hT : PowerSeries.constantCoeff T = 0) :
    PowerSeries.derivative (-PowerSeries.logOf (1 - T)) * (1 - T) =
      PowerSeries.derivative T := by
  have h := formal_logOf_derivative_mul (1 - T) (by simp [hT])
  simp only [map_sub, PowerSeries.derivative_one, zero_sub] at h
  rw [map_neg]
  calc
    _ = -(PowerSeries.derivative (PowerSeries.logOf (1 - T)) * (1 - T)) := by ring
    _ = _ := by rw [h]; simp

/-- Coefficient recurrence for the logarithmic kernel over any rational
commutative algebra. It retains the finite Cauchy product exactly. -/
theorem formal_negative_log_coeff_recurrence
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (T : PowerSeries A) (hT : PowerSeries.constantCoeff T = 0)
    (n : ℕ) :
    let Q := -PowerSeries.logOf (1 - T)
    ((n + 1 : ℕ) : A) * PowerSeries.coeff (n + 1) Q =
      ((n + 1 : ℕ) : A) * PowerSeries.coeff (n + 1) T +
      ∑ ij ∈ Finset.antidiagonal n,
        (((ij.1 + 1 : ℕ) : A) * PowerSeries.coeff (ij.1 + 1) Q) *
          PowerSeries.coeff ij.2 T := by
  let Q := -PowerSeries.logOf (1 - T)
  have h := formal_negative_log_derivative_mul T hT
  change PowerSeries.derivative Q * (1 - T) = PowerSeries.derivative T at h
  have hD : PowerSeries.derivative Q =
      PowerSeries.derivative T + PowerSeries.derivative Q * T := by
    calc
      _ = PowerSeries.derivative Q * (1 - T) + PowerSeries.derivative Q * T := by ring
      _ = _ := by rw [h]
  have hc := congrArg (PowerSeries.coeff n) hD
  simp only [map_add, PowerSeries.coeff_mul,
    PowerSeries.coeff_derivative] at hc
  simpa [Q, mul_comm, mul_left_comm, mul_assoc] using hc

end SpringerLean
