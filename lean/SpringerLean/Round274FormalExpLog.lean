import SpringerLean.Round266FiniteFormalLog

namespace SpringerLean
open PowerSeries

/-- Formal exponential of a normalized logarithm. The identity holds in
every rational commutative algebra, including nested power series. -/
theorem formal_exp_logOf
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) :
    (PowerSeries.exp A).subst (PowerSeries.logOf f) = f := by
  have hs : PowerSeries.HasSubst (f - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hf])
  rw [PowerSeries.logOf_eq,
    ← PowerSeries.subst_comp_subst_apply PowerSeries.HasSubst.log hs,
    PowerSeries.subst_exp_log, PowerSeries.subst_add hs]
  simp only [← PowerSeries.coe_substAlgHom hs, map_one,
    PowerSeries.substAlgHom_X]
  ring

theorem formal_logOf_one
    {A : Type*} [CommRing A] [Algebra ℚ A] :
    PowerSeries.logOf (1 : PowerSeries A) = 0 := by
  rw [PowerSeries.logOf_eq, sub_self]
  exact PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log

/-- The exponential kernel is the genuine inverse difference quotient,
rather than a formal polynomial asserted to have the desired diagonal. -/
theorem formal_exp_negative_log
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (T : PowerSeries A) (hT : PowerSeries.constantCoeff T = 0) :
    (PowerSeries.exp A).subst (-PowerSeries.logOf (1 - T)) =
      PowerSeries.invOfUnit (1 - T) 1 := by
  let I := PowerSeries.invOfUnit (1 - T) (1 : Aˣ)
  have hI : PowerSeries.constantCoeff I = 1 := by
    simp [I, PowerSeries.constantCoeff_invOfUnit]
  have hprod : (1 - T) * I = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp [hT])
  have hlog := formal_logOf_mul (1 - T) I (by simp [hT]) hI
  rw [hprod, formal_logOf_one] at hlog
  have heq : -PowerSeries.logOf (1 - T) = PowerSeries.logOf I := by
    linear_combination hlog
  rw [heq, formal_exp_logOf I hI]

theorem formal_exp_coeff_finite
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (Q : PowerSeries A) (hQ : PowerSeries.constantCoeff Q = 0) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.exp A).subst Q) =
      ∑ d ∈ Finset.range (n + 1),
        algebraMap ℚ A (1 / (d.factorial : ℚ)) * PowerSeries.coeff n (Q ^ d) := by
  rw [formal_coeff_subst_finite _ Q hQ n]
  simp only [PowerSeries.coeff_exp]

end SpringerLean
