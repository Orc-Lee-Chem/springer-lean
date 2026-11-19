import SpringerLean.Round290DiagonalForwardFormula
import Mathlib.Algebra.MvPolynomial.Eval

namespace SpringerLean
open PowerSeries

/-- Rational universal forward coefficients. Variable zero is unused,
so the normalization is genuinely centered. -/
noncomputable def universalForwardSeries : PowerSeries (MvPolynomial ℕ ℚ) :=
  PowerSeries.mk (fun n => if n = 0 then 0 else MvPolynomial.X n)

noncomputable def universalLogGrunskyKernel :
    PowerSeries (PowerSeries (MvPolynomial ℕ ℚ)) :=
  -PowerSeries.logOf (1 - formalFaberKernel universalForwardSeries)

noncomputable def actualForwardPolynomialEval (F : ℂ → ℂ) :
    MvPolynomial ℕ ℚ →+* ℂ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ℂ) (exteriorForwardCoeff F)

theorem formalFaberKernel_map
    {A B : Type*} [CommRing A] [CommRing B] (h : A →+* B) (f : PowerSeries A) :
    PowerSeries.map (PowerSeries.map h) (formalFaberKernel f) =
      formalFaberKernel (PowerSeries.map h f) := by
  ext n m
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
      cases m with
      | zero => simp [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff]
      | succ m => simp [PowerSeries.coeff_map]

theorem universalForwardSeries_eval (F : ℂ → ℂ) :
    PowerSeries.map (actualForwardPolynomialEval F) universalForwardSeries =
      exteriorFormalForward F := by
  ext n
  cases n with
  | zero =>
      simp only [PowerSeries.coeff_map, universalForwardSeries, PowerSeries.coeff_mk,
        ite_true, map_zero]
      exact (exteriorFormalForward_coeff_zero F).symm
  | succ n =>
      simp [PowerSeries.coeff_map, universalForwardSeries, actualForwardPolynomialEval,
        exteriorFormalForward_coeff]

/-- Every universal rational Grunsky coefficient evaluates to the actual
logarithmic coefficient of the same F, at all orders. This is the semantic
bridge needed by a rational Gram checker. -/
theorem universalLogGrunskyKernel_eval (F : ℂ → ℂ) :
    PowerSeries.map (PowerSeries.map (actualForwardPolynomialEval F))
      universalLogGrunskyKernel = exteriorFormalGrunskyKernel F := by
  unfold universalLogGrunskyKernel exteriorFormalGrunskyKernel
  rw [map_neg, formal_logOf_map _ _ (by simp), map_sub, map_one,
    formalFaberKernel_map, universalForwardSeries_eval]

theorem universalLogGrunskyCoeff_eval (F : ℂ → ℂ) (i j : ℕ) :
    actualForwardPolynomialEval F
      (PowerSeries.coeff i (PowerSeries.coeff j universalLogGrunskyKernel)) =
        PowerSeries.coeff i (PowerSeries.coeff j (exteriorFormalGrunskyKernel F)) := by
  have h := congrArg (fun Q : PowerSeries (PowerSeries ℂ) =>
    PowerSeries.coeff i (PowerSeries.coeff j Q)) (universalLogGrunskyKernel_eval F)
  simpa only [PowerSeries.coeff_map] using h

noncomputable def universalPhiPowerCoeff (k d : ℕ) : MvPolynomial ℕ ℚ :=
  PowerSeries.coeff d ((1 + PowerSeries.X * universalForwardSeries) ^ k)

theorem universalPhiPowerCoeff_eval (F : ℂ → ℂ) (k d : ℕ) :
    actualForwardPolynomialEval F (universalPhiPowerCoeff k d) =
      PowerSeries.coeff d (formalExteriorPhi (exteriorFormalForward F) ^ k) := by
  change PowerSeries.coeff d (PowerSeries.map (actualForwardPolynomialEval F)
    ((1 + PowerSeries.X * universalForwardSeries) ^ k)) = _
  rw [map_pow, map_add, map_one, map_mul, PowerSeries.map_X, universalForwardSeries_eval]
  rfl

end SpringerLean
