import SpringerLean.Round265AllFiniteGrunsky
import SpringerLean.Round296ActualCoefficientExpressions
import SpringerLean.LowOrder

namespace SpringerLean
open RatPolyCheck

theorem exteriorFormalGrunskyCoeff_two_two (F : ℂ → ℂ) :
    PowerSeries.coeff 2 (PowerSeries.coeff 2 (exteriorFormalGrunskyKernel F)) =
      exteriorForwardCoeff F 3 + (1 / 2 : ℂ) * exteriorForwardCoeff F 1 ^ 2 := by
  have h := logGrunskyCoeffExpr_sound F 2 2
  have he : (logGrunskyCoeffExpr 2 2).eval (actualCoeffVariable F) =
      exteriorForwardCoeff F 3 + (1 / 2 : ℂ) * exteriorForwardCoeff F 1 ^ 2 := by
    norm_num [logGrunskyCoeffExpr, Expr.fsum, bipowerCoeffExpr,
      forwardKernelCoeffExpr, Expr.mulUnlessRightZero, Expr.smartMulLeft,
      Expr.smartAdd, Expr.smartAddLeft, Expr.eval, actualCoeffVariable]
    ring
  exact h.symm.trans he

theorem exteriorInverseCoeff_three_norm_le_half_one_add_sq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 3‖ ≤ (1 + ‖exteriorForwardCoeff F 1‖ ^ 2) / 2 := by
  have h := exterior_generalGrunsky_weighted_contraction F hc 2 ![0, 1]
  norm_num [Fin.sum_univ_succ, exteriorFormalGrunskyCoeff_two_two,
    norm_mul] at h
  have hc22 : ‖PowerSeries.coeff 2 (PowerSeries.coeff 2
      (exteriorFormalGrunskyKernel F))‖ ≤ (1 / 2 : ℝ) := by
    rw [exteriorFormalGrunskyCoeff_two_two]
    nlinarith [sq_nonneg ‖PowerSeries.coeff 1 (PowerSeries.coeff 2
      (exteriorFormalGrunskyKernel F))‖,
      norm_nonneg (exteriorForwardCoeff F 3 +
        (1 / 2 : ℂ) * exteriorForwardCoeff F 1 ^ 2)]
  calc
    _ = ‖PowerSeries.coeff 2 (PowerSeries.coeff 2 (exteriorFormalGrunskyKernel F)) +
        (1 / 2 : ℂ) * exteriorForwardCoeff F 1 ^ 2‖ := by
      congr 1
      rw [exteriorInverseCoeff_three_eq_forward F hc,
        exteriorFormalGrunskyCoeff_two_two]
      ring
    _ ≤ ‖PowerSeries.coeff 2 (PowerSeries.coeff 2 (exteriorFormalGrunskyKernel F))‖ +
        ‖(1 / 2 : ℂ) * exteriorForwardCoeff F 1 ^ 2‖ := norm_add_le _ _
    _ ≤ (1 + ‖exteriorForwardCoeff F 1‖ ^ 2) / 2 := by
      norm_num [norm_mul, norm_pow]
      linarith

end SpringerLean
