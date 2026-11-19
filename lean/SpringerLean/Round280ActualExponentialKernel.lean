import SpringerLean.Round279InverseKernelAlgebra
import SpringerLean.Round274FormalExpLog

namespace SpringerLean
open PowerSeries

/-- The exponential logarithmic kernel, after substitution by the same
actual inverse coordinate in both variables, is exactly the inverse
difference quotient in the project's minus-sign convention. -/
theorem exteriorActual_substituted_exponential_kernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let H := schoberReciprocalSeries (schoberActualInverseSeries F)
    let hH : PowerSeries.constantCoeff H = 0 := by simp [H, schoberReciprocalSeries]
    (PowerSeries.exp (PowerSeries ℂ)).subst
      (formalKernelSubst H hH (exteriorFormalGrunskyKernel F)) =
        1 + formalFaberKernel (schoberActualInverseSeries F) := by
  let H := schoberReciprocalSeries (schoberActualInverseSeries F)
  have hH : PowerSeries.constantCoeff H = 0 := by simp [H, schoberReciprocalSeries]
  let S := formalKernelSubst H hH
  let T := formalFaberKernel (exteriorFormalForward F)
  let A := 1 - S T
  let J := 1 + formalFaberKernel (schoberActualInverseSeries F)
  have hprod : A * J = 1 := exteriorActual_inverse_kernel_product F hc
  have hJ : PowerSeries.constantCoeff J = 1 := by simp [J]
  have hA : PowerSeries.constantCoeff A = 1 := by
    have hh := congrArg PowerSeries.constantCoeff hprod
    simpa only [map_mul, map_one, hJ, mul_one] using hh
  have hlog := formal_logOf_mul A J hA hJ
  rw [hprod, formal_logOf_one] at hlog
  have hQ : S (exteriorFormalGrunskyKernel F) = PowerSeries.logOf J := by
    change S (-PowerSeries.logOf (1 - T)) = _
    rw [map_neg, formalKernelSubst_logOf H hH _ (by simp [T]), map_sub, map_one]
    change -PowerSeries.logOf A = PowerSeries.logOf J
    linear_combination hlog
  change (PowerSeries.exp (PowerSeries ℂ)).subst (S (exteriorFormalGrunskyKernel F)) = J
  rw [hQ, formal_exp_logOf J hJ]

/-- Every diagonal is the actual inverse Laurent coefficient B_(2k+1).
The plus sign on the right is forced by G(w)=w-sum B_j w^(-j). -/
theorem exteriorActual_substituted_exponential_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (k : ℕ) :
    let H := schoberReciprocalSeries (schoberActualInverseSeries F)
    let hH : PowerSeries.constantCoeff H = 0 := by simp [H, schoberReciprocalSeries]
    PowerSeries.coeff (k + 1) (PowerSeries.coeff (k + 1)
      ((PowerSeries.exp (PowerSeries ℂ)).subst
        (formalKernelSubst H hH (exteriorFormalGrunskyKernel F)))) =
      exteriorInverseCoeff F (2 * k + 1) := by
  dsimp only
  rw [exteriorActual_substituted_exponential_kernel F hc]
  simp only [map_add, PowerSeries.coeff_one, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, zero_add,
    formalFaberKernel_coeff_succ, formalFaberKernelRow_coeff_succ]
  change PowerSeries.coeff (k + 1 + k) (schoberActualInverseSeries F) = _
  rw [show k + 1 + k = 2 * k + 1 by omega]
  simp only [schoberActualInverseSeries, actualTaylorSeries_coeff, actualTaylorCoeff_inverse]

end SpringerLean
