import SpringerLean.Round295CoefficientExpressions
import SpringerLean.Round293ActualGramDeficits

namespace SpringerLean
open PowerSeries RatPolyCheck



noncomputable def actualCoeffVariable (F : ℂ → ℂ) (v : Bool × ℕ) : ℂ :=
  if v.1 then star (exteriorForwardCoeff F v.2) else exteriorForwardCoeff F v.2



theorem phiCoeffExpr_sound (F : ℂ → ℂ) (n : ℕ) :
    (phiCoeffExpr n).eval (actualCoeffVariable F) =
      PowerSeries.coeff n (formalExteriorPhi (exteriorFormalForward F)) := by
  cases n with
  | zero => simp [phiCoeffExpr, Expr.eval, formalExteriorPhi]
  | succ n =>
      cases n with
      | zero =>
          simp [phiCoeffExpr, Expr.eval, formalExteriorPhi,
            PowerSeries.coeff_succ_X_mul, exteriorFormalForward_coeff, exteriorForwardCoeff_zero]
      | succ n =>
          simp [phiCoeffExpr, Expr.eval, actualCoeffVariable, formalExteriorPhi,
            PowerSeries.coeff_succ_X_mul, exteriorFormalForward_coeff]

theorem phiPowerCoeffExpr_sound (F : ℂ → ℂ) (k n : ℕ) :
    (powerCoeffExpr phiCoeffExpr k n).eval (actualCoeffVariable F) =
      PowerSeries.coeff n (formalExteriorPhi (exteriorFormalForward F) ^ k) :=
  powerCoeffExpr_sound _ _ _ (phiCoeffExpr_sound F) k n



theorem forwardKernelCoeffExpr_sound (F : ℂ → ℂ) (i j : ℕ) :
    (forwardKernelCoeffExpr i j).eval (actualCoeffVariable F) =
      PowerSeries.coeff i (PowerSeries.coeff j
        (formalFaberKernel (exteriorFormalForward F))) := by
  cases i with
  | zero =>
      cases j with
      | zero => simp [forwardKernelCoeffExpr, Expr.eval, PowerSeries.coeff_zero_eq_constantCoeff]
      | succ j => simp [forwardKernelCoeffExpr, Expr.eval, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ i =>
      cases j with
      | zero => simp [forwardKernelCoeffExpr, Expr.eval, PowerSeries.coeff_zero_eq_constantCoeff]
      | succ j =>
          simp [forwardKernelCoeffExpr, Expr.eval, actualCoeffVariable,
            exteriorFormalForward_coeff, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem forwardKernelPowerCoeffExpr_sound (F : ℂ → ℂ) (d i j : ℕ) :
    (bipowerCoeffExpr forwardKernelCoeffExpr d i j).eval (actualCoeffVariable F) =
      PowerSeries.coeff i (PowerSeries.coeff j
        (formalFaberKernel (exteriorFormalForward F) ^ d)) :=
  bipowerCoeffExpr_sound _ _ _ (forwardKernelCoeffExpr_sound F) d i j



theorem formalNegativeLogSeries_coeff_C_inverse (d : ℕ) :
    PowerSeries.coeff d (formalNegativeLogSeries (PowerSeries ℂ)) =
      PowerSeries.C ((d : ℂ)⁻¹) := by
  cases d with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ d =>
      rw [formalNegativeLogSeries_coeff_inner, formalNegativeLogSeries_coeff_succ]
      simp

/-- The executable log-kernel coefficient generator reads the actual
Grunsky coefficient, not an independent or hypothesized matrix. -/
theorem logGrunskyCoeffExpr_sound (F : ℂ → ℂ) (i j : ℕ) :
    (logGrunskyCoeffExpr i j).eval (actualCoeffVariable F) =
      PowerSeries.coeff i (PowerSeries.coeff j (exteriorFormalGrunskyKernel F)) := by
  rw [logGrunskyCoeffExpr, Expr.fsum_eval]
  symm
  unfold exteriorFormalGrunskyKernel
  rw [formal_negative_log_coeff_finite _ (by simp) j j le_rfl]
  simp only [map_sum, formalNegativeLogSeries_coeff_C_inverse, PowerSeries.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Expr.eval, forwardKernelPowerCoeffExpr_sound]
  simp [Expr.eval]



theorem CoeffExpr.conjugate_sound (F : ℂ → ℂ) (e : CoeffExpr) :
    e.conjugate.eval (actualCoeffVariable F) = star (e.eval (actualCoeffVariable F)) := by
  induction e with
  | const q => simp [conjugate, Expr.eval]
  | var v =>
      rcases v with ⟨b, n⟩
      cases b <;> simp [conjugate, Expr.eval, actualCoeffVariable]
  | add e f he hf => simp [conjugate, Expr.eval, he, hf]
  | mul e f he hf => simp [conjugate, Expr.eval, he, hf, mul_comm]



theorem CoeffExpr.normSq_sound (F : ℂ → ℂ) (e : CoeffExpr) :
    e.normSq.eval (actualCoeffVariable F) =
      ((‖e.eval (actualCoeffVariable F)‖ ^ 2 : ℝ) : ℂ) := by
  rw [normSq, Expr.eval, conjugate_sound]
  simpa only [Complex.ofReal_pow, starRingEnd_apply] using
    Complex.mul_conj' (e.eval (actualCoeffVariable F))



theorem schoberDiagonalExpr_sound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n : ℕ) :
    (schoberDiagonalExpr (n + 1)).eval (actualCoeffVariable F) =
      ((schoberActualDiagonal F (n + 1) : ℝ) : ℂ) := by
  rw [schoberDiagonalExpr, Expr.fsum_eval, schoberActualDiagonal_forward_formula F hc n]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [Expr.eval, CoeffExpr.normSq_sound, phiPowerCoeffExpr_sound]
  simp only [Expr.eval, map_pow, map_div₀, map_natCast]
  push_cast
  rfl

end SpringerLean
