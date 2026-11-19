import SpringerLean.Round1721ActualFillingLocalLinearZero

open scoped ComplexConjugate

namespace SpringerLean

/-- Each Cartesian derivative of the actual phase field is controlled
by the (k-1)st power of the filling and the local analytic derivative.
This is the explicit pointwise estimate needed at filling zeros. -/
theorem actualHarmonicPhase_gradient_coordinates_abs_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    |(fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1 : ℂ)| ≤
      (k : ℝ) * ‖actualHarmonic F z‖^(k - 1) *
        (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) ∧
    |(fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I| ≤
      (k : ℝ) * ‖actualHarmonic F z‖^(k - 1) *
        (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) := by
  let H := actualHarmonic F z
  let c := deriv (exteriorForwardGerm F) (conj z)
  let W := (k : ℂ) * beta * H^(k - 1)
  have hW : ‖W‖ = (k : ℝ) * ‖H‖^(k - 1) := by
    simp [W, norm_mul, hbeta, norm_pow, mul_assoc]
  obtain ⟨hx, hy⟩ :=
    actualHarmonicPhaseField_gradient_coordinates F hc k beta hz
  constructor
  · rw [hx]
    calc
      |(W * (1 + c)).im| ≤ ‖W * (1 + c)‖ :=
        Complex.abs_im_le_norm _
      _ = ‖W‖ * ‖1 + c‖ := norm_mul _ _
      _ ≤ ‖W‖ * (1 + ‖c‖) := by
        gcongr
        simpa using norm_add_le (1 : ℂ) c
      _ = (k : ℝ) * ‖H‖^(k - 1) * (1 + ‖c‖) := by rw [hW]
  · rw [hy]
    calc
      |(W * (1 - c)).re| ≤ ‖W * (1 - c)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖W‖ * ‖1 - c‖ := norm_mul _ _
      _ ≤ ‖W‖ * (1 + ‖c‖) := by
        gcongr
        simpa using norm_sub_le (1 : ℂ) c
      _ = (k : ℝ) * ‖H‖^(k - 1) * (1 + ‖c‖) := by rw [hW]

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_gradient_coordinates_abs_le
