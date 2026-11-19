import SpringerLean.Round1321ImaginaryRootIdentity
import SpringerLean.Round633ActualOddTailBound

namespace SpringerLean
set_option Elab.async false

theorem largeRootM_le_49_24 {R : ℝ} (hR0 : 0 ≤ R) (hR2 : R ≤ 2) :
    largeRootRadius + (R/2)/largeRootRadius ≤ (49/24 : ℝ) := by
  have hr := largeRootRadius_gt_one
  have hru := largeRootRadius_le_25_24
  have hA : R/2 ≤ 1 := by linarith
  have hdiv : (R/2)/largeRootRadius ≤ 1 :=
    (div_le_iff₀ (by linarith : 0 < largeRootRadius)).2 (by linarith)
  linarith

/-- At the single imaginary source point, the entire odd-root tail is
below 3/40. The exact kernel is log 7 - 24/25 < 1. -/
theorem odd_root_imaginary_tail_lt_three_fortieths
    (H : ℂ → ℂ) (hc : CenteredExteriorUnivalent H)
    (hodd : ∀ z, H (-z) = -H z)
    {R : ℝ} (hR0 : 0 ≤ R) (hR2 : R ≤ 2)
    (hb : exteriorForwardCoeff H 1 = -(R : ℂ)/2)
    (hdef : 1-(R/2)^2 < (1/180 : ℝ)) :
    ‖H (Complex.I*(largeRootRadius : ℂ))-
        Complex.I*((largeRootRadius + (R/2)/largeRootRadius : ℝ) : ℂ)‖ <
      (3/40 : ℝ) := by
  let r : ℝ := largeRootRadius
  let z : ℂ := Complex.I*(r : ℂ)
  let M : ℝ := r+(R/2)/r
  have hr : 1 < r := largeRootRadius_gt_one
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hr))
  have hz : ‖z‖ = r := by
    dsimp [z]
    simp [norm_mul, Complex.norm_real, abs_of_pos (lt_trans zero_lt_one hr)]
  have hinv : z⁻¹ = -(Complex.I/(r : ℂ)) := by
    dsimp [z]
    rw [mul_inv_rev, Complex.inv_I]
    ring
  have htail : H z-z-exteriorForwardCoeff H 1*z⁻¹ =
      H z-Complex.I*(M : ℂ) := by
    rw [hb, hinv]
    dsimp [M]
    push_cast
    field_simp [hr0]
    ring
  have hbudget := exterior_odd_tail_norm_sq_le H hc hodd hr hz
  rw [htail] at hbudget
  have hbN : ‖exteriorForwardCoeff H 1‖^2 = (R/2)^2 := by
    rw [hb, norm_div, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hR0]
    norm_num
  rw [hbN] at hbudget
  have hdef0 : 0 ≤ 1-(R/2)^2 := by
    nlinarith
  have hprod :
      (1-(R/2)^2)*exteriorStripLogKernel r < (1/180 : ℝ) := by
    calc
      _ ≤ (1-(R/2)^2)*1 :=
        mul_le_mul_of_nonneg_left (le_of_lt largeRootRadius_kernel_lt_one) hdef0
      _ < (1/180 : ℝ) := by simpa using hdef
  have hsq : ‖H z-Complex.I*(M : ℂ)‖^2 < (3/40 : ℝ)^2 := by
    nlinarith [hbudget, hprod]
  have hnorm := (sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3/40)).mp hsq
  simpa [z, M, r] using hnorm

end SpringerLean
