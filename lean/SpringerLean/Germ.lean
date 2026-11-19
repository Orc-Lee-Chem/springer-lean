import SpringerLean.ActualExpansion
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.IteratedFDeriv

namespace SpringerLean

/-- The actual inverse, read in the local coordinate t = 1/w at infinity. -/
noncomputable def slitInverseGerm (a t : ℂ) : ℂ :=
  if t = 0 then 0 else t⁻¹ - slitInverse a t⁻¹

private theorem norm_inv_gt_four {t : ℂ} (ht : ‖t‖ < 1 / 4) (ht0 : t ≠ 0) :
    4 < ‖t⁻¹‖ := by
  rw [norm_inv]
  have hp : (0 : ℝ) < ‖t‖ := norm_pos_iff.mpr ht0
  have h := one_div_lt_one_div_of_lt hp ht
  norm_num at h ⊢
  exact h

theorem slitInverseGerm_eq_series (a t : ℂ) (ha : ‖a‖ = 1)
    (ht : ‖t‖ < 1 / 4) :
    slitInverseGerm a t = t * slitQ a (t ^ 2) := by
  by_cases ht0 : t = 0
  · simp [slitInverseGerm, ht0]
  · have hw : 4 < ‖t⁻¹‖ := norm_inv_gt_four ht ht0
    have h := (slitInverse_eq_Q_and_mem a t⁻¹ ha hw).1
    simpa [slitInverseGerm, ht0] using
      (show t⁻¹ - slitInverse a t⁻¹ = t * slitQ a (t ^ 2) by
        rw [h, inv_inv]
        ring)

theorem slitInverseGerm_hasSum_odd (a t : ℂ) (ha : ‖a‖ = 1)
    (ht : ‖t‖ < 1 / 4) :
    HasSum (fun k : ℕ => slitOddCoeff a k * t ^ (2 * k + 1))
      (slitInverseGerm a t) := by
  have hu : ‖t ^ 2‖ < 1 / 4 := by
    rw [norm_pow]
    have hp : 0 < ((1 / 4 : ℝ) - ‖t‖) * ((1 / 4 : ℝ) + ‖t‖) := by
      apply mul_pos <;> nlinarith [norm_nonneg t]
    nlinarith [norm_nonneg t]
  have hs := (slitQ_hasSum a (t ^ 2) ha hu).mul_left t
  rw [slitInverseGerm_eq_series a t ha ht]
  apply HasSum.congr_fun hs
  intro k
  rw [pow_add, pow_mul]
  ring

end SpringerLean