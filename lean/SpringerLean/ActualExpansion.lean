import SpringerLean.Series

namespace SpringerLean

private theorem inv_norm_lt_quarter {w : ℂ} (hw : 4 < ‖w‖) : ‖w⁻¹‖ < 1 / 4 := by
  rw [norm_inv]
  have h := one_div_lt_one_div_of_lt (show (0 : ℝ) < 4 by norm_num) hw
  simpa only [one_div] using h

/-- The convergent Catalan series constructs the actual exterior inverse for `‖w‖>4`. -/
theorem slitInverse_eq_Q_and_mem (a w : ℂ) (ha : ‖a‖ = 1) (hw : 4 < ‖w‖) :
    slitInverse a w = w - w⁻¹ * slitQ a ((w⁻¹) ^ 2) ∧
      w ∈ slitMap a '' exteriorDisk := by
  let t : ℂ := w⁻¹
  let q : ℂ := slitQ a (t ^ 2)
  let g : ℂ := w - t * q
  have ht : ‖t‖ < 1 / 4 := inv_norm_lt_quarter hw
  have hu : ‖t ^ 2‖ < 1 / 4 := by
    rw [norm_pow]
    have hp : 0 < ((1 / 4 : ℝ) - ‖t‖) * ((1 / 4 : ℝ) + ‖t‖) := by
      apply mul_pos <;> nlinarith [norm_nonneg t]
    nlinarith [norm_nonneg t]
  have hq : q = a + t ^ 2 * q ^ 2 := slitQ_quadratic a (t ^ 2) ha hu
  have hqb : ‖q‖ ≤ (4 : ℝ) / 3 := slitQ_norm_le_four_thirds a t ha ht
  have hdiff : ‖g - w‖ < 1 / 3 := by
    have heq : g - w = -(t * q) := by dsimp [g]; ring
    rw [heq, norm_neg, norm_mul]
    have hmul := mul_le_mul_of_nonneg_left hqb (norm_nonneg t)
    nlinarith [hmul]
  have htri : ‖w‖ ≤ ‖g‖ + ‖g - w‖ := by
    calc
      ‖w‖ = ‖g + (w - g)‖ := by congr 1; ring
      _ ≤ ‖g‖ + ‖w - g‖ := norm_add_le _ _
      _ = ‖g‖ + ‖g - w‖ := congrArg (fun x : ℝ => ‖g‖ + x) (norm_sub_rev w g)
  have hg : g ∈ exteriorDisk := by
    change 1 < ‖g‖
    nlinarith
  have hw0 : w ≠ 0 := by
    intro h
    norm_num [h] at hw
  have hwt : w * t = 1 := by
    dsimp [t]
    exact mul_inv_cancel₀ hw0
  have hqzero : a + t ^ 2 * q ^ 2 - q = 0 := by rw [← hq]; ring
  have hquad : g * g - w * g + a = 0 := by
    calc
      g * g - w * g + a = (a + t ^ 2 * q ^ 2 - q) + (1 - w * t) * q := by
        dsimp [g]
        ring
      _ = 0 := by rw [hqzero, hwt]; ring
  have hslit : slitMap a g = w :=
    (slitMap_eq_iff_quadratic a g w (exterior_ne_zero hg)).mpr hquad
  have hmem : w ∈ slitMap a '' exteriorDisk := ⟨g, hg, hslit⟩
  have hinv : slitInverse a w = g := by
    rw [← hslit]
    exact slitInverse_apply a g ha hg
  exact ⟨hinv, hmem⟩


/-- The first two displayed coefficients are `a/w` and `a²/w³`. -/
theorem slitOddCoeff_one (a : ℂ) : slitOddCoeff a 1 = a ^ 2 := by
  simp [slitOddCoeff, catalan_one]

/-- Full convergent Catalan expansion of the existing actual inverse on `‖w‖>4`. -/
theorem slitInverse_hasSum (a w : ℂ) (ha : ‖a‖ = 1) (hw : 4 < ‖w‖) :
    HasSum (fun k : ℕ => slitOddCoeff a k * (w⁻¹) ^ (2 * k + 1))
      (w - slitInverse a w) := by
  have ht : ‖w⁻¹‖ < 1 / 4 := inv_norm_lt_quarter hw
  have hu : ‖(w⁻¹) ^ 2‖ < 1 / 4 := by
    rw [norm_pow]
    have hp : 0 < ((1 / 4 : ℝ) - ‖w⁻¹‖) * ((1 / 4 : ℝ) + ‖w⁻¹‖) := by
      apply mul_pos <;> nlinarith [norm_nonneg (w⁻¹)]
    nlinarith [norm_nonneg (w⁻¹)]
  have hsum := (slitQ_hasSum a ((w⁻¹) ^ 2) ha hu).mul_left w⁻¹
  have hinv := (slitInverse_eq_Q_and_mem a w ha hw).1
  have htarget : w - slitInverse a w = w⁻¹ * slitQ a ((w⁻¹) ^ 2) := by
    rw [hinv]
    ring
  rw [htarget]
  apply HasSum.congr_fun hsum
  intro k
  rw [pow_add, pow_mul]
  ring
end SpringerLean