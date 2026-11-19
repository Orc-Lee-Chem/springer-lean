import SpringerLean.Round1949OddStarBaseSet

namespace SpringerLean

/-- The same star written as radial segments in each m-th root-of-unity
direction. The radius condition is `r^m ≤ 4`, avoiding an auxiliary
choice of a positive real m-th root. -/
def regularStarRaySet (m : ℕ) : Set ℂ :=
  {w : ℂ | ∃ r : ℝ, 0 ≤ r ∧ r ^ m ≤ 4 ∧
    ∃ η : ℂ, η ^ m = 1 ∧ w = (r : ℂ) * η}

/-- The power-preimage definition used by the actual exterior map is
exactly the union of the radial segments in the root-of-unity directions. -/
theorem regularStarPowerSet_eq_raySet
    (m : ℕ) (hm : 0 < m) :
    regularStarPowerSet m = regularStarRaySet m := by
  ext w
  constructor
  · intro hw
    change (w ^ m).im = 0 ∧ 0 ≤ (w ^ m).re ∧ (w ^ m).re ≤ 4 at hw
    rcases hw with ⟨him, hnonneg, hle⟩
    let r : ℝ := ‖w‖
    have hr : 0 ≤ r := norm_nonneg w
    have hpowreal : w ^ m = (((w ^ m).re : ℝ) : ℂ) := by
      apply Complex.ext
      · change (w ^ m).re = (w ^ m).re
        rfl
      · simpa using him
    have hrpow : r ^ m = (w ^ m).re := by
      calc
        r ^ m = ‖w ^ m‖ := by simp [r, norm_pow]
        _ = ‖(((w ^ m).re : ℝ) : ℂ)‖ := congrArg norm hpowreal
        _ = (w ^ m).re := by
          simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have hrle : r ^ m ≤ 4 := hrpow ▸ hle
    by_cases hw0 : w = 0
    · refine ⟨r, hr, hrle, 1, one_pow m, ?_⟩
      subst w
      simp [r]
    · have hr0 : r ≠ 0 := norm_ne_zero_iff.mpr hw0
      let η : ℂ := w / (r : ℂ)
      have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
      have hηpow : η ^ m = 1 := by
        dsimp [η]
        rw [div_pow, ← Complex.ofReal_pow]
        have hpoweq : w ^ m = ((r ^ m : ℝ) : ℂ) := by
          rw [hpowreal, hrpow]
        have hrpowc : ((r ^ m : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast pow_ne_zero m hr0
        rw [hpoweq, div_self hrpowc]
      refine ⟨r, hr, hrle, η, hηpow, ?_⟩
      dsimp [η]
      exact (mul_div_cancel₀ w hrc).symm
  · rintro ⟨r, hr, hrle, η, hηpow, rfl⟩
    change (((r : ℂ) * η) ^ m).im = 0 ∧
      0 ≤ (((r : ℂ) * η) ^ m).re ∧
      (((r : ℂ) * η) ^ m).re ≤ 4
    rw [mul_pow, hηpow, mul_one, ← Complex.ofReal_pow]
    simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
    exact ⟨pow_nonneg hr _, hrle⟩

/-- The actual t=0 omitted set has exactly the radial-arm description
of the regular star. -/
theorem oddStarPerturbation_zero_omitted_eq_regularStarRays
    (m : ℕ) (hm : 2 ≤ m) :
    oddStarPerturbationOmitted m 0 = regularStarRaySet m := by
  rw [oddStarPerturbation_zero_omitted_eq_regularStar m hm,
    regularStarPowerSet_eq_raySet m (by omega)]

end SpringerLean

#print axioms SpringerLean.regularStarPowerSet_eq_raySet
#print axioms SpringerLean.oddStarPerturbation_zero_omitted_eq_regularStarRays
