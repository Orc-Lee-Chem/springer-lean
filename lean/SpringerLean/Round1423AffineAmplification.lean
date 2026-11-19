import SpringerLean.Round1422JointScalarChecks

namespace SpringerLean
set_option maxHeartbeats 200000

/-- A rational upper bound for the exponential in the small interval
used by the affine change of angles. -/
theorem exp_le_small_linear {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1/200) :
    Real.exp x ≤ 1+(200/199:ℝ)*x := by
  have hpos : 0 < 1-x := by linarith
  have hbound := Real.add_one_le_exp (-x)
  have hproduct : Real.exp (-x)*Real.exp x = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hexp0 : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have hfirst : (1-x)*Real.exp x ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : 0 ≤ Real.exp (-x)-(1-x))) hexp0]
  have hrecip : Real.exp x ≤ 1/(1-x) :=
    (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hfirst)
  have hlast : 1/(1-x) ≤ 1+(200/199:ℝ)*x := by
    apply (div_le_iff₀ hpos).2
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr (by linarith : 0 ≤ 1-200*x))]
  exact hrecip.trans hlast

/-- Numerical coefficient behind the logarithmic amplification bound. -/
theorem refinedAffine_amplification_coefficient :
    (71/5000:ℝ)+(107/200)/(2*(1-107/50000))+
      (107/400)/500 < 111/200 := by
  norm_num

/-- Once the exact angular Jacobian has been integrated, this is the
remaining scalar amplification factor. -/
theorem refinedAffine_amplification_le
    (n : ℕ) {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hWsq : (n:ℝ)*W^2 ≤ 3/500) :
    (1+(71/5000:ℝ)*W) *
      (1+(107/200:ℝ)*W^2)^n *
      Real.sqrt ((1+(107/200:ℝ)*W^2)/(1-(107/100:ℝ)*W)) ≤
      1+(57/100:ℝ)*W+(55/100:ℝ)*(n:ℝ)*W^2 := by
  let u : ℝ := 1+(107/200:ℝ)*W^2
  let v : ℝ := 1-(107/100:ℝ)*W
  let p : ℝ := 1+(71/5000:ℝ)*W
  let M : ℝ := p*u^n*Real.sqrt (u/v)
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; nlinarith
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 < u/v := div_pos hu hv
  have hsqrt : 0 < Real.sqrt (u/v) := Real.sqrt_pos.2 hq
  have hM : 0 < M := by dsimp [M]; positivity
  have hlogp : Real.log p ≤ (71/5000:ℝ)*W := by
    have h := Real.log_le_sub_one_of_pos hp
    dsimp [p] at h
    linarith
  have hlogu : Real.log u ≤ (107/200:ℝ)*W^2 := by
    have h := Real.log_le_sub_one_of_pos hu
    dsimp [u] at h
    linarith
  have hlogv : -Real.log v ≤ ((107/100:ℝ)*W)/v := by
    have h := Real.one_sub_inv_le_log_of_pos hv
    have heq : 1-v⁻¹ = -(1-v)/v := by
      field_simp [ne_of_gt hv]
      ring
    have hdelta : (107/100:ℝ)*W=1-v := by dsimp [v]; ring
    rw [hdelta]
    rw [heq] at h
    have h' : -((1-v)/v) ≤ Real.log v := by
      simpa only [neg_div] using h
    linarith
  have hvmin : (1-107/50000:ℝ) ≤ v := by
    dsimp [v]
    nlinarith
  have hfrac : ((107/100:ℝ)*W)/v ≤
      ((107/100:ℝ)/(1-107/50000))*W := by
    apply (div_le_iff₀ hv).2
    dsimp [v]
    have hcoeff : ((107/100:ℝ)/(1-107/50000)) = 53500/49893 := by
      norm_num
    rw [hcoeff]
    nlinarith [mul_nonneg hW0 (sub_nonneg.mpr (by linarith :
      0 ≤ 1/500-W))]
  have hlogMformula : Real.log M =
      Real.log p+(n:ℝ)*Real.log u+(Real.log u-Real.log v)/2 := by
    dsimp [M]
    rw [Real.log_mul (by positivity : p*u^n ≠ 0) (ne_of_gt hsqrt),
      Real.log_mul (ne_of_gt hp) (by positivity : u^n ≠ 0),
      Real.log_pow, Real.log_sqrt hq.le,
      Real.log_div (ne_of_gt hu) (ne_of_gt hv)]
  have hWpow : W^2 ≤ W/500 := by
    nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hW)]
  have hlogM : Real.log M ≤
      (111/200:ℝ)*W+(67/125:ℝ)*(n:ℝ)*W^2 := by
    rw [hlogMformula]
    have hnu := mul_le_mul_of_nonneg_left hlogu
      (show 0 ≤ (n:ℝ) by exact_mod_cast (Nat.zero_le n))
    have hcoeff := refinedAffine_amplification_coefficient
    nlinarith [hfrac]
  let lam : ℝ := (111/200:ℝ)*W+(67/125:ℝ)*(n:ℝ)*W^2
  have hlam0 : 0 ≤ lam := by dsimp [lam]; positivity
  have hlam : lam ≤ 1/200 := by
    dsimp [lam]
    nlinarith [hWsq]
  have hMexp : M ≤ Real.exp lam := (Real.log_le_iff_le_exp hM).mp hlogM
  have hExp := exp_le_small_linear hlam0 hlam
  have hfinal : 1+(200/199:ℝ)*lam ≤
      1+(57/100:ℝ)*W+(55/100:ℝ)*(n:ℝ)*W^2 := by
    dsimp [lam]
    have hnWsq : 0 ≤ (n:ℝ)*W^2 := by positivity
    nlinarith
  change M ≤ _
  exact hMexp.trans (hExp.trans hfinal)

end SpringerLean

#print axioms SpringerLean.exp_le_small_linear
#print axioms SpringerLean.refinedAffine_amplification_le
