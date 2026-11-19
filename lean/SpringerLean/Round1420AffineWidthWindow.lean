import SpringerLean.Round1419AffineActiveArc
import SpringerLean.Round1408WidthSmallness

namespace SpringerLean
set_option maxHeartbeats 200000

/-- A logarithmic window bound that avoids monotonicity in the order.
The variable `u = 1501*d` lies in `(0,1]`. -/
theorem localized_log_sqrt_window
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ 1/1501) :
    Real.sqrt (1501*d) * Real.log (2/d) < (25/3 : ℝ) := by
  let u : ℝ := 1501*d
  let r : ℝ := Real.sqrt u
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; nlinarith
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    have hrsq : r^2 = u := Real.sq_sqrt hu0.le
    nlinarith
  have hrsq : r^2 = u := Real.sq_sqrt hu0.le
  have hlogratio : Real.log (2/d) = Real.log 3002 - Real.log u := by
    have hratio : (2:ℝ)/d = 3002/u := by
      dsimp [u]
      field_simp [ne_of_gt hd0]
      ring
    rw [hratio, Real.log_div (by norm_num) (ne_of_gt hu0)]
  have hlogpow : Real.log u = 2*Real.log r := by
    rw [← hrsq, Real.log_pow]
    ring
  have hlogInv : -Real.log r ≤ 1/r - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1/r by positivity)
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt hr0)] at h
    norm_num at h
    simpa using h
  have hscaled : -2*r*Real.log r ≤ 2-2*r := by
    have hh := mul_le_mul_of_nonneg_left hlogInv (show 0 ≤ 2*r by positivity)
    have hrne : r ≠ 0 := ne_of_gt hr0
    field_simp [hrne] at hh
    nlinarith
  have hlogHi : Real.log (3002:ℝ) < 25/3 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<3002)
      (by norm_num : (3002:ℝ)≤4096)
    rw [show (4096:ℝ)=2^12 by norm_num, Real.log_pow] at h
    have htwo : Real.log (2:ℝ) < 25/36 := by
      have hh := Real.log_two_lt_d9
      norm_num at hh ⊢
      linarith
    norm_num at h
    linarith
  have hlogLo : (2:ℝ) ≤ Real.log 3002 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<16)
      (by norm_num : (16:ℝ)≤3002)
    rw [show (16:ℝ)=2^4 by norm_num, Real.log_pow] at h
    have htwo : (1/2:ℝ) < Real.log 2 := by
      have hh := Real.log_two_gt_d9
      norm_num at hh ⊢
      linarith
    norm_num at h
    linarith
  change r*Real.log (2/d) < 25/3
  rw [hlogratio, hlogpow]
  nlinarith [mul_nonneg (sub_nonneg.mpr hr1)
    (sub_nonneg.mpr hlogLo)]

/-- The width parameter `0.34*d*log(2/d)` is uniformly tiny once
`n*d<1`, even though `n` is unbounded. -/
theorem localized_affine_width_window
    {n : ℕ} (hn : 1501 ≤ n) {d : ℝ}
    (hd0 : 0 < d) (hnd : (n:ℝ)*d < 1) :
    let W : ℝ := (17/50)*d*Real.log (2/d)
    0 < W ∧ W < 1/500 ∧ (n:ℝ)*W^2 < 3/500 := by
  dsimp
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hnlarge : (1501:ℝ)≤n := by exact_mod_cast hn
  have hd : d ≤ (1/1501:ℝ) := by
    have h := mul_nonneg (sub_nonneg.mpr hnlarge) hd0.le
    have hsmall : 1501*d < 1 := by nlinarith
    nlinarith
  have hL : 0 < Real.log (2/d) := by
    apply Real.log_pos
    have hsmall : d < 1 := lt_of_le_of_lt hd (by norm_num)
    apply (one_lt_div hd0).2
    linarith
  have hroot := localized_log_sqrt_window hd0 hd
  let r : ℝ := Real.sqrt (1501*d)
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    have hs : r^2=1501*d := Real.sq_sqrt (by positivity)
    nlinarith [show 1501*d≤1 by nlinarith]
  have hrsq : r^2=1501*d := Real.sq_sqrt (by positivity)
  have hroot' : r*Real.log (2/d) < 25/3 := hroot
  have hrootNonneg : 0 ≤ r*Real.log (2/d) := by positivity
  have hsq : (r*Real.log (2/d))^2 < (25/3:ℝ)^2 := by nlinarith
  have hnd0 : 0 < (17/50:ℝ)*d*Real.log (2/d) := by positivity
  have hW : (17/50:ℝ)*d*Real.log (2/d) < 1/500 := by
    have hprod : 1501*d*Real.log (2/d) < 25/3 := by
      have hh := mul_nonneg (sub_nonneg.mpr hr1) hL.le
      nlinarith
    nlinarith
  have hWsq : (n:ℝ)*((17/50)*d*Real.log (2/d))^2 < 3/500 := by
    have hndle : (n:ℝ)*d ≤ 1 := hnd.le
    have hfactor : (n:ℝ)*d*((17/50:ℝ)^2/1501*(r*Real.log (2/d))^2) ≤
        (17/50:ℝ)^2/1501*(r*Real.log (2/d))^2 := by
      apply mul_le_of_le_one_left (by positivity) hndle
    have heq : (n:ℝ)*((17/50)*d*Real.log (2/d))^2 =
        (n:ℝ)*d*((17/50:ℝ)^2/1501*(r*Real.log (2/d))^2) := by
      have hdR : d = r^2/1501 := by nlinarith [hrsq]
      rw [hdR]
      ring
    rw [heq]
    nlinarith [hsq]
  exact ⟨hnd0,hW,hWsq⟩

end SpringerLean

#print axioms SpringerLean.localized_log_sqrt_window
#print axioms SpringerLean.localized_affine_width_window
