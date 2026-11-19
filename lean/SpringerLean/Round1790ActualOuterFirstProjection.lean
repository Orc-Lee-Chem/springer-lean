import SpringerLean.Round1785ActualAlignedNearPhaseCost

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 700000

/-- The first fine strip bounds the transverse square on the ENTIRE
ordinary hull, including the assigned negative half. -/
theorem exteriorOmitted_actualEndpoint_transverse_sq_small
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (w : ℂ) (hw : w ∈ convexHull ℝ (exteriorOmitted F)) :
    (conj (P/(‖P‖ : ℂ))*w).im^2 < 1/100 := by
  let W := exteriorFineEndpointWidth P
  let ξ := P/(‖P‖ : ℂ)
  have hW0 : 0 ≤ W := by dsimp [W, exteriorFineEndpointWidth]; positivity
  have hm : (1500 : ℝ) ≤ ((2*k-2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hR : 0 < ‖P‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd.le]
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne']
  have hWsmall : W < 1/3000 := by
    have hh := mul_le_mul_of_nonneg_right hm hW0
    change ((2*k-2 : ℕ) : ℝ)*W < 1/2 at hW
    nlinarith
  have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have hpabs : |(conj ξ*w).re| ≤ 2 := by
    calc
      _ ≤ ‖conj ξ*w‖ := Complex.abs_re_le_norm _
      _ = ‖w‖ := by rw [norm_mul, Complex.norm_conj, hξ, one_mul]
      _ ≤ 2 := hw2
  have hp := (abs_le.mp hpabs).1
  have hR2 := exteriorOmitted_norm_le_two F hc hP
  have hs := (exteriorOmitted_actualEndpoint_fine_strip F hc k hk P hP hd ht w hw).2.1
  have hlinear : ‖P‖-(conj ξ*w).re ≤ 4 := by linarith
  have hh := mul_le_mul_of_nonneg_left hlinear (show 0 ≤ 4*W by positivity)
  have hWsq : W^2 ≤ W/3000 := by
    nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hWsmall.le)]
  change (conj ξ*w).im^2 < 1/100
  change (conj ξ*w).im^2 ≤ 4*W*(W+‖P‖-(conj ξ*w).re) at hs
  nlinarith

/-- High-radius points in the original forward assigned half project
above 9/5 even after the small phase-ray perturbation. -/
theorem exteriorOmitted_actualEndpoint_forward_outer_projection
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (w : ℂ) (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hr : (46/25 : ℝ) ≤ ‖w‖)
    (hforward : 0 ≤ (conj (P/(‖P‖ : ℂ))*w).re)
    (v : ℂ) (hv : ‖v-P/(‖P‖ : ℂ)‖ ≤ 1/200) :
    (9/5 : ℝ) < (conj v*w).re := by
  let ξ := P/(‖P‖ : ℂ)
  have hq := exteriorOmitted_actualEndpoint_transverse_sq_small F hc k hk P hP hd ht hW w hw
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hR : 0 < ‖P‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd.le]
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne']
  have hnorm : ‖conj ξ*w‖=‖w‖ := by rw [norm_mul, Complex.norm_conj, hξ, one_mul]
  have hnorm2 : ‖w‖^2=(conj ξ*w).re^2+(conj ξ*w).im^2 := by
    rw [←hnorm, Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two]
  have hr2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 46/25) hr 2
  have hp : (181/100 : ℝ) < (conj ξ*w).re := by
    by_contra hh
    have hh' := le_of_not_gt hh
    have hsq := mul_nonneg hforward (sub_nonneg.mpr hh')
    nlinarith
  have hpert := unit_projection_perturbation_le ξ v w
  have hcost : ‖ξ-v‖*‖w‖ ≤ 1/100 := by
    rw [norm_sub_rev]
    have hh := mul_le_mul hv (exteriorOmitted_convexHull_norm_le_two F hc hw)
      (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1/200)
    nlinarith
  linarith

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_actualEndpoint_forward_outer_projection
