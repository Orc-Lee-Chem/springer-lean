import SpringerLean.Round1831ActualTinyFirstEndpoint

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 900000

/-- The whole ordinary hull lies in a strip whose thickness vanishes
with the first endpoint deficit, not merely in a fixed small strip. -/
theorem exteriorOmitted_actualEndpoint_transverse_le_deficit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hlog : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)) < 3/2)
    (hwidth : exteriorFineEndpointWidth P <
      (1/3 : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)))
    (w : ℂ) (hw : w ∈ convexHull ℝ (exteriorOmitted F)) :
    |(conj (P/(‖P‖ : ℂ))*w).im| ≤ (5/2 : ℝ)*Real.sqrt ((2-‖P‖)*Real.log (2/(2-‖P‖))) := by
  let E := (2-‖P‖)*Real.log (2/(2-‖P‖))
  let W := exteriorFineEndpointWidth P
  let ξ := P/(‖P‖ : ℂ)
  have hL := (endpointPhaseParameter_scalar_relations k hk P hd ht).1
  have hE : 0 < E := by dsimp [E]; positivity
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hEsmall : E < 1/1000 := by
    have hh := mul_le_mul_of_nonneg_right hn hE.le
    rw [mul_assoc] at hlog
    change ((2*k-1 : ℕ) : ℝ)*E < 3/2 at hlog
    nlinarith
  have hW0 : 0 ≤ W := by dsimp [W,exteriorFineEndpointWidth]; positivity
  have hW : W < E/3 := by change exteriorFineEndpointWidth P < E/3; nlinarith [hwidth]
  have hR : 0 < ‖P‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd.le]
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR,div_self hR.ne']
  have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have hpabs : |(conj ξ*w).re| ≤ 2 := by
    calc
      _ ≤ ‖conj ξ*w‖ := Complex.abs_re_le_norm _
      _ = ‖w‖ := by rw [norm_mul,Complex.norm_conj,hξ,one_mul]
      _ ≤ 2 := hw2
  have hp := (abs_le.mp hpabs).1
  have hR2 := exteriorOmitted_norm_le_two F hc hP
  have hs := (exteriorOmitted_actualEndpoint_fine_strip F hc k hk P hP hd ht w hw).2.1
  change (conj ξ*w).im^2 ≤ 4*W*(W+‖P‖-(conj ξ*w).re) at hs
  have hlinear : ‖P‖-(conj ξ*w).re ≤ 4 := by linarith
  have hquad : W^2 ≤ W/3000 := by
    nlinarith [mul_nonneg hW0 (show 0 ≤ 1/3000-W by linarith)]
  have hsquare : (conj ξ*w).im^2 ≤ (25/4 : ℝ)*E := by
    have hh := mul_le_mul_of_nonneg_left hlinear (show 0 ≤ 4*W by positivity)
    nlinarith
  have hroot := Real.sq_sqrt hE.le
  change |(conj ξ*w).im| ≤ (5/2 : ℝ)*Real.sqrt E
  nlinarith [sq_abs (conj ξ*w).im,abs_nonneg (conj ξ*w).im,Real.sqrt_nonneg E]

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_actualEndpoint_transverse_le_deficit
