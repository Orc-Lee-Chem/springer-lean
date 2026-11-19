import SpringerLean.Round1421AffineJacobianScalar

namespace SpringerLean

/-- The squared strip width of the actual root construction inherits
the same small parameter window as its logarithmic upper bound. -/
theorem mediumWidth_actual_window
    {n : ℕ} (hn : 1501 ≤ n) {d : ℝ}
    (hd0 : 0 < d) (hnd : (n:ℝ)*d < 1) :
    let W : ℝ := (exteriorRealRootWidth (2-d)
      (1+Real.sqrt d/10))^2
    0 ≤ W ∧ W < 1/500 ∧ (n:ℝ)*W^2 < 3/500 := by
  dsimp
  let U : ℝ := (17/50)*d*Real.log (2/d)
  let W : ℝ := (exteriorRealRootWidth (2-d)
    (1+Real.sqrt d/10))^2
  have hnlarge : (1501:ℝ)≤n := by exact_mod_cast hn
  have hd : d ≤ (1/1501:ℝ) := by
    have h := mul_nonneg (sub_nonneg.mpr hnlarge) hd0.le
    nlinarith
  have hU := localized_affine_width_window hn hd0 hnd
  change 0 < U ∧ U < 1/500 ∧ (n:ℝ)*U^2 < 3/500 at hU
  have hW : W < U := by
    simpa [W,U, show (34/100:ℝ)=17/50 by norm_num] using
      (mediumWidth_exact_width_sq_lt hd0 hd)
  have hW0 : 0 ≤ W := sq_nonneg _
  have hsq : W^2 ≤ U^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hW.le)
      (add_nonneg hW0 hU.1.le)]
  have hn0 : (0:ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
  have hmul := mul_le_mul_of_nonneg_left hsq hn0
  exact ⟨hW0,hW.trans hU.2.1, by linarith [hU.2.2]⟩

/-- The sharper short-arc variance coefficient is compatible with the
elementary bounds on `S(θ)=2-2*cos θ`. -/
theorem movingArc_variance_rational_margin :
    (999/1000:ℝ)^2/5-1/9 ≥ (995/1000:ℝ)*4/45 := by
  norm_num

/-- The raw cubic difference is small enough for the exponential
tangent at `s₀=2b²/5`. -/
theorem movingArc_third_moment_rational_margin :
    (1/7:ℝ)-(999/1000:ℝ)^3/27 <
      (6/5:ℝ)*(995/1000)*4/45 := by
  norm_num

/-- The joint endpoint budget has a strictly positive reserve at the
initial order `n=1501`. -/
theorem jointEndpoint_budget_margin :
    (1/100:ℝ)-13/1501 > 0 := by
  norm_num

/-- The cubic used to separate the two positive endpoint deficits is
bounded below uniformly for `z≥0`. -/
theorem jointEndpoint_cubic_lower {z : ℝ} (hz : 0 ≤ z) :
    -(9/160:ℝ) ≤ (5/2)*z^3-(11/40)*z^2-(57/200)*z := by
  have hidentity :
      (5/2:ℝ)*z^3-(11/40)*z^2-(57/200)*z+9/160 =
      (z-1/4)^2*((5/2)*z+9/10)+(3/40)*z^2+(7/800)*z := by
    ring
  have hnonneg :
      0 ≤ (z-1/4)^2*((5/2)*z+9/10)+(3/40)*z^2+(7/800)*z := by
    positivity
  linarith

/-- The conditional joint bound `J₁+J₂≤0.52` and the cubic lower
bound would give a strict `0.58` one-end exclusion threshold. -/
theorem jointEndpoint_one_side_budget :
    (52/100:ℝ)+9/160 < 58/100 := by
  norm_num

end SpringerLean

#print axioms SpringerLean.movingArc_variance_rational_margin
#print axioms SpringerLean.movingArc_third_moment_rational_margin
#print axioms SpringerLean.jointEndpoint_cubic_lower
#print axioms SpringerLean.mediumWidth_actual_window
