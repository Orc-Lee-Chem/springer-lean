import SpringerLean.Round2003OddStarVariationIntegral

open MeasureTheory

namespace SpringerLean

/-- The scalar integrand proved positive in R2003 is exactly the
parameter derivative of the original opposite-tip log distance. -/
theorem oddStarOppositeTipLogDistance_hasDerivAt_pointwiseVariation
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    HasDerivAt (oddStarOppositeTipLogDistance m θ)
      (oddStarPointwiseVariation m θ) 0 := by
  simpa only [oddStarPointwiseVariation] using
    oddStarOppositeTipLogDistance_hasDerivAt_formula m hm θ

/-- The angular integral of the actual pointwise derivative is
strictly positive for every m>=3. -/
theorem oddStarOppositeTipLogDistance_integral_deriv_pos
    (m : ℕ) (hm : 3 ≤ m) :
    0 < (∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (oddStarOppositeTipLogDistance m θ) 0) := by
  have hpoint (θ : ℝ) :
      deriv (oddStarOppositeTipLogDistance m θ) 0 =
        oddStarPointwiseVariation m θ :=
    (oddStarOppositeTipLogDistance_hasDerivAt_pointwiseVariation m hm θ).deriv
  simp_rw [hpoint]
  exact oddStarPointwiseVariation_integral_pos m hm

/-- At the regular star the actual opposite-tip separation is at
least the tip radius, uniformly in the boundary angle. -/
theorem oddStarOppositeTip_distance_ge_tipRadius
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    oddStarTipRadius m 0 ≤
      ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ 0 -
        (oddStarTipRadius m 0 : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖ := by
  have hrbase : 0 ≤ 2 + 2 * Real.cos θ := by
    nlinarith [Real.neg_one_le_cos θ]
  have hr : 0 ≤ oddStarBoundaryRadius m θ := by
    unfold oddStarBoundaryRadius
    exact Real.rpow_nonneg hrbase _
  have hR : 0 < oddStarTipRadius m 0 := oddStarTipRadius_zero_pos m
  have hgeom :=
    (oddStar_opposite_tip_angle_geometry m hm
      (oddStarBoundaryRadius m θ) (oddStarTipRadius m 0) hr hR.le).2.2
  have hZ : oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ 0 =
      (oddStarBoundaryRadius m θ : ℂ) := by
    simp [oddStarMovingBoundaryPoint, oddStarBoundaryFactor]
  rw [hZ]
  have hsq := oddStarOppositeTip_norm_sq_formula
    (oddStarBoundaryRadius m θ) (oddStarTipRadius m 0)
    (Real.pi - Real.pi / (m : ℝ))
  have hnorm : 0 ≤ ‖(oddStarBoundaryRadius m θ : ℂ) -
      (oddStarTipRadius m 0 : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖ :=
    norm_nonneg _
  nlinarith

end SpringerLean

#print axioms SpringerLean.oddStarOppositeTipLogDistance_integral_deriv_pos
#print axioms SpringerLean.oddStarOppositeTip_distance_ge_tipRadius
