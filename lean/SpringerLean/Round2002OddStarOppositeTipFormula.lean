import SpringerLean.Round2001OddStarOppositeTipLogDerivative

namespace SpringerLean
open scoped RealInnerProductSpace

/-- Exact radial and angular expansion of the first-variation
real inner product. -/
theorem oddStarOppositeTip_inner_formula
    (r R q θ δ : ℝ) :
    ⟪(r : ℂ) - (R : ℂ) * Complex.exp ((δ : ℂ) * Complex.I),
      (q : ℂ) * ((Real.sin θ : ℂ) + (Real.cos θ - 1 : ℝ) * Complex.I)⟫ =
      q * ((r - R * Real.cos δ) * Real.sin θ +
        R * Real.sin δ * (1 - Real.cos θ)) := by
  rw [Complex.inner, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re]
  ring

/-- Squared opposite-tip distance in the radial coordinates. -/
theorem oddStarOppositeTip_norm_sq_formula
    (r R δ : ℝ) :
    ‖(r : ℂ) - (R : ℂ) * Complex.exp ((δ : ℂ) * Complex.I)‖ ^ 2 =
      r ^ 2 + R ^ 2 - 2 * r * R * Real.cos δ := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq δ]

/-- The pointwise first variation in the paper's explicit scalar
form, before angular integration. -/
theorem oddStarOppositeTipLogDistance_hasDerivAt_formula
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    HasDerivAt (oddStarOppositeTipLogDistance m θ)
      ((oddStarBoundaryRadius m θ / (m : ℝ)) *
        ((oddStarBoundaryRadius m θ - oddStarTipRadius m 0 *
            Real.cos (Real.pi - Real.pi / (m : ℝ))) * Real.sin θ +
          oddStarTipRadius m 0 *
            Real.sin (Real.pi - Real.pi / (m : ℝ)) * (1 - Real.cos θ)) /
        ((oddStarBoundaryRadius m θ) ^ 2 + (oddStarTipRadius m 0) ^ 2 -
          2 * oddStarBoundaryRadius m θ * oddStarTipRadius m 0 *
            Real.cos (Real.pi - Real.pi / (m : ℝ)))) 0 := by
  let r := oddStarBoundaryRadius m θ
  let R := oddStarTipRadius m 0
  let δ := Real.pi - Real.pi / (m : ℝ)
  have hZ : oddStarMovingBoundaryPoint m r θ 0 = (r : ℂ) := by
    simp [oddStarMovingBoundaryPoint, oddStarBoundaryFactor]
  have hcoef : (r : ℂ) * (m : ℂ)⁻¹ = ((r / (m : ℝ)) : ℂ) := by
    push_cast
    ring
  convert oddStarOppositeTipLogDistance_hasDerivAt_zero m hm θ using 1
  rw [hZ, hcoef, ← Complex.ofReal_div,
    oddStarOppositeTip_inner_formula,
    oddStarOppositeTip_norm_sq_formula]

/-- The scalar denominator stays strictly positive for every angle. -/
theorem oddStarOppositeTip_denominator_pos
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    0 < (oddStarBoundaryRadius m θ) ^ 2 +
      (oddStarTipRadius m 0) ^ 2 -
        2 * oddStarBoundaryRadius m θ * oddStarTipRadius m 0 *
          Real.cos (Real.pi - Real.pi / (m : ℝ)) := by
  have hrbase : 0 ≤ 2 + 2 * Real.cos θ := by
    nlinarith [Real.neg_one_le_cos θ]
  have hr : 0 ≤ oddStarBoundaryRadius m θ := by
    unfold oddStarBoundaryRadius
    exact Real.rpow_nonneg hrbase _
  have hR : 0 < oddStarTipRadius m 0 := oddStarTipRadius_zero_pos m
  have hbound :=
    (oddStar_opposite_tip_angle_geometry m hm
      (oddStarBoundaryRadius m θ) (oddStarTipRadius m 0) hr hR.le).2.2
  nlinarith [sq_pos_of_pos hR]

end SpringerLean

#print axioms SpringerLean.oddStarOppositeTipLogDistance_hasDerivAt_formula
#print axioms SpringerLean.oddStarOppositeTip_denominator_pos
