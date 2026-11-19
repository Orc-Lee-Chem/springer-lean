import SpringerLean.Round1777AlignedAngularScalar

namespace SpringerLean
set_option maxHeartbeats 700000

theorem sin_sq_gt_thirtieth_on_middle {α : ℝ}
    (hαlo : Real.pi/3-6/7 ≤ α) (hαhi : α ≤ Real.pi-(Real.pi/3-6/7)) :
    (1/30 : ℝ) < (Real.sin α)^2 := by
  let b : ℝ := Real.pi/3-6/7
  change b ≤ α at hαlo
  change α ≤ Real.pi-b at hαhi
  have hb0 : 0 < b := by dsimp [b]; linarith [Real.pi_gt_d2]
  have hblo : (199/1050 : ℝ) ≤ b := by dsimp [b]; linarith [Real.pi_gt_d2]
  have hbhi : b ≤ 1/5 := by dsimp [b]; linarith [Real.pi_lt_d2]
  have hb3 := pow_le_pow_left₀ hb0.le hbhi 3
  have hbsin : (3/16 : ℝ) < Real.sin b := by
    have hh := Real.sin_ge_sub_cube hb0.le
    nlinarith
  have hd : 0 < Real.pi-2*b := by linarith [Real.pi_gt_three]
  let t := (α-b)/(Real.pi-2*b)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hαlo) hd.le
  have ht1 : t ≤ 1 := by
    apply (div_le_one hd).mpr
    change α-b ≤ Real.pi-2*b
    linarith
  have hcombo : (1-t)*b+t*(Real.pi-b)=α := by
    have hh : t*(Real.pi-2*b)=α-b := by
      dsimp [t]
      exact div_mul_cancel₀ _ hd.ne'
    nlinarith
  have hbmem : b ∈ Set.Icc 0 Real.pi := ⟨hb0.le, by linarith [Real.pi_gt_three]⟩
  have hbmem' : Real.pi-b ∈ Set.Icc 0 Real.pi := ⟨by linarith [Real.pi_gt_three], by linarith⟩
  have hconc := strictConcaveOn_sin_Icc.concaveOn.2 hbmem hbmem'
    (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
  simp only [smul_eq_mul, Real.sin_pi_sub] at hconc
  rw [hcombo] at hconc
  have hs : (3/16 : ℝ) < Real.sin α := by nlinarith
  nlinarith [sq_nonneg (Real.sin α-3/16)]

/-- A single sine-square floor covers the whole short-s interval of
the nonaligned true-axis branch. -/
theorem trueAxis_phase_sine_sq_floor {γ θ : ℝ}
    (hγlo : Real.pi/3 ≤ |γ|) (hγhi : |γ| ≤ Real.pi/2)
    (hθ : |θ| ≤ 6/7) : (1/30 : ℝ) < (Real.sin (γ-θ))^2 := by
  have hlo : Real.pi/3-6/7 ≤ |γ-θ| := by
    have htriangle : |γ| ≤ |γ-θ|+|θ| := by
      calc
        |γ|=|(γ-θ)+θ| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    linarith
  have hhi : |γ-θ| ≤ Real.pi-(Real.pi/3-6/7) := by
    have htriangle : |γ-θ| ≤ |γ|+|θ| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le γ (-θ)
    linarith [Real.pi_pos]
  have hh := sin_sq_gt_thirtieth_on_middle hlo hhi
  by_cases hx : 0 ≤ γ-θ
  · simpa only [abs_of_nonneg hx] using hh
  · simpa only [abs_of_neg (lt_of_not_ge hx), Real.sin_neg, neg_sq] using hh

end SpringerLean

#print axioms SpringerLean.trueAxis_phase_sine_sq_floor
