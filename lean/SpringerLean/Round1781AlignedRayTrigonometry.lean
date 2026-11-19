import SpringerLean.Round1780AlignedStripBudget

namespace SpringerLean
set_option maxHeartbeats 400000

theorem aligned_ray_trig_bounds {k : ℕ} (hk : 751 ≤ k) {δ : ℝ}
    (hδ : |(k : ℝ)*δ| ≤ Real.pi/3) :
    (999/1000 : ℝ) ≤ Real.cos δ ∧
      ((2*k-2 : ℕ) : ℝ)*|Real.tan δ| ≤ 21/10 ∧
      |Real.tan δ| ≤ 7/5000 ∧ (7/4 : ℝ) ≤ (9/5 : ℝ)*Real.cos δ := by
  have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hm : ((2*k-2 : ℕ) : ℝ)=2*(k : ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2*k), Nat.cast_mul, Nat.cast_ofNat]
  have hm0 : (0 : ℝ) ≤ ((2*k-2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_mul, abs_of_nonneg hk0] at hδ
  have hδsmall : |δ| ≤ 1/100 := by
    have hh := mul_le_mul_of_nonneg_right hk' (abs_nonneg δ)
    linarith [Real.pi_lt_four]
  have hδsq : δ^2 ≤ 1/10000 := by
    nlinarith [sq_abs δ, mul_nonneg (sub_nonneg.mpr hδsmall) (add_nonneg (abs_nonneg δ) (by norm_num : (0 : ℝ) ≤ 1/100))]
  have hcos : (999/1000 : ℝ) ≤ Real.cos δ := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := δ)]
  have hcos0 : 0 < Real.cos δ := by linarith
  have htan : ((2*k-2 : ℕ) : ℝ)*|Real.tan δ| ≤ 21/10 := by
    rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcos0, ← mul_div_assoc]
    apply (div_le_iff₀ hcos0).mpr
    have hs := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := δ)) hm0
    rw [hm] at hs ⊢
    have hpi : Real.pi < 1571/500 := by linarith [Real.pi_lt_d4]
    nlinarith [abs_nonneg δ]
  have hτ : |Real.tan δ| ≤ 7/5000 := by
    have hh := mul_le_mul_of_nonneg_right
      (show (1500 : ℝ) ≤ ((2*k-2 : ℕ) : ℝ) by rw [hm]; linarith)
      (abs_nonneg (Real.tan δ))
    nlinarith
  exact ⟨hcos, htan, hτ, by linarith⟩

end SpringerLean

#print axioms SpringerLean.aligned_ray_trig_bounds
