import SpringerLean.Round1322ImaginaryTail

namespace SpringerLean

/-- Exact rational payment of the two error terms in the imaginary
square-root identity.  This lemma contains no analytic hypotheses. -/
theorem imaginary_root_projection_lt_neg_eight_fifths
    (A M : ℝ) (T : ℂ)
    (hA : (359/360 : ℝ) < A)
    (hM0 : 0 ≤ M) (hM : M ≤ (49/24 : ℝ))
    (hT : ‖T‖ < (3/40 : ℝ)) :
    (-(1+(A : ℂ)^2)*(24/25 : ℂ)+
      2*Complex.I*(M : ℂ)*T+T^2).re < -(8/5 : ℝ) := by
  have hA0 : 0 ≤ A := by linarith
  have hAsq : (359/360 : ℝ)^2 < A^2 :=
    (sq_lt_sq₀ (by norm_num) hA0).mpr hA
  have hmain : (153/80 : ℝ) < (1+A^2)*(24/25 : ℝ) := by
    nlinarith [hAsq]
  have hterm : (2*Complex.I*(M : ℂ)*T).re ≤ 2*M*‖T‖ := by
    calc
      _ ≤ ‖2*Complex.I*(M : ℂ)*T‖ := Complex.re_le_norm _
      _ = 2*M*‖T‖ := by
        simp only [norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hM0]
        norm_num
  have hterm2 : (T^2).re ≤ ‖T‖^2 := by
    calc
      _ ≤ ‖T^2‖ := Complex.re_le_norm _
      _ = ‖T‖^2 := norm_pow _ _
  have hMt : 2*M*‖T‖ ≤ 2*(49/24 : ℝ)*‖T‖ := by
    have hh := mul_le_mul_of_nonneg_right hM
      (show 0 ≤ 2*‖T‖ by positivity)
    nlinarith [hh]
  have hTplus : 2*(49/24 : ℝ)*‖T‖ < 2*(49/24 : ℝ)*(3/40 : ℝ) := by
    exact mul_lt_mul_of_pos_left hT (by norm_num)
  have hTsq : ‖T‖^2 < (3/40 : ℝ)^2 :=
    (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mpr hT
  have herr : 2*M*‖T‖+‖T‖^2 < (5/16 : ℝ) := by
    nlinarith [hMt,hTplus,hTsq]
  have hreal : (-(1+(A : ℂ)^2)*(24/25 : ℂ)).re =
      -(1+A^2)*(24/25 : ℝ) := by
    norm_num [Complex.mul_re, Complex.add_re, pow_two]
  simp only [Complex.add_re]
  rw [hreal]
  linarith

end SpringerLean
