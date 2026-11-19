import SpringerLean.Round1863CosineBetaIntegral
import SpringerLean.Round1849ActualRadialTwoSlit

namespace SpringerLean

theorem normalized_cosine_half_integral_eq_slit_constant
    (p : ℝ) (hp : 0 < p) :
    (2 : ℝ) ^ (p + 1) / Real.pi *
      (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ p) =
      slitRadialMomentConstant p := by
  have hhalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := by
    have hh := Real.Gamma_mul_Gamma_add_half (1 / 2 : ℝ)
    norm_num at hh
    exact hh
  have hsum : (1 / 2 : ℝ) + (p + 1) / 2 = 1 + p / 2 := by ring
  have hbeta := gamma_mul_gamma_eq_radialBetaIntegral
    (s := (1 / 2 : ℝ)) (t := (p + 1) / 2) (by norm_num) (by linarith)
  rw [hhalf, hsum, ← two_integral_cos_rpow_eq_radialBetaIntegral] at hbeta
  have hdup := Real.Gamma_mul_Gamma_add_half ((p + 1) / 2)
  have he1 : (p + 1) / 2 + 1 / 2 = 1 + p / 2 := by ring
  have he2 : 2 * ((p + 1) / 2) = p + 1 := by ring
  have he3 : 1 - 2 * ((p + 1) / 2) = -p := by ring
  rw [he1, he3, he2] at hdup
  have hP : (2 : ℝ) ^ p ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hdp : Real.Gamma ((p + 1) / 2) * Real.Gamma (1 + p / 2) * (2 : ℝ) ^ p =
      Real.Gamma (p + 1) * Real.sqrt Real.pi := by
    rw [hdup, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have hsquare : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hbalance : 2 * (2 : ℝ) ^ p *
      (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ p) *
        Real.Gamma (1 + p / 2) ^ 2 = Real.Gamma (p + 1) * Real.pi := by
    linear_combination
      -(Real.Gamma (1 + p / 2) * (2 : ℝ) ^ p) * hbeta +
      Real.sqrt Real.pi * hdp + Real.Gamma (p + 1) * hsquare
  have hG : Real.Gamma (1 + p / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + p / 2)).ne'
  have hpower : (2 : ℝ) ^ (p + 1) = 2 * (2 : ℝ) ^ p := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  rw [hpower, slitRadialMomentConstant]
  field_simp [Real.pi_ne_zero, hG]
  rw [show (2 + p) / 2 = 1 + p / 2 by ring]
  nlinarith [hbalance]

end SpringerLean

#print axioms SpringerLean.normalized_cosine_half_integral_eq_slit_constant
