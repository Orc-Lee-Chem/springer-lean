import SpringerLean.Round1862RealBetaIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory Set

namespace SpringerLean

theorem cosine_beta_substitution_point (p θ : ℝ)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    (Real.sin θ ^ 2) ^ (-1 / 2 : ℝ) *
        (1 - Real.sin θ ^ 2) ^ ((p - 1) / 2) *
        (2 * Real.sin θ * Real.cos θ) = 2 * (Real.cos θ) ^ p := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsquare : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hsquare, ← Real.rpow_natCast_mul hs.le, ← Real.rpow_natCast_mul hc.le]
  norm_num only [Nat.cast_ofNat]
  have he2 : (2 : ℝ) * ((p - 1) / 2) = p - 1 := by ring
  rw [he2, Real.rpow_neg_one, Real.rpow_sub_one hc.ne']
  field_simp
  <;> ring

/-- A nonsingular monotone substitution on the angle interval.  The
beta density may be unbounded at its endpoints; no continuity there
is assumed. -/
theorem two_integral_cos_rpow_eq_radialBetaIntegral (p : ℝ) :
    2 * (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ p) =
      radialBetaIntegral (1 / 2) ((p + 1) / 2) := by
  let u : ℝ → ℝ := fun θ => Real.sin θ ^ 2
  let du : ℝ → ℝ := fun θ => 2 * Real.sin θ * Real.cos θ
  let g : ℝ → ℝ := fun x => x ^ (-1 / 2 : ℝ) * (1 - x) ^ ((p - 1) / 2)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := Real.pi / 2) (f := u) (f' := du) (g := g)
    (by fun_prop) (by
      intro θ hθ
      convert (Real.hasDerivAt_sin θ).pow 2 using 1 <;> simp [u, du, mul_assoc]) (by
      intro θ hθ
      rw [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2),
        max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
      have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos])
      have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      exact mul_nonneg (mul_nonneg (by norm_num) hs.le) hc.le)
  have heq : (∫ θ in (0 : ℝ)..(Real.pi / 2), (g ∘ u) θ * du θ) =
      ∫ θ in (0 : ℝ)..(Real.pi / 2), 2 * (Real.cos θ) ^ p := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (Real.pi / 2)] with θ hne hθ
    have hθ' : θ ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
      have hh : θ ∈ Ioc (0 : ℝ) (Real.pi / 2) := by
        simpa only [uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
      exact ⟨hh.1, (lt_or_eq_of_le hh.2).resolve_right hne⟩
    exact cosine_beta_substitution_point p θ hθ'
  rw [heq, intervalIntegral.integral_const_mul] at hsub
  have hstart : u 0 = 0 := by simp [u]
  have hend : u (Real.pi / 2) = 1 := by simp [u]
  rw [hstart, hend] at hsub
  have he1 : (1 / 2 : ℝ) - 1 = -1 / 2 := by norm_num
  have he2 : (p + 1) / 2 - 1 = (p - 1) / 2 := by ring
  simpa only [radialBetaIntegral, g, he1, he2] using hsub

end SpringerLean

#print axioms SpringerLean.two_integral_cos_rpow_eq_radialBetaIntegral
