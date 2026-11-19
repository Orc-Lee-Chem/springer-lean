import SpringerLean.Round1790ActualOuterFirstProjection

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 900000

theorem opposite_outer_axis_projection
    (ξ P w : ℂ) (hξ : ‖ξ‖=1)
    (hRlo : (1999/1000 : ℝ) ≤ ‖P‖) (hRhi : ‖P‖ ≤ 2)
    (hPneg : (conj ξ*P).re ≤ 0) (hwneg : (conj ξ*w).re ≤ 0)
    (hwr : (46/25 : ℝ) ≤ ‖w‖)
    (hPq : (conj ξ*P).im^2 < 1/100) (hwq : (conj ξ*w).im^2 < 1/100) :
    (181/100 : ℝ) < (conj (P/(‖P‖ : ℂ))*w).re := by
  let u := conj ξ*w
  let z := conj ξ*P
  have hR : 0 < ‖P‖ := by linarith
  have hnormu : ‖u‖=‖w‖ := by dsimp [u]; rw [norm_mul, Complex.norm_conj, hξ, one_mul]
  have hnormz : ‖z‖=‖P‖ := by dsimp [z]; rw [norm_mul, Complex.norm_conj, hξ, one_mul]
  have hu2 : ‖w‖^2=u.re^2+u.im^2 := by
    rw [←hnormu, Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two]
  have hz2 : ‖P‖^2=z.re^2+z.im^2 := by
    rw [←hnormz, Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two]
  have hw2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 46/25) hwr 2
  have hP2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1999/1000) hRlo 2
  have hup : u.re < -183/100 := by
    by_contra hh
    have hh' := le_of_not_gt hh
    have hp := mul_nonneg (neg_nonneg.mpr hwneg)
      (sub_nonneg.mpr hh')
    nlinarith
  have hzp : z.re < -199/100 := by
    by_contra hh
    have hh' := le_of_not_gt hh
    have hp := mul_nonneg (neg_nonneg.mpr hPneg)
      (sub_nonneg.mpr hh')
    nlinarith
  have hprod : (36417/10000 : ℝ) < z.re*u.re := by
    have hp := mul_pos (show 0 < -z.re-199/100 by linarith)
      (show 0 < -u.re-183/100 by linarith)
    nlinarith
  have hqprod : -(1/100 : ℝ) < z.im*u.im := by
    nlinarith [sq_nonneg (z.im+u.im)]
  have hunit : ξ*conj ξ=1 := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ]
  have hmul : (ξ*conj P)*(conj ξ*w)=conj P*w := by
    calc
      _ = (ξ*conj ξ)*(conj P*w) := by ring
      _ = _ := by rw [hunit, one_mul]
  have hcomplex : conj (P/(‖P‖ : ℂ))*w=(conj z*u)/(‖P‖ : ℂ) := by
    dsimp [u, z]
    rw [map_div₀, Complex.conj_ofReal, map_mul, Complex.conj_conj, hmul]
    ring
  have hcoord : (conj (P/(‖P‖ : ℂ))*w).re=(z.re*u.re+z.im*u.im)/‖P‖ := by
    rw [hcomplex, div_eq_mul_inv, ←Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hcoord]
  apply (lt_div_iff₀ hR).mpr
  nlinarith

theorem exteriorOmitted_selected_second_outer_projection
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ exteriorOmitted F) (hP₂ : P₂ ∈ exteriorOmitted F)
    (hd₁ : 0 < 2-‖P₁‖) (ht₁ : ((2*k-1 : ℕ) : ℝ)*(2-‖P₁‖) < 3/20)
    (hW₁ : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P₁ < 1/2)
    (hd₂ : 0 < 2-‖P₂‖) (ht₂ : ((2*k-1 : ℕ) : ℝ)*(2-‖P₂‖) < 3/20)
    (hneg : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0)
    (w : ℂ) (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hr : (46/25 : ℝ) ≤ ‖w‖) (hwneg : (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0)
    (v : ℂ) (hv : ‖v-P₂/(‖P₂‖ : ℂ)‖ ≤ 1/200) :
    (9/5 : ℝ) < (conj v*w).re := by
  let ξ := P₁/(‖P₁‖ : ℂ)
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hR₁ : 0 < ‖P₁‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd₁.le]
  have hR₂ : (1999/1000 : ℝ) ≤ ‖P₂‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hn hd₂.le]
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR₁, div_self hR₁.ne']
  have hwP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F) := subset_convexHull ℝ _ hP₂
  have hqP := exteriorOmitted_actualEndpoint_transverse_sq_small F hc k hk P₁ hP₁ hd₁ ht₁ hW₁ P₂ hwP₂
  have hqw := exteriorOmitted_actualEndpoint_transverse_sq_small F hc k hk P₁ hP₁ hd₁ ht₁ hW₁ w hw
  have haxis := opposite_outer_axis_projection ξ P₂ w hξ hR₂
    (exteriorOmitted_norm_le_two F hc hP₂) hneg hwneg hr hqP hqw
  have hpert := unit_projection_perturbation_le (P₂/(‖P₂‖ : ℂ)) v w
  have hcost : ‖P₂/(‖P₂‖ : ℂ)-v‖*‖w‖ ≤ 1/100 := by
    rw [norm_sub_rev]
    have hh := mul_le_mul hv (exteriorOmitted_convexHull_norm_le_two F hc hw)
      (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1/200)
    nlinarith
  linarith

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_selected_second_outer_projection
