import SpringerLean.Round09WeightedImage

open MeasureTheory

namespace SpringerLean

/-- Weighted area scaling for the actual omitted set of the regular dilate.
The weight is evaluated on the genuine sets `K(F_s)` and `K_s`. -/
theorem rescaleExterior_omitted_weighted_integral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (m : ℕ) :
    (∫ w in exteriorOmitted (rescaleExterior s F), ‖w‖ ^ m ∂volume) =
      s ^ (m + 2) *
        (∫ w in exteriorOmittedAtScale F s, ‖w‖ ^ m ∂volume) := by
  let K : Set ℂ := exteriorOmittedAtScale F s
  let L : ℂ →L[ℝ] ℂ := (s : ℂ) • (1 : ℂ →L[ℝ] ℂ)
  have hL : (fun w : ℂ => (s : ℂ) * w) = (L : ℂ → ℂ) := by
    funext w
    simp [L]
  have hderiv : ∀ w ∈ K,
      HasFDerivWithinAt (fun v : ℂ => (s : ℂ) * v) L K w := by
    intro w hw
    rw [hL]
    exact L.hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn (fun w : ℂ => (s : ℂ) * w) K := by
    intro x hx y hy hxy
    have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    exact mul_left_cancel₀ hsne hxy
  have hmeas : MeasurableSet K :=
    exteriorOmittedAtScale_measurableSet F hc hs0 hs1
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume) hmeas hderiv hinj (fun w : ℂ => ‖w‖ ^ m)
  rw [← rescaleExterior_omitted_eq_image F hs0] at hchange
  have hfun : (fun w : ℂ => |L.det| • ‖(s : ℂ) * w‖ ^ m) =
      (fun w : ℂ => s ^ (m + 2) * ‖w‖ ^ m) := by
    funext w
    change |((s : ℂ) • (1 : ℂ →L[ℝ] ℂ)).det| •
      ‖(s : ℂ) * w‖ ^ m = s ^ (m + 2) * ‖w‖ ^ m
    rw [complex_mul_real_det, Complex.normSq_eq_norm_sq, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    rw [abs_of_nonneg (sq_nonneg s)]
    simp only [smul_eq_mul, mul_pow, pow_add]
    ring
  rw [hfun, integral_const_mul] at hchange
  exact hchange

end SpringerLean
