import SpringerLean.Round1783RotatedStripCoordinates
import SpringerLean.Round1774ActualCandidatePhaseEndpoints

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 700000

theorem rotated_complex_coordinates (ξ v w : ℂ) (δ : ℝ)
    (hv : v=ξ*Complex.exp ((δ : ℂ)*Complex.I)) :
    (conj v*w).re=Real.cos δ*(conj ξ*w).re+Real.sin δ*(conj ξ*w).im ∧
      (conj v*w).im=Real.cos δ*(conj ξ*w).im-Real.sin δ*(conj ξ*w).re := by
  rw [hv]
  constructor <;>
    simp [map_mul, Complex.mul_re, Complex.mul_im, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin] <;> ring

/-- The actual full-hull strip supplies the normalized transverse
quadratic and slope bounds used by both aligned subregions. -/
theorem exteriorOmitted_actualEndpoint_aligned_scaled_strip
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (v : ℂ) (δ : ℝ)
    (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδ : |(k : ℝ)*δ| ≤ Real.pi/3)
    (w : ℂ) (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hx : (9/5 : ℝ) ≤ (conj v*w).re) :
    let m := ((2*k-2 : ℕ) : ℝ)
    let y := m*exteriorFineEndpointWidth P
    let Q := m*|(conj (P/(‖P‖ : ℂ))*w).im|
    let s := m*(1-(conj v*w).re/2)
    let H := m*|(conj v*w).im|/(conj v*w).re
    0 ≤ y ∧ y ≤ 1/2 ∧ 0 ≤ Q ∧ 0 ≤ s ∧ 0 ≤ H ∧
      Q^2 ≤ 1+8*y*s+(7/2500 : ℝ)*Q ∧
      H ≤ 21/10+(4/7 : ℝ)*Q := by
  let m := ((2*k-2 : ℕ) : ℝ)
  let W := exteriorFineEndpointWidth P
  let ξ := P/(‖P‖ : ℂ)
  let x := (conj v*w).re
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hW0 : 0 ≤ W := by dsimp [W, exteriorFineEndpointWidth]; positivity
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hR : 0 < ‖P‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd.le]
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne']
  have hvnorm : ‖v‖=1 := by rw [hv, norm_mul, hξ, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hx2 : x ≤ 2 := by
    calc
      _ ≤ ‖conj v*w‖ := Complex.re_le_norm _
      _ = ‖w‖ := by rw [norm_mul, Complex.norm_conj, hvnorm, one_mul]
      _ ≤ 2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have hy0 : 0 ≤ m*W := mul_nonneg hm0 hW0
  have hQ0 : 0 ≤ m*|(conj ξ*w).im| := mul_nonneg hm0 (abs_nonneg _)
  have hs0 : 0 ≤ m*(1-x/2) := mul_nonneg hm0 (by linarith)
  have hH0 : 0 ≤ m*|(conj v*w).im|/x := by positivity
  obtain ⟨hC, hmt, hτ, hxC⟩ := aligned_ray_trig_bounds hk hδ
  have hC0 : 0 < Real.cos δ := by linarith
  have hτeq : Real.cos δ*|Real.tan δ|=|Real.sin δ| := by
    rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hC0]
    field_simp
  have hrot := rotated_complex_coordinates ξ v w δ hv
  have hstrip := (exteriorOmitted_actualEndpoint_fine_strip F hc k hk P hP hd ht w hw).2.1
  have hquad := rotated_strip_scaled_quadratic hm0 hW0
    (exteriorOmitted_norm_le_two F hc hP) hx0.le hC0 (Real.cos_le_one δ)
    hτeq hrot.1 hstrip
  have hcoarse := aligned_strip_quadratic_coarse hy0 hW.le hQ0
    (abs_nonneg (Real.tan δ)) hτ hquad
  have hxC' : (7/4 : ℝ) ≤ x*Real.cos δ := by
    have hh := mul_le_mul_of_nonneg_right hx hC0.le
    nlinarith
  have hslope := rotated_strip_scaled_slope hm0 hx0 hC0
    (Real.cos_sq_add_sin_sq δ) hτeq hrot.1 hrot.2 hmt hxC'
  exact ⟨hy0, hW.le, hQ0, hs0, hH0, hcoarse, hslope⟩

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_actualEndpoint_aligned_scaled_strip
