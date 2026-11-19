import SpringerLean.Round1407StripAffineScalar
import SpringerLean.Round1408WidthSmallness
import SpringerLean.Round1405ActualLocalizedWidth

open scoped ComplexConjugate

namespace SpringerLean

/-- On the positive projection half of an actual localized endpoint,
the root strip pays for the explicit affine radius majorant. The
assignment of all high-radius points to this half is a separate step. -/
theorem exteriorOmitted_actualEndpoint_positive_affine_cap
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd0 : 0 < 2-‖P‖)
    (hdef : ((2*k-1:ℕ):ℝ)*(2-‖P‖) < 1)
    (w : ℂ) (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hx0 : 0 ≤ (conj (P/(‖P‖:ℂ))*w).re) :
    let ξ : ℂ := P/(‖P‖:ℂ)
    let W : ℝ := (exteriorRealRootWidth ‖P‖
      (1+Real.sqrt (2-‖P‖)/10))^2
    ‖w‖ ≤ max (19/10 : ℝ)
      (2-(1-(107/100 : ℝ)*W)*(2-(conj ξ*w).re)+(107/100 : ℝ)*W^2) := by
  let d : ℝ := 2-‖P‖
  let ξ : ℂ := P/(‖P‖:ℂ)
  let r : ℝ := 1+Real.sqrt d/10
  let W : ℝ := (exteriorRealRootWidth ‖P‖ r)^2
  let x : ℝ := (conj ξ*w).re
  have hnNat : 1501 ≤ 2*k-1 := by omega
  have hn : (1501 : ℝ) ≤ ((2*k-1:ℕ):ℝ) := by exact_mod_cast hnNat
  have hdn : d ≤ (1/1501 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hn hd0.le
    dsimp only [d]
    nlinarith
  have hPnorm : 0 < ‖P‖ := by dsimp [d] at hdn; linarith
  have hξ : ‖ξ‖ = 1 := by
    dsimp [ξ]
    simp [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hPnorm, ne_of_gt hPnorm]
  have hw2 : ‖w‖ ≤ 2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have hx2 : x ≤ 2 := by
    have hre := Complex.re_le_norm (conj ξ*w)
    have hnorm : ‖conj ξ*w‖ = ‖w‖ := by
      rw [norm_mul, Complex.norm_conj, hξ, one_mul]
    dsimp only [x]
    rw [hnorm] at hre
    linarith
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hW : W ≤ (1/100 : ℝ) := by
    have hh := mediumWidth_sq_lt_one_hundred hd0 hdn
    have heq : (2 : ℝ)-d=‖P‖ := by dsimp [d]; ring
    rw [heq] at hh
    exact hh.le
  have hstrip := exteriorOmitted_actualEndpoint_localized_strip
    F hc k hk P hP hd0 hdef w hw
  dsimp only at hstrip
  have hvstrip : ‖w‖^2 ≤ (x-2*W)^2+4*W*‖P‖ := hstrip.2.2
  have hR : ‖P‖ ≤ 2 := exteriorOmitted_norm_le_two F hc hP
  have hcap := smallStrip_affinePlatform_radius_cap
    hx0 hx2 hR hW0 hW (norm_nonneg w) hvstrip
  dsimp only
  exact hcap

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_actualEndpoint_positive_affine_cap
