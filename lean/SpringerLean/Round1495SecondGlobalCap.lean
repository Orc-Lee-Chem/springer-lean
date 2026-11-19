import SpringerLean.Round1494OppositeAxisProjection

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The fine first-end strip turns the second endpoint's assigned-half
radius maximum into a projection cap on the whole omitted hull. -/
theorem selectedEndpoints_second_full_axis_cap
    (F : ℂ → ℂ) (P₁ P₂ : ℂ) (W : ℝ)
    (hR₁ : 0 < ‖P₁‖) (hR₁le : ‖P₁‖ ≤ 2)
    (hR₂ : 1 < ‖P₂‖)
    (hW0 : 0 ≤ W) (hW : W < 1/3000)
    (hneg : (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0)
    (hmax₂ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖)
    (hstrip : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).im^2 ≤
        4*W*(W+‖P₁‖-(conj (P₁/(‖P₁‖:ℂ))*w).re)) :
    ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₂/(‖P₂‖:ℂ))*w).re ≤ ‖P₂‖ := by
  intro w hw
  by_cases hx : (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0
  · have hunit : ‖P₂/(‖P₂‖:ℂ)‖=1 := by
      simp [norm_div,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (by linarith : 0<‖P₂‖),ne_of_gt (by linarith : 0<‖P₂‖)]
    calc
      (conj (P₂/(‖P₂‖:ℂ))*w).re ≤
          ‖conj (P₂/(‖P₂‖:ℂ))*w‖ := Complex.re_le_norm _
      _ = ‖w‖ := by rw [norm_mul,Complex.norm_conj,hunit,one_mul]
      _ ≤ ‖P₂‖ := hmax₂ w hw hx
  · have hxf : 0 ≤ (conj (P₁/(‖P₁‖:ℂ))*w).re := le_of_lt (lt_of_not_ge hx)
    have hunit : ‖P₁/(‖P₁‖:ℂ)‖=1 := by
      simp [norm_div,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hR₁,ne_of_gt hR₁]
    have htrans := oppositeAxis_projection_le_transverse
      (P₁/(‖P₁‖:ℂ)) P₂ w hunit (by linarith) hneg hxf
    have hs := hstrip w hw
    have hbound : (conj (P₁/(‖P₁‖:ℂ))*w).im^2 < (1/10:ℝ)^2 := by
      nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hR₁le)]
    have habs : |(conj (P₁/(‖P₁‖:ℂ))*w).im| < 1/10 := by
      nlinarith [sq_abs (conj (P₁/(‖P₁‖:ℂ))*w).im,
        abs_nonneg (conj (P₁/(‖P₁‖:ℂ))*w).im]
    linarith

end SpringerLean

#print axioms SpringerLean.selectedEndpoints_second_full_axis_cap
