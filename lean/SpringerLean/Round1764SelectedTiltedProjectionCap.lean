import SpringerLean.Round1495SecondGlobalCap

open scoped ComplexConjugate

namespace SpringerLean

theorem unit_projection_perturbation_le (v a w : ℂ) :
    (conj v*w).re ≤ (conj a*w).re + ‖v-a‖*‖w‖ := by
  have h := Complex.re_le_norm (conj (v-a)*w)
  rw [norm_mul, Complex.norm_conj] at h
  have heq : (conj (v-a)*w).re = (conj v*w).re-(conj a*w).re := by
    simp only [map_sub, sub_mul, Complex.sub_re]
  linarith

/-- The second selected endpoint caps every nearby unit direction
on the WHOLE actual omitted hull. On the assigned negative half use
radius maximality; on the positive half use the first endpoint's
strip and perturb the direction. -/
theorem selectedEndpoints_second_nearby_direction_cap
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P₁ P₂ : ℂ) (W : ℝ)
    (hR₁ : 0 < ‖P₁‖) (hR₁le : ‖P₁‖ ≤ 2)
    (hR₂ : 1 < ‖P₂‖)
    (hW0 : 0 ≤ W) (hW : W < 1/3000)
    (hneg : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0)
    (hmax₂ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖)
    (hstrip : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*w).im^2 ≤
        4*W*(W+‖P₁‖-(conj (P₁/(‖P₁‖ : ℂ))*w).re))
    (v : ℂ) (hv : ‖v‖ = 1)
    (hclose : ‖v-P₂/(‖P₂‖ : ℂ)‖ ≤ 1/4) :
    ∀ w ∈ convexHull ℝ (exteriorOmitted F), (conj v*w).re ≤ ‖P₂‖ := by
  intro w hw
  by_cases hx : (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0
  · calc
      (conj v*w).re ≤ ‖conj v*w‖ := Complex.re_le_norm _
      _ = ‖w‖ := by rw [norm_mul, Complex.norm_conj, hv, one_mul]
      _ ≤ ‖P₂‖ := hmax₂ w hw hx
  · have hforward : 0 ≤ (conj (P₁/(‖P₁‖ : ℂ))*w).re :=
      le_of_lt (lt_of_not_ge hx)
    have hunit : ‖P₁/(‖P₁‖ : ℂ)‖ = 1 := by
      simp [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR₁, ne_of_gt hR₁]
    have htrans := oppositeAxis_projection_le_transverse
      (P₁/(‖P₁‖ : ℂ)) P₂ w hunit (by linarith) hneg hforward
    have hs := hstrip w hw
    have hsmall : |(conj (P₁/(‖P₁‖ : ℂ))*w).im| < 1/10 := by
      have hsq : (conj (P₁/(‖P₁‖ : ℂ))*w).im^2 < (1/10 : ℝ)^2 := by
        nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hR₁le)]
      nlinarith [sq_abs (conj (P₁/(‖P₁‖ : ℂ))*w).im,
        abs_nonneg (conj (P₁/(‖P₁‖ : ℂ))*w).im]
    have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
    have hpert := unit_projection_perturbation_le v (P₂/(‖P₂‖ : ℂ)) w
    have hcost : ‖v-P₂/(‖P₂‖ : ℂ)‖*‖w‖ ≤ (1/4 : ℝ)*2 :=
      mul_le_mul hclose hw2 (norm_nonneg _) (by norm_num)
    linarith

end SpringerLean

#print axioms SpringerLean.selectedEndpoints_second_nearby_direction_cap
