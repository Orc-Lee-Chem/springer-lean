import SpringerLean.Round1764SelectedTiltedProjectionCap
import SpringerLean.Round1567ActualUnitDiskCubicGain

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

theorem exteriorOmitted_actual_selected_second_tilted_cap
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ exteriorOmitted F)
    (hd₁ : 0 < 2-‖P₁‖)
    (ht₁ : ((2*k-1 : ℕ) : ℝ)*(2-‖P₁‖) < 3/20)
    (hd₂ : 0 < 2-‖P₂‖)
    (ht₂ : ((2*k-1 : ℕ) : ℝ)*(2-‖P₂‖) < 3/20)
    (hmW₁ : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P₁ < 1/2)
    (hneg : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0)
    (hmax₂ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖)
    (v : ℂ) (hv : ‖v‖ = 1)
    (hclose : ‖v-P₂/(‖P₂‖ : ℂ)‖ ≤ 1/4) :
    ∀ w ∈ convexHull ℝ (exteriorOmitted F), (conj v*w).re ≤ ‖P₂‖ := by
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hm : (1500 : ℝ) ≤ ((2*k-2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hR₁le : ‖P₁‖ ≤ 2 := exteriorOmitted_norm_le_two F hc hP₁
  have hR₁ : 0 < ‖P₁‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hn hd₁.le]
  have hR₂ : 1 < ‖P₂‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hn hd₂.le]
  let W := exteriorFineEndpointWidth P₁
  have hW0 : 0 ≤ W := by dsimp [W, exteriorFineEndpointWidth]; positivity
  have hW : W < 1/3000 := by
    have hmul := mul_le_mul_of_nonneg_right hm hW0
    dsimp [W] at hmW₁ ⊢
    nlinarith
  have hstrip : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*w).im^2 ≤
        4*W*(W+‖P₁‖-(conj (P₁/(‖P₁‖ : ℂ))*w).re) := by
    intro w hw
    exact (exteriorOmitted_actualEndpoint_fine_strip
      F hc k hk P₁ hP₁ hd₁ ht₁ w hw).2.1
  exact selectedEndpoints_second_nearby_direction_cap F hc P₁ P₂ W
    hR₁ hR₁le hR₂ hW0 hW hneg hmax₂ hstrip v hv hclose

/-- The full-disk saving depends on a direction only through its
whole-hull cap. The same radius and deficit can therefore be used
for a tilted direction, with no new Poisson or thin-ring estimate. -/
theorem actualHarmonic_positivePower_unitDisk_cubic_gain_of_radius
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : ℂ) (hv : ‖v‖ = 1) (R : ℝ) (hR0 : 0 < R) (hR2 : R < 2)
    {m : ℕ} (hm : 1500 ≤ m) (hD : (m : ℝ)*(2-R) ≤ 3/20)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F), (conj v*w).re ≤ R) :
    ((m : ℝ)*(2-R))^3/30 <
      ((m : ℝ)*Real.sqrt (m : ℝ)/(2 : ℝ)^m)*Real.pi⁻¹*
      (∫ z in ball (0 : ℂ) 1,
        (max (2*z.re) 0)^m -
          (max ((conj v*actualHarmonic F z).re) 0)^m) := by
  obtain ⟨h, hh0, hhpi, hR⟩ := exists_flattened_angle_of_radius hR0 hR2
  exact actualHarmonic_positivePower_unitDisk_cubic_gain F hc v hv
    hh0 hhpi (by linarith [hR]) (by linarith)
    (by simpa only [← hR] using hcap) hm hD

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_actual_selected_second_tilted_cap
#print axioms SpringerLean.actualHarmonic_positivePower_unitDisk_cubic_gain_of_radius
