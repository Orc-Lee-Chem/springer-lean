import SpringerLean.Round30OuterSplit

open MeasureTheory Set Filter
open scoped Topology

namespace SpringerLean

/-- The signed compensated tail also tends uniformly to zero with bounded
vertical shifts, by domination by the previously verified absolute tail. -/
theorem regularExterior_vertical_difference_shifted_tail_uniformOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (K : Set ℝ) (hK : IsCompact K) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun (n : ℕ) (p : ℝ × ℝ) =>
        ∫ t in (Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)))ᶜ,
          regularExteriorVerticalPotentialDifference F s ξ p.1 (t + p.2))
      (fun _ => (0 : ℝ)) atTop (K ×ˢ Icc (-R) R) := by
  have hU := regularExterior_vertical_difference_shifted_abs_tail_uniformOn
    F hc hs0 hs1 ξ K hK R hR
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) η hη]
    with n hn
  intro p hp
  have hAbs := abs_integral_le_integral_abs
    (f := fun t : ℝ =>
      regularExteriorVerticalPotentialDifference F s ξ p.1 (t + p.2))
    (μ := volume.restrict ((Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)))ᶜ))
  have hIntNonneg : 0 ≤
      (∫ t in (Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)))ᶜ,
        |regularExteriorVerticalPotentialDifference F s ξ p.1 (t + p.2)|) :=
    integral_nonneg (fun _ => abs_nonneg _)
  have h := hn p hp
  have hsmall :
      (∫ t in (Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)))ᶜ,
        |regularExteriorVerticalPotentialDifference F s ξ p.1 (t + p.2)|) < η := by
    simpa [Real.dist_eq, abs_of_nonneg hIntNonneg] using h
  change dist (0 : ℝ) (∫ t in (Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)))ᶜ,
    regularExteriorVerticalPotentialDifference F s ξ p.1 (t + p.2)) < η
  rw [Real.dist_eq, zero_sub, abs_neg]
  exact lt_of_le_of_lt hAbs hsmall

end SpringerLean