import SpringerLean.Round30TailDomination
import SpringerLean.Round27UniformTail

open MeasureTheory Set Filter
open scoped Topology

namespace SpringerLean

/-- The absolute compensated tail is uniformly small on a compact horizontal
set and a bounded range of vertical translations. The two logarithms remain
paired as one integrable difference. -/
theorem regularExterior_vertical_difference_shifted_abs_tail_uniformOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (K : Set ℝ) (hK : IsCompact K) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun (n : ℕ) (p : ℝ × ℝ) =>
        ∫ t in (Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)))ᶜ,
          |regularExteriorVerticalPotentialDifference F s ξ p.1 (t + p.2)|)
      (fun _ => (0 : ℝ)) atTop (K ×ˢ Icc (-R) R) := by
  have hU := regularExterior_vertical_difference_abs_tail_uniformOn
    F hc hs0 hs1 ξ K hK
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) η hη,
    (eventually_ge_atTop (Nat.ceil R))] with n hn hnR
  intro p hp
  have hpK : p.1 ∈ K := hp.1
  have hpR : |p.2| ≤ R := abs_le.mpr hp.2
  have hRn : R ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil R) (by exact_mod_cast hnR)
  have hpN : |p.2| ≤ (n : ℝ) := le_trans hpR hRn
  have hInt : Integrable
      (regularExteriorVerticalPotentialDifference F s ξ p.1) :=
    regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ p.1
  have hdom := integral_shifted_outer_tail_abs_le
    (regularExteriorVerticalPotentialDifference F s ξ p.1) hInt
      (n : ℝ) p.2 hpN
  have hA :
      (∫ t in (Icc (-(n : ℝ)) (n : ℝ))ᶜ,
        |regularExteriorVerticalPotentialDifference F s ξ p.1 t|) < η := by
    have hnonneg : 0 ≤
        (∫ t in (Icc (-(n : ℝ)) (n : ℝ))ᶜ,
          |regularExteriorVerticalPotentialDifference F s ξ p.1 t|) :=
      integral_nonneg (fun _ => abs_nonneg _)
    have h := hn p.1 hpK
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using h
  have hnonneg : 0 ≤
      (∫ t in (Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)))ᶜ,
        |regularExteriorVerticalPotentialDifference F s ξ p.1 (t + p.2)|) :=
    integral_nonneg (fun _ => abs_nonneg _)
  change dist (0 : ℝ) (∫ t in (Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)))ᶜ,
    |regularExteriorVerticalPotentialDifference F s ξ p.1 (t + p.2)|) < η
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt hdom hA

end SpringerLean