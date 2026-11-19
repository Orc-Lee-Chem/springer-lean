import SpringerLean.Round31OuterFunctions
import SpringerLean.Round30ShiftedTailSigned

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean

/-- Finite-annulus compensated integrals converge uniformly to the actual
unbounded outer-tail integral on every circle with radius below T. -/
theorem regularVerticalFiniteAnnulus_tendstoUniformlyOn_circle
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a T ρ : ℝ) (hρ : 0 ≤ ρ) (hρT : ρ < T) :
    TendstoUniformlyOn
      (fun n : ℕ => regularVerticalFiniteAnnulus F s ξ T (2 * (n : ℝ)))
      (regularVerticalOuterTail F s ξ T) atTop (sphere (a : ℂ) |ρ|) := by
  let K : Set ℝ := Icc (a - ρ) (a + ρ)
  have hK : IsCompact K := isCompact_Icc
  have hU := regularExterior_vertical_difference_shifted_tail_uniformOn
    F hc hs0 hs1 ξ K hK ρ hρ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) η hη,
    (eventually_ge_atTop (Nat.ceil T))] with n hn hnT
  intro z hz
  have hrad : ‖z - (a : ℂ)‖ = ρ := by
    simpa [mem_sphere, dist_eq_norm, abs_of_nonneg hρ] using hz
  have hre : |z.re - a| ≤ ρ := by
    have h := Complex.abs_re_le_norm (z - (a : ℂ))
    simpa [Complex.sub_re, hrad] using h
  have him : |z.im| ≤ ρ := by
    have h := Complex.abs_im_le_norm (z - (a : ℂ))
    simpa [Complex.sub_im, hrad] using h
  have hp : (z.re, z.im) ∈ K ×ˢ Icc (-ρ) ρ := by
    exact ⟨⟨by linarith [(abs_le.mp hre).1],
      by linarith [(abs_le.mp hre).2]⟩,
      abs_le.mp him⟩
  have hTn : T ≤ 2 * (n : ℝ) := by
    have hT0 : T ≤ (Nat.ceil T : ℝ) := Nat.le_ceil T
    have hN : (Nat.ceil T : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnT
    have hN0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hsplit := regularVerticalOuterTail_eq_finite_add_tail
    F hc hs0 hs1 ξ z T (2 * (n : ℝ)) hTn
  have hsmall := hn (z.re, z.im) hp
  change dist (regularVerticalOuterTail F s ξ T z)
    (regularVerticalFiniteAnnulus F s ξ T (2 * (n : ℝ)) z) < η
  rw [hsplit, Real.dist_eq]
  simpa [Real.dist_eq] using hsmall

end SpringerLean