import SpringerLean.Round29LargeCore
import SpringerLean.Round29ActualComplement

open MeasureTheory Set

namespace SpringerLean

/-- On bounded horizontal strips, increasing height pushes both actual
reference-error complement integrals into one prescribed outer tail. -/
theorem regularVerticalAuxiliary_large_height_tail_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, ∃ H : ℝ, 0 < H ∧ ∀ (a h : ℝ), |a| ≤ A → H ≤ h →
      regularVerticalAuxiliary F s ξ a h ≤
        2 * C * (∫ t in (Icc (-L) L)ᶜ, (1 + t ^ 2)⁻¹) := by
  obtain ⟨C, hC0, hC⟩ :=
    regularExterior_potentials_reference_global_quadratic F hc hs0 hs1 ξ hξ
  refine ⟨C, hC0, ?_⟩
  intro L
  obtain ⟨H₀, hH₀, hcore⟩ :=
    regularVerticalCosts_large_height_core_minimizer F hc hs0 hs1 ξ hξ A L
  let H : ℝ := max H₀ (L + 1)
  have hH : 0 < H := lt_of_lt_of_le hH₀ (le_max_left _ _)
  refine ⟨H, hH, ?_⟩
  intro a h ha hh
  have hh0 : 0 < h := lt_of_lt_of_le hH hh
  have hH₀h : H₀ ≤ h := (le_max_left _ _).trans hh
  have hLh : L ≤ h := by
    have := (le_max_right H₀ (L + 1)).trans hh
    linarith
  obtain ⟨E, hE, hLE, hmin⟩ := hcore a h ha hH₀h
  have hU := regularVerticalAuxiliary_le_reference_complement_errors
    F hc hs0 hs1 ξ hξ a h hh0 E hE hmin
  let S : Set ℝ := (Icc (-L) L)ᶜ
  let ka : ℝ → ℝ := fun t => (1 + t ^ 2)⁻¹
  let eg : ℝ → ℝ := fun t =>
    |regularExteriorRotatedPotential F s ξ
      ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t|
  let eG : ℝ → ℝ := fun t =>
    |comparisonSegmentPotential
      ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t|
  have herr := regularExterior_reference_vertical_errors_integrable
    F hc hs0 hs1 ξ hξ a
  have hka : Integrable ka := by
    have h := verticalReferenceErrorKernel_integrable 0
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, zero_add, ka] using h
  have hdomInt : Integrable (fun t => C * ka t) := hka.const_mul C
  have hpoint (t : ℝ) : eg t + eG t ≤ C * ka t := by
    have hz := hC ((a : ℂ) + (t : ℂ) * Complex.I)
    rw [radialReferencePotential_vertical, vertical_complex_norm_sq] at hz
    have hden1 : 0 < 1 + t ^ 2 := by positivity
    have hden2 : 0 < 1 + a ^ 2 + t ^ 2 := by positivity
    have hdiv : C / (1 + a ^ 2 + t ^ 2) ≤ C / (1 + t ^ 2) := by
      apply (div_le_div_iff₀ hden2 hden1).2
      nlinarith [sq_nonneg a]
    dsimp [eg, eG, ka]
    calc
      _ ≤ C / (1 + a ^ 2 + t ^ 2) := by
        simpa only [div_eq_mul_inv, ← add_assoc] using hz
      _ ≤ C / (1 + t ^ 2) := hdiv
      _ = C * (1 + t ^ 2)⁻¹ := by ring
  have hnonneg (t : ℝ) : 0 ≤ eg t ∧ 0 ≤ eG t := ⟨abs_nonneg _, abs_nonneg _⟩
  have hES : Eᶜ ⊆ S := compl_subset_compl.mpr hLE
  have hIS : (Icc (-h) h)ᶜ ⊆ S := by
    apply compl_subset_compl.mpr
    intro t ht
    change -L ≤ t ∧ t ≤ L at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgS : (∫ t in Eᶜ, eg t) ≤ ∫ t in S, eg t :=
    setIntegral_mono_set herr.1.abs.integrableOn
      (Filter.Eventually.of_forall fun t => (hnonneg t).1)
      (Filter.Eventually.of_forall hES)
  have hGS : (∫ t in (Icc (-h) h)ᶜ, eG t) ≤ ∫ t in S, eG t :=
    setIntegral_mono_set herr.2.abs.integrableOn
      (Filter.Eventually.of_forall fun t => (hnonneg t).2)
      (Filter.Eventually.of_forall hIS)
  have hgdom : (∫ t in S, eg t) ≤ ∫ t in S, C * ka t := by
    apply integral_mono herr.1.abs.integrableOn hdomInt.integrableOn
    intro t
    linarith [(hpoint t), (hnonneg t).2]
  have hGdom : (∫ t in S, eG t) ≤ ∫ t in S, C * ka t := by
    apply integral_mono herr.2.abs.integrableOn hdomInt.integrableOn
    intro t
    linarith [(hpoint t), (hnonneg t).1]
  have hfactor : (∫ t in S, C * ka t) = C * ∫ t in S, ka t :=
    by rw [integral_const_mul]
  dsimp [S, eg, eG] at hU hgS hGS
  dsimp [S, ka] at hfactor
  linarith

end SpringerLean
