import SpringerLean.Round29LargeHeightTail
import SpringerLean.Round27Tail

open MeasureTheory Set Filter
open scoped Topology

namespace SpringerLean

/-- Along vertical escape on every bounded horizontal strip, the actual
auxiliary has limsup at most zero, uniformly in the horizontal coordinate. -/
theorem regularVerticalAuxiliary_vertical_limsup_le_zero_on_strip
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (A : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ H : ℝ, 0 < H ∧
      ∀ (a h : ℝ), |a| ≤ A → H ≤ h →
        regularVerticalAuxiliary F s ξ a h ≤ η := by
  obtain ⟨C, hC0, hbound⟩ :=
    regularVerticalAuxiliary_large_height_tail_bound F hc hs0 hs1 ξ hξ A
  have hka : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) := by
    have h := verticalReferenceErrorKernel_integrable 0
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, zero_add] using h
  have htend := integrable_symmetric_complement_tail_tendsto_zero hka
  intro η hη
  let D : ℝ := 2 * C + 1
  have hD : 0 < D := by dsimp [D]; linarith
  have hδ : 0 < η / D := div_pos hη hD
  have hev : ∀ᶠ n : ℕ in atTop,
      (∫ t in (Icc (-(n : ℝ)) (n : ℝ))ᶜ, (1 + t ^ 2)⁻¹) < η / D := by
    exact htend.eventually (eventually_lt_nhds hδ)
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨H, hH, hHbound⟩ := hbound (n : ℝ)
  refine ⟨H, hH, ?_⟩
  intro a h ha hh
  have hU := hHbound a h ha hh
  let tail : ℝ := ∫ t in (Icc (-(n : ℝ)) (n : ℝ))ᶜ, (1 + t ^ 2)⁻¹
  have htail0 : 0 ≤ tail := integral_nonneg (fun t => by positivity)
  have hDtail : D * tail ≤ D * (η / D) :=
    mul_le_mul_of_nonneg_left hn.le hD.le
  have hDid : D * (η / D) = η := by
    field_simp
  have hCtail : 2 * C * tail ≤ D * tail := by
    dsimp [D]
    nlinarith
  change regularVerticalAuxiliary F s ξ a h ≤ 2 * C * tail at hU
  linarith

end SpringerLean
