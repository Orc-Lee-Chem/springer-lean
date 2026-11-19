import SpringerLean.Round12HullParameter
import Mathlib.Topology.Order.Compact
open scoped ComplexConjugate

namespace SpringerLean

theorem exteriorOmitted_convexHull_zero_mem
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (0 : ℂ) ∈ convexHull ℝ (exteriorOmitted F) := by
  have h := actualHarmonic_mem_convexHull_omitted F hc (z := 0) (by simp)
  simpa [actualHarmonic, exteriorForwardGerm] using h

/-- The first Section6 maximizer can already be chosen in the actual omitted set. -/
theorem exteriorOmitted_exists_radius_maximizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ P : ℂ, P ∈ exteriorOmitted F ∧
      ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P‖ := by
  obtain ⟨P, hP, hmax⟩ := (exteriorOmitted_isCompact F hc).exists_isMaxOn
    (exteriorOmitted_nonempty F hc) continuous_norm.continuousOn
  refine ⟨P, hP, ?_⟩
  have hsub : exteriorOmitted F ⊆ Metric.closedBall (0 : ℂ) ‖P‖ := by
    intro w hw
    simpa only [Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq] using hmax hw
  have hh := convexHull_min hsub (convex_closedBall (0 : ℂ) ‖P‖)
  intro w hw
  simpa only [Metric.mem_closedBall, dist_zero_right] using hh hw

/-- Compactness gives the opposite-half maximizer in the hull. Its membership
in K, and all numerical localization, remain separate geometric steps. -/
theorem exteriorOmitted_exists_half_radius_maximizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (ξ : ℂ) :
    ∃ P : ℂ, P ∈ convexHull ℝ (exteriorOmitted F) ∧
      Complex.re (conj ξ * P) ≤ 0 ∧
      ∀ w ∈ convexHull ℝ (exteriorOmitted F),
        Complex.re (conj ξ * w) ≤ 0 → ‖w‖ ≤ ‖P‖ := by
  let S := convexHull ℝ (exteriorOmitted F) ∩
    {w : ℂ | Complex.re (conj ξ * w) ≤ 0}
  have hclosed : IsClosed {w : ℂ | Complex.re (conj ξ * w) ≤ 0} :=
    isClosed_le (by fun_prop) continuous_const
  have hcompact : IsCompact S :=
    (complex_isCompact_convexHull (exteriorOmitted_isCompact F hc)).inter_right hclosed
  have hzero : (0 : ℂ) ∈ S :=
    ⟨exteriorOmitted_convexHull_zero_mem F hc, by simp⟩
  obtain ⟨P, hP, hmax⟩ := hcompact.exists_isMaxOn ⟨0, hzero⟩ continuous_norm.continuousOn
  exact ⟨P, hP.1, hP.2, fun w hw hneg => hmax ⟨hw, hneg⟩⟩

theorem exteriorOmitted_exists_ne_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ w ∈ exteriorOmitted F, w ≠ 0 := by
  by_contra h
  have hsub : exteriorOmitted F ⊆ ({0} : Set ℂ) := by
    intro w hw
    have he : w = 0 := by
      by_contra he
      exact h ⟨w, hw, he⟩
    simpa only [Set.mem_singleton_iff] using he
  have hHull : convexHull ℝ (exteriorOmitted F) ⊆ ({0} : Set ℂ) :=
    convexHull_min hsub (convex_singleton (0 : ℂ))
  have hnear : actualHarmonic F =ᶠ[nhds (0 : ℂ)] fun _ => 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    exact Set.mem_singleton_iff.mp (hHull (actualHarmonic_mem_convexHull_omitted F hc hz'))
  have hzero : HasFDerivAt (actualHarmonic F) (0 : ℂ →L[ℝ] ℂ) 0 :=
    (hasFDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hnear
  have hd := (actualHarmonic_hasFDerivAt_real F hc (z := 0) (by simp)).unique hzero
  have h1 := congrArg (fun T : ℂ →L[ℝ] ℂ => (T 1).re) hd
  have hi := congrArg (fun T : ℂ →L[ℝ] ℂ => (T Complex.I).im) hd
  simp at h1 hi
  linarith

theorem exteriorOmitted_exists_nonzero_radius_maximizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ P : ℂ, P ∈ exteriorOmitted F ∧ P ≠ 0 ∧
      ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P‖ := by
  obtain ⟨P, hP, hmax⟩ := exteriorOmitted_exists_radius_maximizer F hc
  obtain ⟨w, hw, hw0⟩ := exteriorOmitted_exists_ne_zero F hc
  have hP0 : P ≠ 0 := by
    intro he
    have hb := hmax w (subset_convexHull ℝ _ hw)
    rw [he, norm_zero] at hb
    exact (norm_pos_iff.mpr hw0).not_ge hb
  exact ⟨P, hP, hP0, hmax⟩

end SpringerLean
