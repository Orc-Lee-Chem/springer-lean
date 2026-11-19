import SpringerLean.Round18Tail

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual rotated boundary projection is continuous on the unit
circle, with no assumed boundary extension of the original exterior map. -/
theorem regularExterior_projection_continuousOn_sphere
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ) :
    ContinuousOn (fun ζ : ℂ => (conj ξ * rescaleExterior s F ζ).re)
      (sphere (0 : ℂ) 1) := by
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : ContinuousOn (rescaleExterior s F) (sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hζ
    have hext : ζ ∈ exteriorAbove s := by
      change s < ‖ζ‖
      rw [hnorm]
      exact hs1
    exact (rescaleExterior_analyticAt hs0 hF hext).continuousAt.continuousWithinAt
  exact Complex.continuous_re.continuousOn.comp
    (continuousOn_const.mul hG) (subset_preimage_image _ _)

/-- The actual rotated regularized boundary projection has a finite
absolute range bound, derived from local analyticity and circle compactness. -/
theorem regularExterior_projection_exists_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ sphere (0 : ℂ) 1,
      |(conj ξ * rescaleExterior s F ζ).re| ≤ M := by
  let X : ℂ → ℝ := fun ζ => (conj ξ * rescaleExterior s F ζ).re
  have hX : ContinuousOn X (sphere (0 : ℂ) 1) :=
    regularExterior_projection_continuousOn_sphere F hc hs0 hs1 ξ
  have hb : Bornology.IsBounded (X '' sphere (0 : ℂ) 1) :=
    ((isCompact_sphere (0 : ℂ) 1).image_of_continuousOn hX).isBounded
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro ζ hζ
  have h := hM (X ζ) ⟨ζ, hζ, rfl⟩
  have h' : |X ζ| ≤ M := by simpa only [Real.norm_eq_abs] using h
  exact h'.trans (le_max_left _ _)

/-- For every actual regularized map, its vertical potential difference
has compact support as a function of the real threshold. -/
theorem regularExteriorVerticalPotentialDifference_integral_eventually_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ a : ℝ, R ≤ |a| →
      (∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) = 0 := by
  obtain ⟨M, hM0, hM⟩ := regularExterior_projection_exists_bound F hc hs0 hs1 ξ
  refine ⟨M + 2, by linarith, ?_⟩
  intro a ha
  have hY (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1) : |2 * ζ.re| ≤ 2 := by
    have hnorm : ‖ζ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hζ
    have hr := Complex.abs_re_le_norm ζ
    rw [hnorm] at hr
    calc
      |2 * ζ.re| = 2 * |ζ.re| := by simp
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = 2 := by ring
  rcases le_total 0 a with hapos | haneg
  · have haa : M + 2 ≤ a := by rwa [abs_of_nonneg hapos] at ha
    apply regularExteriorVerticalPotentialDifference_integral_zero_of_upper
      F hc hs0 hs1 ξ a
    · intro ζ hζ
      have h := hM ζ hζ
      linarith [le_abs_self ((conj ξ * rescaleExterior s F ζ).re)]
    · intro ζ hζ
      have h := hY ζ hζ
      linarith [le_abs_self (2 * ζ.re)]
  · have haa : M + 2 ≤ -a := by rwa [abs_of_nonpos haneg] at ha
    apply regularExteriorVerticalPotentialDifference_integral_zero_of_lower
      F hc hs0 hs1 ξ a
    · intro ζ hζ
      have h := hM ζ hζ
      linarith [neg_le_of_abs_le h]
    · intro ζ hζ
      have h := hY ζ hζ
      linarith [neg_le_of_abs_le h]

end SpringerLean
