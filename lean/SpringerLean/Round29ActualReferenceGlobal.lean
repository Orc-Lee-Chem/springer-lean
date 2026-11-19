import SpringerLean.Round29ComparisonGlobalBound

namespace SpringerLean

/-- Both actual regularized and comparison logarithmic potentials have a
single global reciprocal-quadratic error from the common radial reference. -/
theorem regularExterior_potentials_reference_global_quadratic
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      |regularExteriorRotatedPotential F s ξ z - radialReferencePotential z| +
        |comparisonSegmentPotential z - radialReferencePotential z| ≤
          C / (1 + ‖z‖ ^ 2) := by
  obtain ⟨R₀, Cfar, hR₀0, hCfar0, hfar⟩ :=
    regularExterior_potentials_reference_far_quadratic F hc hs0 hs1 ξ hξ
  obtain ⟨Cg, hCg0, hCg⟩ :=
    regularExterior_boundary_potential_linear_bound F hc hs0 hs1
  let R : ℝ := max R₀ 1
  have hR0 : 0 ≤ R := le_trans hR₀0 (le_max_left _ _)
  have hR1 : 1 ≤ R := le_max_right _ _
  let B : ℝ := 2 * R + Cg + 4 + R ^ 2
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  let C : ℝ := max (2 * Cfar) (B * (1 + R ^ 2))
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, ?_⟩
  intro z
  let g : ℝ := regularExteriorRotatedPotential F s ξ z
  let G : ℝ := comparisonSegmentPotential z
  let k : ℝ := radialReferencePotential z
  have hg0 : 0 ≤ g := regularExterior_rotated_boundary_potential_nonneg
    F hc hs0 hs1 ξ hξ z
  have hG0 : 0 ≤ G := comparisonCircle_boundary_log_potential_nonneg z
  have hk0 : 0 ≤ k := by
    dsimp [k, radialReferencePotential]
    apply mul_nonneg (by norm_num)
    exact Real.log_nonneg (by nlinarith [sq_nonneg ‖z‖])
  have hkBound : k ≤ (1 / 2 : ℝ) * (1 + ‖z‖ ^ 2) := by
    dsimp [k, radialReferencePotential]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_self (by positivity)) (by norm_num)
  have hgBound : g ≤ ‖z‖ + Cg + 1 := by
    have h := hCg (ξ * z)
    rw [← regularExterior_rotated_potential_eq F s ξ hξ z,
      norm_mul, hξ, one_mul] at h
    exact h
  have hGBound : G ≤ ‖z‖ + 2 := comparisonSegmentPotential_le_norm_add_two z
  have hAbsG : |g-k| ≤ g+k := by
    simpa only [sub_eq_add_neg, abs_neg, abs_of_nonneg hg0, abs_of_nonneg hk0]
      using abs_add_le g (-k)
  have hAbsComp : |G-k| ≤ G+k := by
    simpa only [sub_eq_add_neg, abs_neg, abs_of_nonneg hG0, abs_of_nonneg hk0]
      using abs_add_le G (-k)
  by_cases hzR : ‖z‖ ≤ R
  · have hzsq : ‖z‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR0).2 hzR
    have hnear : |g-k| + |G-k| ≤ B := by
      dsimp [B]
      linarith
    have hden : 0 < 1 + ‖z‖ ^ 2 := by positivity
    have hCnear : B * (1 + R ^ 2) ≤ C := le_max_right _ _
    apply (le_div_iff₀ hden).2
    have hprod := mul_le_mul_of_nonneg_left hzsq hB0
    nlinarith
  · have hzR' : R < ‖z‖ := lt_of_not_ge hzR
    have hzR₀ : R₀ < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hzR'
    have hfar' := hfar z hzR₀
    have hzsq : 1 ≤ ‖z‖ ^ 2 := by nlinarith
    have hden : 0 < 1 + ‖z‖ ^ 2 := by positivity
    have hsqpos : 0 < ‖z‖ ^ 2 := by nlinarith
    have hdiv : Cfar / ‖z‖ ^ 2 ≤ (2 * Cfar) / (1 + ‖z‖ ^ 2) := by
      apply (div_le_div_iff₀ hsqpos hden).2
      have hprod : 0 ≤ Cfar * (‖z‖ ^ 2 - 1) :=
        mul_nonneg hCfar0 (by linarith)
      nlinarith
    have hCfar : 2 * Cfar ≤ C := le_max_left _ _
    have hlast := div_le_div_of_nonneg_right hCfar hden.le
    exact hfar'.trans (hdiv.trans hlast)
end SpringerLean