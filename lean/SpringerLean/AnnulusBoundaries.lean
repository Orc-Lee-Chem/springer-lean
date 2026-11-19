import SpringerLean.RadialLower

namespace SpringerLean

/-- Both boundary circles of a sufficiently large annulus satisfy one
corrected-image bound with a single constant independent of `R`. -/
theorem exteriorLinearCorrection_annulus_boundaries
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr : 1 < r) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ 1 ≤ R₀ ∧
      ∀ (R : ℝ) (z : ℂ), R₀ ≤ R →
        (‖z‖ = r ∨ ‖z‖ = R) →
          ‖exteriorLinearCorrection F R (F z)‖ ≤ R + C / R ^ 2 := by
  obtain ⟨C, Rout, hC, hRout, houter⟩ :=
    exteriorLinearCorrection_large_circle_fixed_C F hc
  have hsphere : IsCompact (Metric.sphere (0 : ℂ) r) := isCompact_sphere _ _
  have hsphere_ext : Metric.sphere (0 : ℂ) r ⊆ exteriorDisk := by
    intro z hz
    change dist z 0 = r at hz
    rw [dist_zero_right] at hz
    change 1 < ‖z‖
    rw [hz]
    exact hr
  have hFcont : ContinuousOn F (Metric.sphere (0 : ℂ) r) :=
    hc.1.continuousOn.mono hsphere_ext
  obtain ⟨M, hM⟩ :=
    (hsphere.image_of_continuousOn hFcont).isBounded.exists_norm_le
  have hrpos : 0 < r := by linarith
  have hMnonneg : 0 ≤ M := by
    have hrpoint : (r : ℂ) ∈ Metric.sphere (0 : ℂ) r := by
      change dist (r : ℂ) 0 = r
      simp [dist_zero_right, Complex.norm_real, abs_of_pos hrpos]
    have := hM (F (r : ℂ)) (Set.mem_image_of_mem F hrpoint)
    linarith [norm_nonneg (F (r : ℂ))]
  let B : ℝ := ‖exteriorForwardCoeff F 1‖
  let R₀ : ℝ := max Rout (max 1 (M * (1 + B)))
  refine ⟨C, R₀, hC, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  intro R z hR hz
  rcases hz with hinner | houterz
  · have hR1 : 1 ≤ R :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hR)
    have hRpos : 0 < R := by linarith
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    have hR2pos : 0 < R ^ 2 := by positivity
    have hF : ‖F z‖ ≤ M := by
      apply hM _ (Set.mem_image_of_mem F ?_)
      change dist z 0 = r
      simpa only [dist_zero_right] using hinner
    have hB : 0 ≤ B := norm_nonneg _
    have hBdiv : B / R ^ 2 ≤ B :=
      (div_le_iff₀ hR2pos).mpr
        (by simpa using mul_le_mul_of_nonneg_left hR2 hB)
    have hlin : ‖exteriorLinearCorrection F R (F z)‖ ≤
        ‖F z‖ + (B / R ^ 2) * ‖F z‖ := by
      unfold exteriorLinearCorrection
      calc
        ‖F z - (exteriorForwardCoeff F 1 / (R : ℂ) ^ 2) * star (F z)‖ ≤
            ‖F z‖ + ‖(exteriorForwardCoeff F 1 / (R : ℂ) ^ 2) * star (F z)‖ :=
              norm_sub_le _ _
        _ = _ := by
          rw [norm_mul, norm_div, norm_pow, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hRpos, norm_star]
    have hMbound : M * (1 + B) ≤ R :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hR)
    have hlinR : ‖exteriorLinearCorrection F R (F z)‖ ≤ R := by
      have hnonneg : 0 ≤ B / R ^ 2 := div_nonneg hB hR2pos.le
      nlinarith [mul_le_mul_of_nonneg_left hF hnonneg,
        mul_le_mul_of_nonneg_right hBdiv hMnonneg]
    exact le_trans hlinR (by have : 0 ≤ C / R ^ 2 := div_nonneg hC hR2pos.le; linarith)
  · exact houter R z (le_trans (le_max_left _ _) hR) houterz

end SpringerLean
