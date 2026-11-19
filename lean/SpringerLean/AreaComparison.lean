import SpringerLean.AreaLower

namespace SpringerLean

/-- The finite annulus area comparison with both bounds combined, in ordinary
real numbers. All correction constants are independent of the outer radius. -/
theorem exteriorArea_finite_comparison_real
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr : 1 < r) (N : ℕ) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ r < R₀ ∧
      ∀ R : ℝ, R₀ ≤ R →
        (1 - ‖exteriorForwardCoeff F 1 / (R : ℂ) ^ 2‖ ^ 2) *
          (R ^ 2 - r ^ 2 +
            ∑ j ∈ Finset.Icc 1 N,
              (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
                ((r⁻¹) ^ (2 * j) - (R⁻¹) ^ (2 * j))) ≤
          (R + C / R ^ 2) ^ 2 := by
  obtain ⟨C, R₁, hC, hrR₁, hupper⟩ :=
    exteriorAnnulus_image_area_corrected_upper F hc hr
  let B : ℝ := ‖exteriorForwardCoeff F 1‖
  let R₀ : ℝ := max R₁ (max 2 (B + 2))
  refine ⟨C, R₀, hC, ?_, ?_⟩
  · exact lt_of_lt_of_le hrR₁ (le_max_left _ _)
  intro R hR
  have hR₁ : R₁ ≤ R := le_trans (le_max_left _ _) hR
  have hRdet : max 2 (‖exteriorForwardCoeff F 1‖ + 2) ≤ R :=
    le_trans (le_max_right _ _) hR
  have hrR : r < R := lt_of_lt_of_le hrR₁ hR₁
  have hdpos : 0 < 1 - ‖exteriorForwardCoeff F 1 / (R : ℂ) ^ 2‖ ^ 2 := by
    simpa only [exteriorLinearCorrectionRealMap_det] using
      (exteriorLinearCorrectionRealMap_det_pos F hRdet)
  let d : ℝ := 1 - ‖exteriorForwardCoeff F 1 / (R : ℂ) ^ 2‖ ^ 2
  let E : ℝ := R ^ 2 - r ^ 2 +
    ∑ j ∈ Finset.Icc 1 N,
      (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
        ((r⁻¹) ^ (2 * j) - (R⁻¹) ^ (2 * j))
  let S : ℝ := R + C / R ^ 2
  have hlower : ENNReal.ofReal (Real.pi * E) ≤
      MeasureTheory.volume (F '' exteriorAnnulus r R) :=
    exteriorAnnulus_image_area_finite_lower F hc hr hrR N
  have hupperR := hupper R hR₁
  rw [abs_of_pos hdpos] at hupperR
  have hupperR' : ENNReal.ofReal d *
      MeasureTheory.volume (F '' exteriorAnnulus r R) ≤
      ENNReal.ofReal S ^ 2 * NNReal.pi := hupperR
  have hcombo : ENNReal.ofReal d * ENNReal.ofReal (Real.pi * E) ≤
      ENNReal.ofReal S ^ 2 * NNReal.pi :=
    le_trans (mul_le_mul_of_nonneg_left hlower bot_le) hupperR'
  have hπENN : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
    calc
      (NNReal.pi : ENNReal) = ENNReal.ofReal (NNReal.pi : ℝ) :=
        (ENNReal.ofReal_coe_nnreal).symm
      _ = ENNReal.ofReal Real.pi := congrArg ENNReal.ofReal NNReal.coe_real_pi
  have hSnonneg : 0 ≤ S := by
    have hRpos : 0 < R := lt_trans (by linarith : 0 < r) hrR
    dsimp [S]
    positivity
  rw [hπENN, ← ENNReal.ofReal_mul hdpos.le,
    ← ENNReal.ofReal_pow hSnonneg 2,
    ← ENNReal.ofReal_mul (sq_nonneg S)] at hcombo
  have hreal : d * (Real.pi * E) ≤ S ^ 2 * Real.pi :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg S) Real.pi_nonneg)).mp hcombo
  have hπpos : 0 < Real.pi := Real.pi_pos
  apply le_of_mul_le_mul_left (a := Real.pi) (by nlinarith [hreal]) hπpos

end SpringerLean
