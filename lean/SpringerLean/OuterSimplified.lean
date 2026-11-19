import SpringerLean.CircleLower

namespace SpringerLean

/-- The outer-circle correction has a fixed second-order error constant,
independent of the circle radius. -/
theorem exteriorLinearCorrection_large_circle_fixed_C
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ 1 ≤ R₀ ∧
      ∀ (R : ℝ) (z : ℂ), R₀ ≤ R → ‖z‖ = R →
        ‖exteriorLinearCorrection F R (F z)‖ ≤ R + C / R ^ 2 := by
  obtain ⟨δ, hδ, houter⟩ :=
    exteriorLinearCorrection_large_circle_norm_bound F hc
  let B : ℝ := ‖exteriorForwardCoeff F 1‖
  let T : ℝ := ‖exteriorSecondTail F 0‖ + 1
  let C : ℝ := T + B * (B + T)
  let R₀ : ℝ := max 1 (2 / δ)
  refine ⟨C, R₀, ?_, le_max_left _ _, ?_⟩
  · dsimp [C, B, T]
    positivity
  intro R z hR hz
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := by linarith
  have hRbig : 2 / δ ≤ R := le_trans (le_max_right _ _) hR
  have hRinv : R⁻¹ < δ := by
    have hδ2 : 0 < δ / 2 := by positivity
    have hRbound : 1 / R ≤ δ / 2 := by
      apply (div_le_iff₀ hRpos).mpr
      have : 2 ≤ δ * R := by
        apply (div_le_iff₀ hδ).mp at hRbig
        nlinarith
      nlinarith
    rw [inv_eq_one_div]
    linarith
  have h := houter R z hRpos hz hRinv
  have hB : 0 ≤ B := norm_nonneg _
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hR2 : 0 < R ^ 2 := by positivity
  have hR2one : 1 ≤ R ^ 2 := by nlinarith
  have hBdiv : B / R ≤ B :=
    (div_le_iff₀ hRpos).mpr (by simpa using mul_le_mul_of_nonneg_left hR1 hB)
  have hTdiv : T / R ^ 2 ≤ T :=
    (div_le_iff₀ hR2).mpr (by simpa using mul_le_mul_of_nonneg_left hR2one hT)
  have hinner : B / R + T / R ^ 2 ≤ B + T := add_le_add hBdiv hTdiv
  have hmul : (B / R ^ 2) * (B / R + T / R ^ 2) ≤
      (B / R ^ 2) * (B + T) :=
    mul_le_mul_of_nonneg_left hinner (div_nonneg hB hR2.le)
  have hcombine :
      T / R ^ 2 + (B / R ^ 2) * (B + T) = C / R ^ 2 := by
    dsimp [C]
    field_simp
  calc
    ‖exteriorLinearCorrection F R (F z)‖ ≤
        R + T / R ^ 2 +
          (B / R ^ 2) * (B / R + T / R ^ 2) := h
    _ ≤ R + T / R ^ 2 + (B / R ^ 2) * (B + T) := by linarith
    _ = R + C / R ^ 2 := by rw [add_assoc, hcombine]

end SpringerLean
