import SpringerLean.Round09Rectangle

namespace SpringerLean

/-- Uniform displacement of a regular dilate from the identity throughout
the actual exterior disk. This controls the outer boundary of the Stokes
comparison without any boundary hypothesis on the original map. -/
theorem rescaleExterior_sub_id_bounded
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ exteriorDisk, ‖rescaleExterior s F z - z‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exteriorForwardGerm_bounded_unitDisk F hc
  refine ⟨C, hC0, ?_⟩
  intro z hz
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := by
    intro hzero
    simp [hzero] at hz1
    norm_num at hz1
  have hu : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz1
  have hsu : ‖(s : ℂ) * z⁻¹‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    nlinarith [mul_nonneg hs0.le (norm_nonneg z⁻¹)]
  have heq : rescaleExterior s F z - z =
      (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * z⁻¹) := by
    have hp := exteriorForwardGerm_punctured
      (rescaleExterior s F) (inv_ne_zero hz0)
    rw [inv_inv] at hp
    rw [rescaleExterior_forwardGerm s hs0 F z⁻¹] at hp
    exact hp.symm
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs0]
  calc
    s * ‖exteriorForwardGerm F ((s : ℂ) * z⁻¹)‖ ≤ s * C :=
      mul_le_mul_of_nonneg_left (hC _ hsu) hs0.le
    _ ≤ C := by nlinarith

/-- A compactly supported weight vanishes on the far exterior image once
its support radius is smaller than the source radius minus the displacement
bound. -/
theorem rescaleExterior_compact_weight_vanish_far
    (F : ℂ → ℂ) {s : ℝ}
    {C T R : ℝ}
    (hC : ∀ z ∈ exteriorDisk, ‖rescaleExterior s F z - z‖ ≤ C)
    (hR : T + C ≤ R)
    (φ : ℂ → ℝ) (hφ : ∀ w : ℂ, T ≤ ‖w‖ → φ w = 0)
    {z : ℂ} (hz : R ≤ ‖z‖) (hR1 : 1 < R) :
    φ (rescaleExterior s F z) = 0 := by
  have hzE : z ∈ exteriorDisk := lt_of_lt_of_le hR1 hz
  have hdist := hC z hzE
  apply hφ
  have htri : ‖z‖ ≤ ‖rescaleExterior s F z‖ +
      ‖rescaleExterior s F z - z‖ := by
    calc
      ‖z‖ = ‖rescaleExterior s F z -
          (rescaleExterior s F z - z)‖ := by congr 1; abel
      _ ≤ ‖rescaleExterior s F z‖ +
          ‖rescaleExterior s F z - z‖ := norm_sub_le _ _
  linarith

/-- Every point of the straight-line homotopy from a sufficiently large
standard circle to its genuine image remains outside the support of the
cutoff weight. The primitive itself need not vanish there. -/
theorem rescaleExterior_outer_homotopy_weight_vanish
    (F : ℂ → ℂ) {s : ℝ}
    {C T R : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ exteriorDisk, ‖rescaleExterior s F z - z‖ ≤ C)
    (hR : T + C ≤ R)
    (φ : ℂ → ℝ) (hφ : ∀ w : ℂ, T ≤ ‖w‖ → φ w = 0)
    {z : ℂ} (hz : R ≤ ‖z‖) (hR1 : 1 < R)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    φ (z + (t : ℂ) * (rescaleExterior s F z - z)) = 0 := by
  have hzE : z ∈ exteriorDisk := lt_of_lt_of_le hR1 hz
  have hdist := hC z hzE
  have htnorm : ‖(t : ℂ) * (rescaleExterior s F z - z)‖ ≤ C := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc
      t * ‖rescaleExterior s F z - z‖ ≤ t * C :=
        mul_le_mul_of_nonneg_left hdist ht0
      _ ≤ C := by nlinarith
  apply hφ
  have htri : ‖z‖ ≤
      ‖z + (t : ℂ) * (rescaleExterior s F z - z)‖ +
        ‖(t : ℂ) * (rescaleExterior s F z - z)‖ := by
    have h := norm_sub_le
      (z + (t : ℂ) * (rescaleExterior s F z - z))
      ((t : ℂ) * (rescaleExterior s F z - z))
    simpa only [add_sub_cancel_right] using h
  linarith

end SpringerLean
