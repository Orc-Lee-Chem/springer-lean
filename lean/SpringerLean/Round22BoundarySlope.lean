import SpringerLean.Round22PotentialNear

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal ComplexConjugate

namespace SpringerLean

set_option maxHeartbeats 800000

/-- A continuous function vanishing at the center has a one-sided
`η h` bound for its integral over sufficiently short symmetric intervals,
provided the actual local integrals exist. -/
theorem symmetric_setIntegral_le_linear_of_continuousAt
    (f : ℝ → ℝ) (t₀ : ℝ)
    (hcont : ContinuousAt f t₀) (hzero : f t₀ = 0)
    (hint : ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 ≤ h → h < δ →
      IntegrableOn f (Icc (t₀ - h) (t₀ + h))) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ,
      0 < h → h < δ →
        (∫ t in Icc (t₀ - h) (t₀ + h), f t) ≤ η * h := by
  intro η hη
  obtain ⟨δ₁, hδ₁, hint⟩ := hint
  have hη2 : 0 < η / 2 := by linarith
  have hevent : ∀ᶠ t in 𝓝 t₀, f t < η / 2 := by
    exact hcont.eventually
      (show ∀ᶠ y in 𝓝 (f t₀), y < η / 2 from
        Iio_mem_nhds (by simpa [hzero] using hη2))
  obtain ⟨δ₂, hδ₂, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro h hh hhδ
  have hh₁ : h < δ₁ := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hh₂ : h < δ₂ := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hInt : IntegrableOn f (Icc (t₀ - h) (t₀ + h)) :=
    hint h (le_of_lt hh) hh₁
  have hbound : ∀ t ∈ Icc (t₀ - h) (t₀ + h), f t ≤ η / 2 := by
    intro t ht
    have htball : t ∈ Metric.ball t₀ δ₂ := by
      change dist t t₀ < δ₂
      rw [Real.dist_eq]
      have habs : |t - t₀| ≤ h := abs_le.mpr (by constructor <;> linarith [ht.1, ht.2])
      exact lt_of_le_of_lt habs hh₂
    exact le_of_lt (hball htball)
  have hle : (∫ t in Icc (t₀ - h) (t₀ + h), f t) ≤
      ∫ _t in Icc (t₀ - h) (t₀ + h), η / 2 := by
    apply integral_mono_ae hInt (integrable_const _)
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hbound)
  calc
    (∫ t in Icc (t₀ - h) (t₀ + h), f t) ≤
        ∫ _t in Icc (t₀ - h) (t₀ + h), η / 2 := hle
    _ = η * h := by
      rw [integral_const, Measure.real_def, Measure.restrict_apply_univ, Real.volume_Icc]
      have hnonneg : 0 ≤ (t₀ + h) - (t₀ - h) := by linarith
      rw [ENNReal.toReal_ofReal hnonneg]
      simp only [smul_eq_mul]
      ring

/-- At every positive actual vertical potential difference, the boundary
value of the BLP auxiliary function has arbitrarily small downward slope
into the upper half-plane. This is unconditional for the paper's actual
regularized exterior map. -/
theorem regularVerticalAuxiliary_boundary_slope_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a : ℝ)
    (hpos : 0 < (∫ t : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a t)) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ,
      0 < h → h < δ →
        regularVerticalAuxiliary F s ξ a 0 -
          regularVerticalAuxiliary F s ξ a h ≤ η * h := by
  intro η hη
  obtain ⟨v, hv, hvre⟩ :=
    regularExterior_projection_exists_eq_of_vertical_integral_pos
      F hc hs0 hs1 ξ a hpos
  let W : ℂ := conj ξ * rescaleExterior s F v
  have hvnorm : ‖v‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using hv
  have hpoint : ((a : ℂ) + (W.im : ℂ) * Complex.I) = W := by
    change W.re = a at hvre
    rw [← hvre]
    exact Complex.re_add_im W
  let f : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  have hzero : f W.im = 0 := by
    dsimp [f]
    rw [hpoint, regularExterior_rotated_potential_eq F s ξ hξ]
    have hunit : ξ * conj ξ = 1 := by
      rw [RCLike.mul_conj, hξ]
      norm_num
    rw [show ξ * W = rescaleExterior s F v from by
      dsimp [W]
      rw [← mul_assoc, hunit, one_mul]]
    exact regularExterior_curve_boundary_log_potential_zero F hc hs0 hs1 hvnorm
  have hcont : ContinuousAt f W.im := by
    have hcurve : ContinuousAt (regularExteriorRotatedPotential F s ξ) W :=
      regularExterior_rotated_potential_continuousAt_curve F hc hs0 hs1 ξ hξ hvnorm
    have hline : ContinuousAt
        (fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I) W.im := by fun_prop
    exact hcurve.comp_of_eq hline hpoint
  have hint : ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 ≤ h → h < δ →
      IntegrableOn f (Icc (W.im - h) (W.im + h)) := by
    have h := regularExterior_rotated_potential_integrable_near_curve
      F hc hs0 hs1 ξ hξ hvnorm
    simpa only [← hvre, f, W] using h
  obtain ⟨δ, hδ, hbound⟩ :=
    symmetric_setIntegral_le_linear_of_continuousAt f W.im hcont hzero hint η hη
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhδ
  have haux := regularVerticalAuxiliary_boundary_difference_le
    F hc hs0 hs1 ξ hξ a h W.im hh
  have hcomp : 0 ≤
      ∫ t in Icc (-h) h,
        comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I) := by
    apply integral_nonneg
    intro t
    exact comparisonCircle_boundary_log_potential_nonneg _
  have hsmall :
      (∫ t in Icc (W.im - h) (W.im + h), f t) ≤ η * h :=
    hbound h hh hhδ
  dsimp [f] at hsmall
  linarith

end SpringerLean
