import SpringerLean.Round11PolarArea

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean

/-- The real Jacobian of the actual exterior dilate is the square of its
complex derivative at every point in the paper's open exterior disk. -/
theorem rescaleExterior_realJacobian
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : z ∈ exteriorDisk) :
    (fderiv ℝ (rescaleExterior s F) z).det =
      ‖deriv (rescaleExterior s F) z‖ ^ 2 := by
  have hF : ∀ w ∈ exteriorDisk, AnalyticAt ℂ F w := by
    intro w hw
    exact hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hw)
  have hzabove : z ∈ exteriorAbove s := by
    change s < ‖z‖
    exact lt_trans hs1 hz
  have hcomplex : DifferentiableAt ℂ (rescaleExterior s F) z :=
    (rescaleExterior_analyticAt hs0 hF hzabove).differentiableAt
  rw [hcomplex.hasDerivAt.complexToReal_fderiv.fderiv,
    complex_mul_real_det, Complex.normSq_eq_norm_sq]

/-- The compact cutoff makes the full exterior integral equal to the
finite annulus integral, with the actual complex Jacobian substituted. -/
theorem regular_exterior_signed_cutoff_integral_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {R : ℝ} (hR : 1 < R)
    (φ : ℂ → ℝ)
    (hfar : ∀ z : ℂ, R ≤ ‖z‖ → φ (rescaleExterior s F z) = 0) :
    (∫ z in exteriorDisk,
      ‖deriv (rescaleExterior s F) z‖ ^ 2 *
        φ (rescaleExterior s F z) ∂volume) =
      ∫ z in exteriorAnnulus 1 R,
        φ (rescaleExterior s F z) *
          (fderiv ℝ (rescaleExterior s F) z).det ∂volume := by
  let G := rescaleExterior s F
  have hsubset : exteriorAnnulus 1 R ⊆ exteriorDisk := by
    intro z hz
    exact hz.1
  have heq :
      (∫ z in exteriorDisk, ‖deriv G z‖ ^ 2 * φ (G z) ∂volume) =
      ∫ z in exteriorAnnulus 1 R,
        ‖deriv G z‖ ^ 2 * φ (G z) ∂volume := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      exteriorDisk_isOpen.measurableSet hsubset
    intro z hz
    have hzR : R ≤ ‖z‖ := by
      have hn : ¬ (1 < ‖z‖ ∧ ‖z‖ < R) := hz.2
      exact le_of_not_gt (fun hlt => hn ⟨hz.1, hlt⟩)
    simp [G, hfar z hzR]
  rw [heq]
  apply setIntegral_congr_fun (exteriorAnnulus_isOpen 1 R).measurableSet
  intro z hz
  have hzE : z ∈ exteriorDisk := hz.1
  dsimp only [G]
  rw [rescaleExterior_realJacobian F hc hs0 hs1 hzE]
  ring

/-- The signed Green partition for the actual regularized harmonic filling,
the genuine exterior map, and the smooth even-weight cutoff. No area or
boundary conclusion is assumed in the original function class. -/
theorem regular_signedPartition_actual
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    regularSignedPartitionTarget F s T hT k := by
  obtain ⟨R, hR, hφfar, hGfar, houter⟩ :=
    regular_greenBoundary_outer_eq F hc hs0 hs1 T hT k
  let φ : ℂ → ℝ := evenWeightCutoff T hT k
  have hφ : ContDiff ℝ 1 φ := evenWeightCutoff_contDiff T hT k
  have hcompact : HasCompactSupport φ :=
    evenWeightCutoff_hasCompactSupport T hT k
  have hD := regular_green_disk_area F hc hs0 hs1 φ hφ hcompact
  have hA := regular_green_annulus_area F hc hs0 hs1 hR φ hφ hcompact
  have hE := regular_exterior_signed_cutoff_integral_eq
    F hc hs0 hs1 hR φ hGfar
  have hS := green_standard_disk_area φ hφ hcompact R
    (lt_trans (by norm_num : (0 : ℝ) < 1) hR)
  have hfull :
      (∫ z in Metric.ball (0 : ℂ) R, φ z ∂volume) =
        ∫ z : ℂ, φ z ∂volume := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    apply hφfar z
    exact le_of_not_gt (by
      intro hlt
      apply hz
      simpa only [Metric.mem_ball, dist_zero_right] using hlt)
  have hunit := regular_greenBoundary_unit_eq F hs0 φ
  change (∫ z in Metric.ball (0 : ℂ) 1,
        φ (regularHarmonic s F z) *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) +
      (∫ z in exteriorDisk,
        ‖deriv (rescaleExterior s F) z‖ ^ 2 *
          φ (rescaleExterior s F z) ∂volume) =
      ∫ w : ℂ, φ w ∂volume
  linarith

/-- Unconditional regularized weighted omitted-area identity, including
the constant-weight case `k=1` and the actual omitted set of `F_s`. -/
theorem regularWeightedOmittedAreaTarget_proved
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {k : ℕ} (hk : 1 ≤ k) :
    regularWeightedOmittedAreaTarget F s k := by
  exact regularWeightedOmittedAreaTarget_of_signedPartition
    F hc hs0 hs1 hk
    (fun T hT => regular_signedPartition_actual F hc hs0 hs1 T hT k)

/-- Expanded, audit-ready form of the unconditional regularized second
identity. The right side is the genuine omitted set of `rescaleExterior s F`. -/
theorem regularWeightedOmittedArea_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {k : ℕ} (hk : 1 ≤ k) :
    (Real.pi : ℝ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖regularHarmonic s F z‖ ^ (2 * k - 2) *
          (1 - ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2)
          ∂volume) =
    (Real.pi : ℝ)⁻¹ *
      (∫ w in exteriorOmitted (rescaleExterior s F),
        ‖w‖ ^ (2 * k - 2) ∂volume) :=
  regularWeightedOmittedAreaTarget_proved F hc hs0 hs1 hk

/-- Constant-weight `k=1` check, including the normalization by `π`. -/
theorem regularOmittedArea_k_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (Real.pi : ℝ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        (1 - ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2)
          ∂volume) =
    (Real.pi : ℝ)⁻¹ *
      (∫ w in exteriorOmitted (rescaleExterior s F),
        (1 : ℝ) ∂volume) := by
  simpa using (regularWeightedOmittedArea_eq F hc hs0 hs1
    (k := 1) (by norm_num))

end SpringerLean
