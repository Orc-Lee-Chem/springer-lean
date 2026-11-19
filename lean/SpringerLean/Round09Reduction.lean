import SpringerLean.Round09Cutoff

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean

/-- The one remaining signed Green/Stokes partition formula for the actual
regularized map and the explicit smooth compact cutoff. This is a target
specification, not an assumption of the paper's function class. -/
def regularSignedPartitionTarget
    (F : ℂ → ℂ) (s T : ℝ) (hT : 0 ≤ T) (k : ℕ) : Prop :=
  (∫ z in Metric.ball (0 : ℂ) 1,
    evenWeightCutoff T hT k (regularHarmonic s F z) *
      (fderiv ℝ (regularHarmonic s F) z).det ∂volume) +
  (∫ z in exteriorDisk,
    ‖deriv (rescaleExterior s F) z‖ ^ 2 *
      evenWeightCutoff T hT k (rescaleExterior s F z) ∂volume) =
  ∫ w : ℂ, evenWeightCutoff T hT k w ∂volume

/-- Once the signed boundary comparison is supplied as a separately
identified mathematical lemma, all cutoff restoration, actual image change
of variables, and normalization steps yield the exact regularized second
identity. This conditional bridge is not the final lemma 3.1 result. -/
theorem regularWeightedOmittedAreaTarget_of_signedPartition
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {k : ℕ} (hk : 1 ≤ k)
    (hpartition : ∀ (T : ℝ) (hT : 0 ≤ T),
      regularSignedPartitionTarget F s T hT k) :
    regularWeightedOmittedAreaTarget F s k := by
  obtain ⟨T, hT, hH, hK⟩ := regular_evenWeightCutoff_exists F hc hs0 hs1 hk
  let G : ℂ → ℂ := rescaleExterior s F
  let φ : ℂ → ℝ := evenWeightCutoff T hT k
  have hcG : CenteredExteriorUnivalent G :=
    rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have himage : MeasurableSet (G '' exteriorDisk) := by
    simpa only [exteriorOmitted, compl_compl] using
      (exteriorOmitted_measurableSet G hcG).compl
  have hKmeas : MeasurableSet (exteriorOmitted G) :=
    exteriorOmitted_measurableSet G hcG
  have hφint : Integrable φ volume :=
    (evenWeightCutoff_contDiff T hT k).continuous.integrable_of_hasCompactSupport
      (evenWeightCutoff_hasCompactSupport T hT k)
  have hdecomp := integral_add_compl himage hφint
  have hchange := (regular_evenWeightCutoff_exteriorImage_change
    F hc hs0 hs1 T hT k).2
  have hpart := hpartition T hT
  dsimp only [regularSignedPartitionTarget] at hpart
  rw [← hchange] at hpart
  have hdecomp' :
      (∫ w in G '' exteriorDisk, φ w ∂volume) +
        (∫ w in exteriorOmitted G, φ w ∂volume) =
          ∫ w : ℂ, φ w ∂volume := by
    simpa only [exteriorOmitted] using hdecomp
  have hsame :
      (∫ z in Metric.ball (0 : ℂ) 1,
        φ (regularHarmonic s F z) *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) =
      ∫ w in exteriorOmitted G, φ w ∂volume := by
    dsimp only [G, φ] at hdecomp' ⊢
    linarith [hpart, hdecomp']
  have hdiskeq :
      (∫ z in Metric.ball (0 : ℂ) 1,
        φ (regularHarmonic s F z) *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) =
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖regularHarmonic s F z‖ ^ (2 * k - 2) *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro z hz
    change evenWeightCutoff T hT k (regularHarmonic s F z) * _ = _ * _
    rw [hH z (Metric.ball_subset_closedBall hz)]
  have hKweight :
      (∫ w in exteriorOmitted G, φ w ∂volume) =
        ∫ w in exteriorOmitted G, ‖w‖ ^ (2 * k - 2) ∂volume := by
    apply setIntegral_congr_fun hKmeas
    intro w hw
    exact hK w hw
  have hraw :
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖regularHarmonic s F z‖ ^ (2 * k - 2) *
          (1 - ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2)
        ∂volume) =
      ∫ w in exteriorOmitted G, ‖w‖ ^ (2 * k - 2) ∂volume := by
    calc
      _ = (∫ z in Metric.ball (0 : ℂ) 1,
            ‖regularHarmonic s F z‖ ^ (2 * k - 2) *
              (fderiv ℝ (regularHarmonic s F) z).det ∂volume) :=
          (regularHarmonic_weighted_signedJacobian_integral
            F hc hs0 hs1 (2 * k - 2)).symm
      _ = ∫ z in Metric.ball (0 : ℂ) 1,
            φ (regularHarmonic s F z) *
              (fderiv ℝ (regularHarmonic s F) z).det ∂volume := hdiskeq.symm
      _ = ∫ w in exteriorOmitted G, φ w ∂volume := hsame
      _ = _ := hKweight
  change (Real.pi : ℝ)⁻¹ * _ = (Real.pi : ℝ)⁻¹ * _
  exact congrArg (fun x : ℝ => (Real.pi : ℝ)⁻¹ * x) hraw

end SpringerLean
