import SpringerLean.Round08Jacobian
import Mathlib.MeasureTheory.Function.Jacobian

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean

/-- Exact Round 09 target for the regularized second identity in Lemma 3.1.
This is a specification, not a theorem or an assumption in any proved result. -/
def regularWeightedOmittedAreaTarget (F : ℂ → ℂ) (s : ℝ) (k : ℕ) : Prop :=
  (Real.pi : ℝ)⁻¹ *
    (∫ z in Metric.ball (0 : ℂ) 1,
      ‖regularHarmonic s F z‖ ^ (2 * k - 2) *
        (1 - ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2) ∂volume) =
  (Real.pi : ℝ)⁻¹ *
    (∫ w in exteriorOmitted (rescaleExterior s F),
      ‖w‖ ^ (2 * k - 2) ∂volume)

/-- Weighted change of variables for an integrable weight on the actual
exterior image. The Jacobian is `‖G'‖²`. The integrability premise prevents
the ordinary integral of an unbounded polynomial weight from silently
defaulting to zero on the unbounded exterior image. -/
theorem exteriorImage_integrable_weight_change
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (φ : ℂ → ℝ) (hφ : IntegrableOn φ (G '' exteriorDisk)) :
    IntegrableOn (fun z => ‖deriv G z‖ ^ 2 * φ (G z)) exteriorDisk ∧
      (∫ w in G '' exteriorDisk, φ w ∂volume) =
        ∫ z in exteriorDisk, ‖deriv G z‖ ^ 2 * φ (G z) ∂volume := by
  have hderiv : ∀ z ∈ exteriorDisk,
      HasFDerivWithinAt G ((deriv G z) • (1 : ℂ →L[ℝ] ℂ)) exteriorDisk z := by
    intro z hz
    have hdiff : DifferentiableAt ℂ G z :=
      hc.1.differentiableAt (exteriorDisk_isOpen.mem_nhds hz)
    exact hdiff.hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt
  have hint := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (μ := volume) exteriorDisk_isOpen.measurableSet hderiv hc.2.1 φ).mp hφ
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume) exteriorDisk_isOpen.measurableSet hderiv hc.2.1
    φ
  have hfun : (fun z => |((deriv G z) • (1 : ℂ →L[ℝ] ℂ)).det| • φ (G z)) =
      (fun z => ‖deriv G z‖ ^ 2 * φ (G z)) := by
    funext z
    rw [complex_mul_real_det, abs_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq]
    simp only [smul_eq_mul]
  rw [hfun] at hint hchange
  exact ⟨hint, hchange⟩

/-- The weighted exterior-image formula for any continuous compactly
supported weight. This is the form needed after inserting a cutoff around
the omitted set and the harmonic filling. -/
theorem exteriorImage_compact_weight_change
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (φ : ℂ → ℝ) (hφcont : Continuous φ) (hφsupp : HasCompactSupport φ) :
    IntegrableOn (fun z => ‖deriv G z‖ ^ 2 * φ (G z)) exteriorDisk ∧
      (∫ w in G '' exteriorDisk, φ w ∂volume) =
        ∫ z in exteriorDisk, ‖deriv G z‖ ^ 2 * φ (G z) ∂volume :=
  exteriorImage_integrable_weight_change G hc φ
    (hφcont.integrable_of_hasCompactSupport hφsupp).integrableOn

end SpringerLean
