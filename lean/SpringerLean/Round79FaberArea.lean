import SpringerLean.Round78RowOneArea
import SpringerLean.AnnulusArea

namespace SpringerLean

open MeasureTheory

/-- Change of variables for a real weight on a bounded exterior annulus.
This is the area input needed for a polynomial derivative weight in the
finite Faber inequality. It uses injectivity of the actual map `F`. -/
theorem exteriorAnnulus_image_weighted_change
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r R : ℝ} (hr : 1 < r) (φ : ℂ → ℝ) :
    (∫ w in F '' exteriorAnnulus r R, φ w ∂volume) =
      ∫ z in exteriorAnnulus r R, ‖deriv F z‖ ^ 2 * φ (F z) ∂volume := by
  have hderiv : ∀ z ∈ exteriorAnnulus r R,
      HasFDerivWithinAt F ((deriv F z) • (1 : ℂ →L[ℝ] ℂ))
        (exteriorAnnulus r R) z := by
    intro z hz
    have hzext : z ∈ exteriorDisk :=
      exteriorAnnulus_subset_exteriorDisk hr hz
    have hdiff : DifferentiableAt ℂ F z :=
      hc.1.differentiableAt (exteriorDisk_isOpen.mem_nhds hzext)
    exact hdiff.hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume) (exteriorAnnulus_isOpen r R).measurableSet hderiv
    (hc.2.1.mono (exteriorAnnulus_subset_exteriorDisk hr)) φ
  convert hchange using 1
  apply setIntegral_congr_fun (exteriorAnnulus_isOpen r R).measurableSet
  intro z hz
  change ‖deriv F z‖ ^ 2 * φ (F z) =
    |((deriv F z) • (1 : ℂ →L[ℝ] ℂ)).det| • φ (F z)
  rw [complex_mul_real_det, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  simp only [smul_eq_mul]

/-- The exact finite-annulus change of variables for the nonnegative
polynomial derivative weight. The polynomial itself need not be injective. -/
theorem exteriorAnnulus_image_polynomial_deriv_sq_change
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r R : ℝ} (hr : 1 < r) (P : Polynomial ℂ) :
    (∫ w in F '' exteriorAnnulus r R,
        ‖P.derivative.eval w‖ ^ 2 ∂volume) =
      ∫ z in exteriorAnnulus r R,
        ‖deriv F z‖ ^ 2 * ‖P.derivative.eval (F z)‖ ^ 2 ∂volume :=
  exteriorAnnulus_image_weighted_change F hc hr
    (fun w => ‖P.derivative.eval w‖ ^ 2)

/-- The polynomial derivative weight in the preceding area identity is
integrable on the genuine annulus image. This rules out a vacuous use of
the ordinary integral's nonintegrable default value. -/
theorem exteriorAnnulus_image_polynomial_deriv_sq_integrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r R : ℝ} (hr : 1 < r) (P : Polynomial ℂ) :
    IntegrableOn (fun w => ‖P.derivative.eval w‖ ^ 2)
      (F '' exteriorAnnulus r R) := by
  let K : Set ℂ := Metric.closedBall 0 R ∩ {z : ℂ | r ≤ ‖z‖}
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) R).inter_right
      (isClosed_le continuous_const continuous_norm)
  have hKext : K ⊆ exteriorDisk := by
    intro z hz
    exact lt_of_lt_of_le hr hz.2
  have hFKcompact : IsCompact (F '' K) :=
    hKcompact.image_of_continuousOn (hc.1.continuousOn.mono hKext)
  have hsK : exteriorAnnulus r R ⊆ K := by
    intro z hz
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hz.2.le,
      hz.1.le⟩
  have hsimage : F '' exteriorAnnulus r R ⊆ F '' K :=
    Set.image_mono hsK
  have hmeas : MeasurableSet (F '' exteriorAnnulus r R) := by
    have hderiv : ∀ z ∈ exteriorAnnulus r R,
        HasFDerivWithinAt F ((deriv F z) • (1 : ℂ →L[ℝ] ℂ))
          (exteriorAnnulus r R) z := by
      intro z hz
      have hzext : z ∈ exteriorDisk :=
        exteriorAnnulus_subset_exteriorDisk hr hz
      have hdiff : DifferentiableAt ℂ F z :=
        hc.1.differentiableAt (exteriorDisk_isOpen.mem_nhds hzext)
      exact hdiff.hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt
    exact measurable_image_of_fderivWithin
      (exteriorAnnulus_isOpen r R).measurableSet hderiv
      (hc.2.1.mono (exteriorAnnulus_subset_exteriorDisk hr))
  have hfin : volume (F '' exteriorAnnulus r R) ≠ ⊤ :=
    ne_top_of_le_ne_top hFKcompact.measure_ne_top (measure_mono hsimage)
  have hcont : Continuous (fun w : ℂ => ‖P.derivative.eval w‖ ^ 2) := by
    fun_prop
  exact hcont.continuousOn.integrableOn_of_subset_isCompact
    hFKcompact hmeas hsimage hfin

end SpringerLean
