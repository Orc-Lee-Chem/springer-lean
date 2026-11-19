import SpringerLean.OuterCircle
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Complex.Determinant

namespace SpringerLean

theorem complex_mul_real_det (c : ℂ) :
    (c • (1 : ℂ →L[ℝ] ℂ)).det = Complex.normSq c := by
  change (c • (1 : ℂ →L[ℝ] ℂ)).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  have hm : (c • (1 : ℂ →L[ℝ] ℂ)).toLinearMap.toMatrix
      Complex.basisOneI Complex.basisOneI =
      !![c.re, -c.im; c.im, c.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply]
  rw [hm, Matrix.det_fin_two_of]
  simp [Complex.normSq_apply]

/-- An annulus strictly inside the paper's exterior domain. -/
def exteriorAnnulus (r R : ℝ) : Set ℂ :=
  {z | r < ‖z‖ ∧ ‖z‖ < R}

theorem exteriorAnnulus_isOpen (r R : ℝ) :
    IsOpen (exteriorAnnulus r R) := by
  exact (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem exteriorAnnulus_subset_exteriorDisk {r R : ℝ} (hr : 1 < r) :
    exteriorAnnulus r R ⊆ exteriorDisk := by
  intro z hz
  exact lt_trans hr hz.1

/-- The area of the image of an exterior annulus, as an actual Jacobian
integral. This is the change-of-variables step of the area argument. -/
theorem exteriorAnnulus_image_area_eq_jacobian
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r R : ℝ} (hr : 1 < r) :
    (∫⁻ z in exteriorAnnulus r R,
       ENNReal.ofReal |((deriv F z) • (1 : ℂ →L[ℝ] ℂ)).det| ∂MeasureTheory.volume) =
      MeasureTheory.volume (F '' exteriorAnnulus r R) := by
  have hs : MeasurableSet (exteriorAnnulus r R) :=
    (exteriorAnnulus_isOpen r R).measurableSet
  have hderiv : ∀ z ∈ exteriorAnnulus r R,
      HasFDerivWithinAt F ((deriv F z) • (1 : ℂ →L[ℝ] ℂ))
        (exteriorAnnulus r R) z := by
    intro z hz
    have hzext : z ∈ exteriorDisk :=
      exteriorAnnulus_subset_exteriorDisk hr hz
    have hdiff : DifferentiableAt ℂ F z :=
      hc.1.differentiableAt (exteriorDisk_isOpen.mem_nhds hzext)
    exact hdiff.hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt
  have hinj : Set.InjOn F (exteriorAnnulus r R) :=
    hc.2.1.mono (exteriorAnnulus_subset_exteriorDisk hr)
  exact MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
    MeasureTheory.volume hs hderiv hinj

/-- The Jacobian in the preceding image-area formula is `|F'|²`. -/
theorem exteriorAnnulus_image_area_eq_deriv_sq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r R : ℝ} (hr : 1 < r) :
    (∫⁻ z in exteriorAnnulus r R,
      ENNReal.ofReal (‖deriv F z‖ ^ 2) ∂MeasureTheory.volume) =
      MeasureTheory.volume (F '' exteriorAnnulus r R) := by
  convert exteriorAnnulus_image_area_eq_jacobian F hc hr using 1
  apply MeasureTheory.setLIntegral_congr_fun
  · exact (exteriorAnnulus_isOpen r R).measurableSet
  · intro z hz
    change ENNReal.ofReal (‖deriv F z‖ ^ 2) =
      ENNReal.ofReal |((deriv F z) • (1 : ℂ →L[ℝ] ℂ)).det|
    rw [complex_mul_real_det, abs_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq]

end SpringerLean
