import SpringerLean.Round17LogAngles

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- On a finite angle interval, the compensated kernel differs from the
ordinary logarithm by a common radial term and the imaginary mean. -/
theorem verticalCurveKernel_angle_decompose
    (a y : ℝ) (W : ℝ → ℂ) (hW : Continuous W)
    (hlog : IntegrableOn
      (fun θ : ℝ => Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) - W θ‖)
      (Ioc (0 : ℝ) (2 * Real.pi))) :
    (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), verticalPointKernel a (W θ) y) =
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) - W θ‖) -
      (∫ _θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), verticalLogRadial 1 y) +
      verticalBaseSlope y *
        (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), (W θ).im) := by
  let S : Set ℝ := Ioc (0 : ℝ) (2 * Real.pi)
  have hI : IntegrableOn (fun θ : ℝ => (W θ).im) S := by
    have h : Continuous (fun θ : ℝ => (W θ).im) := Complex.continuous_im.comp hW
    exact (h.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi)))).mono_set Ioc_subset_Icc_self
  have hC : IntegrableOn (fun _θ : ℝ => verticalLogRadial 1 y) S := by
    exact integrableOn_const (hs := by
      dsimp [S]
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hmul : IntegrableOn
      (fun θ : ℝ => (W θ).im * verticalBaseSlope y) S := hI.mul_const _
  change (∫ θ : ℝ in S,
      Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) - W θ‖ -
        verticalLogRadial 1 y + (W θ).im * verticalBaseSlope y) = _
  have hsplit := integral_add (hlog.sub hC) hmul
  have hsub := integral_sub hlog hC
  have hmulint := integral_mul_const (f := fun θ : ℝ => (W θ).im)
    (r := verticalBaseSlope y) (μ := volume.restrict S)
  simp only [Pi.add_apply, Pi.sub_apply] at hsplit hsub
  rw [hsplit, hsub, hmulint]
  ring

/-- Two continuous curves with the same imaginary angle integral have the
same raw and compensated vertical potential difference pointwise. -/
theorem verticalCurveKernel_difference_eq_raw
    (a y : ℝ) (W V : ℝ → ℂ) (hW : Continuous W) (hV : Continuous V)
    (hlogW : IntegrableOn
      (fun θ : ℝ => Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) - W θ‖)
      (Ioc (0 : ℝ) (2 * Real.pi)))
    (hlogV : IntegrableOn
      (fun θ : ℝ => Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) - V θ‖)
      (Ioc (0 : ℝ) (2 * Real.pi)))
    (hmean : (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), (W θ).im) =
      ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), (V θ).im) :
    (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), verticalPointKernel a (W θ) y) -
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), verticalPointKernel a (V θ) y) =
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) - W θ‖) -
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) - V θ‖) := by
  rw [verticalCurveKernel_angle_decompose a y W hW hlogW,
    verticalCurveKernel_angle_decompose a y V hV hlogV, hmean]
  ring

end SpringerLean
