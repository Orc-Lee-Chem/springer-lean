import SpringerLean.Round17ShiftIntegral
import SpringerLean.Round16VerticalPrelude

open MeasureTheory

namespace SpringerLean

/-- A compensated vertical-line logarithm for one complex boundary point. -/
noncomputable def verticalPointKernel (a : ℝ) (w : ℂ) (y : ℝ) : ℝ :=
  Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) - w‖ -
    verticalLogRadial 1 y + w.im * verticalBaseSlope y

theorem verticalPointKernel_decompose (a : ℝ) (w : ℂ) (y : ℝ) :
    verticalPointKernel a w y =
      (verticalLogRadial |a - w.re| (y - w.im) -
        verticalLogRadial 1 (y - w.im)) +
      verticalShiftRemainder w.im y := by
  rw [verticalShiftRemainder, verticalPointKernel,
    vertical_log_norm_eq_half_log_squares]
  have habs : |a - w.re| ^ 2 = (a - w.re) ^ 2 := sq_abs _
  simp only [verticalLogRadial, habs]
  ring

/-- The compensated logarithmic kernel is genuinely integrable, including
when the vertical line passes through the target point. -/
theorem verticalPointKernel_integrable (a : ℝ) (w : ℂ) :
    Integrable (verticalPointKernel a w) := by
  have hrad := (verticalLogRadial_sub_one_integrable (abs_nonneg (a - w.re))).comp_sub_right w.im
  have hshift := verticalShiftRemainder_integrable w.im
  convert hrad.add hshift using 1
  funext y
  exact verticalPointKernel_decompose a w y

/-- The full vertical-line integral for one point is π times horizontal
distance minus the same base constant for every target. -/
theorem verticalPointKernel_integral (a : ℝ) (w : ℂ) :
    (∫ y : ℝ, verticalPointKernel a w y) =
      Real.pi * (|a - w.re| - 1) := by
  have hrad := (verticalLogRadial_sub_one_integrable (abs_nonneg (a - w.re))).comp_sub_right w.im
  rw [show (fun y : ℝ => verticalPointKernel a w y) =
      (fun y => verticalLogRadial |a - w.re| (y - w.im) -
        verticalLogRadial 1 (y - w.im)) + verticalShiftRemainder w.im from
        funext (verticalPointKernel_decompose a w)]
  change (∫ y : ℝ,
      (verticalLogRadial |a - w.re| (y - w.im) -
        verticalLogRadial 1 (y - w.im)) + verticalShiftRemainder w.im y) = _
  rw [integral_add hrad (verticalShiftRemainder_integrable w.im)]
  have htrans : (∫ y : ℝ,
      verticalLogRadial |a - w.re| (y - w.im) -
        verticalLogRadial 1 (y - w.im)) =
      ∫ y : ℝ, verticalLogRadial |a - w.re| y - verticalLogRadial 1 y := by
    exact integral_sub_right_eq_self (μ := volume)
      (fun y : ℝ => verticalLogRadial |a - w.re| y - verticalLogRadial 1 y) w.im
  rw [htrans, verticalLogRadial_sub_one_integral (abs_nonneg (a - w.re)),
    verticalShiftRemainder_integral_zero, add_zero]

/-- A parameter-uniform L¹ estimate for one compensated point kernel.
It is polynomial in the horizontal and imaginary coordinates of the point. -/
theorem verticalPointKernel_abs_integral_le (a : ℝ) (w : ℂ) :
    (∫ y : ℝ, |verticalPointKernel a w y|) ≤
      Real.pi * |(|a - w.re|) - 1| +
        w.im ^ 2 * (∫ y : ℝ, ‖verticalBaseCurvature y‖) := by
  let D : ℝ → ℝ := fun y =>
    verticalLogRadial |a - w.re| (y - w.im) - verticalLogRadial 1 (y - w.im)
  let R : ℝ → ℝ := verticalShiftRemainder w.im
  have hD : Integrable D :=
    (verticalLogRadial_sub_one_integrable (abs_nonneg (a - w.re))).comp_sub_right w.im
  have hR : Integrable R := verticalShiftRemainder_integrable w.im
  have hpoint (y : ℝ) : |verticalPointKernel a w y| ≤ |D y| + |R y| := by
    rw [verticalPointKernel_decompose]
    exact abs_add_le _ _
  have hle := integral_mono (verticalPointKernel_integrable a w).abs
    (hD.abs.add hR.abs) hpoint
  have hDint : (∫ y : ℝ, |D y|) = Real.pi * |(|a - w.re|) - 1| := by
    change (∫ y : ℝ,
      |(verticalLogRadial |a - w.re| (y - w.im) -
        verticalLogRadial 1 (y - w.im))|) = _
    rw [integral_sub_right_eq_self (μ := volume)
      (fun y : ℝ => |verticalLogRadial |a - w.re| y - verticalLogRadial 1 y|) w.im]
    exact verticalLogRadial_sub_one_abs_integral (abs_nonneg (a - w.re))
  change (∫ y : ℝ, |verticalPointKernel a w y|) ≤
    (∫ y : ℝ, |D y| + |R y|) at hle
  rw [integral_add hD.abs hR.abs, hDint] at hle
  have hshift := add_le_add_left (verticalShiftRemainder_abs_integral_le_sq w.im)
    (Real.pi * |(|a - w.re|) - 1|)
  exact hle.trans (by simpa only [R, add_comm] using hshift)

end SpringerLean
