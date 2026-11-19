import SpringerLean.Round27RadialL1

open MeasureTheory

namespace SpringerLean

/-- The compensated logarithmic point kernel is globally Lipschitz in the
horizontal coordinate as an L¹ function of the vertical variable. -/
theorem verticalPointKernel_L1_lipschitz_horizontal
    (a a' : ℝ) (w : ℂ) :
    (∫ y : ℝ, |verticalPointKernel a w y -
      verticalPointKernel a' w y|) ≤ Real.pi * |a - a'| := by
  let b : ℝ := |a - w.re|
  let c : ℝ := |a' - w.re|
  have hpoint (y : ℝ) :
      verticalPointKernel a w y - verticalPointKernel a' w y =
        verticalLogRadial b (y - w.im) - verticalLogRadial c (y - w.im) := by
    rw [verticalPointKernel_decompose, verticalPointKernel_decompose]
    dsimp [b, c]
    ring
  have hbcInt : Integrable (fun y : ℝ =>
      |verticalLogRadial b y - verticalLogRadial c y|) := by
    have hb := verticalLogRadial_sub_one_integrable (abs_nonneg (a - w.re))
    have hc := verticalLogRadial_sub_one_integrable (abs_nonneg (a' - w.re))
    have h := (hb.sub hc).abs
    convert h using 1
    funext y
    change |verticalLogRadial b y - verticalLogRadial c y| =
      |(verticalLogRadial b y - verticalLogRadial 1 y) -
        (verticalLogRadial c y - verticalLogRadial 1 y)|
    ring
  have hL : |b - c| ≤ |a - a'| := by
    have h := abs_abs_sub_abs_le_abs_sub (a - w.re) (a' - w.re)
    dsimp [b, c]
    convert h using 1 <;> ring
  calc
    (∫ y : ℝ, |verticalPointKernel a w y -
        verticalPointKernel a' w y|) =
      ∫ y : ℝ, |verticalLogRadial b (y - w.im) -
        verticalLogRadial c (y - w.im)| := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [hpoint]
    _ = ∫ y : ℝ, |verticalLogRadial b y - verticalLogRadial c y| := by
          exact integral_sub_right_eq_self
            (fun y : ℝ => |verticalLogRadial b y - verticalLogRadial c y|) w.im
    _ = Real.pi * |b - c| := verticalLogRadial_sub_abs_integral
      (abs_nonneg (a - w.re)) (abs_nonneg (a' - w.re))
    _ ≤ Real.pi * |a - a'| := mul_le_mul_of_nonneg_left hL Real.pi_nonneg

end SpringerLean