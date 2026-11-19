import SpringerLean.Round1540PeakDeficitThreeHalves
import Mathlib.Analysis.Convex.Continuous

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The positive semicircle loses at least the explicitly integrated
quadratic tangent remainder. The factor 1/π is the full-circle
probability normalization after evenness. -/
theorem clippedTangentPower_peakArc_semicircle_loss
    {r v M : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hM0 : 0 ≤ M) (hMq : M ≤ 2*r-v)
    {m : ℕ} (hm : 2 ≤ m) :
    (4/(15*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
        (2*r-v)^(m-2)*v^2*Real.sqrt v ≤
      Real.pi⁻¹ *
        (∫ θ in (0:ℝ)..Real.pi,
          (max (2*r*Real.cos θ) 0)^m-
            clippedTangentPower M m (2*r*Real.cos θ)) := by
  let b := Real.sqrt v
  let q := 2*r-v
  let L : ℝ → ℝ := fun θ =>
    (max (2*r*Real.cos θ) 0)^m-
      clippedTangentPower M m (2*r*Real.cos θ)
  let C : ℝ := ((m:ℝ)*((m:ℝ)-1)/2)*q^(m-2)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg v
  have hbpi : b ≤ Real.pi := by
    have hb2 : b^2=v := Real.sq_sqrt hv0
    have hb1 : b ≤ 1 := by nlinarith
    linarith [Real.pi_gt_three]
  have hclipC : Continuous (clippedTangentPower M m) := by
    have hc := (clippedTangentPower_convexOn hM0 (by omega : 1 ≤ m)).continuousOn
      isOpen_univ
    simpa using hc
  have hLC : Continuous L := by
    dsimp [L]
    fun_prop (disch := exact hclipC)
  have hLI1 : IntervalIntegrable L volume 0 b := hLC.intervalIntegrable _ _
  have hLI2 : IntervalIntegrable L volume b Real.pi := hLC.intervalIntegrable _ _
  have hpolyC : Continuous (fun θ : ℝ => C*(v-θ^2)^2) := by fun_prop
  have hpolyI : IntervalIntegrable (fun θ : ℝ => C*(v-θ^2)^2)
      volume 0 b := hpolyC.intervalIntegrable _ _
  have hlocal : C*(8/15:ℝ)*v^2*b ≤
      ∫ θ in (0:ℝ)..b,L θ := by
    have hcmp : (∫ θ in (0:ℝ)..b,C*(v-θ^2)^2) ≤
        ∫ θ in (0:ℝ)..b,L θ := by
      apply intervalIntegral.integral_mono_on hb0 hpolyI hLI1
      intro θ hθ
      exact clippedTangentPower_shortPeakArc_pointwise
        hr0 hr1 hv0 hM0 hMq hθ.1 hθ.2 hm
    rw [intervalIntegral.integral_const_mul,
      shortPeakArc_square_integral hv0] at hcmp
    simpa [b,mul_assoc] using hcmp
  have houter : 0 ≤ ∫ θ in b..Real.pi,L θ := by
    apply intervalIntegral.integral_nonneg hbpi
    intro θ _
    dsimp [L]
    exact sub_nonneg.mpr
      (clippedTangentPower_le_positivePart_pow hM0 m)
  have hfull : C*(8/15:ℝ)*v^2*b ≤
      ∫ θ in (0:ℝ)..Real.pi,L θ := by
    rw [←intervalIntegral.integral_add_adjacent_intervals hLI1 hLI2]
    linarith
  have hscale := mul_le_mul_of_nonneg_left hfull
    (show 0 ≤ Real.pi⁻¹ by positivity)
  change (4/(15*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
      q^(m-2)*v^2*b ≤ Real.pi⁻¹*(∫ θ in (0:ℝ)..Real.pi,L θ)
  convert hscale using 1
  dsimp [C]
  ring

end SpringerLean

#print axioms SpringerLean.clippedTangentPower_peakArc_semicircle_loss
