import SpringerLean.Round13Potential
import Mathlib.Analysis.Complex.Poisson

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The real Poisson kernel is unchanged by conjugating both the target
and the boundary point. -/
theorem poissonKernel_conj_zero (w ζ : ℂ) :
    poissonKernel 0 (conj w) (conj ζ) = poissonKernel 0 w ζ := by
  simp [poissonKernel_def, ← map_sub]

/-- The actual regular correction is complex differentiable on and inside
the unit circle, because the dilation parameter is strictly below one. -/
theorem regularForwardGerm_diffContOnCl_unitDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    DiffContOnCl ℂ (regularForwardGerm s F) (ball 0 1) := by
  have hlarge : 1 < s⁻¹ := by
    have h := one_div_lt_one_div_of_lt hs0 hs1
    simpa only [one_div, inv_one] using h
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 s⁻¹ := by
    intro z hz
    exact lt_of_le_of_lt hz hlarge
  exact (regularForwardGerm_analyticOnNhd F hc hs0).differentiableOn
    |>.diffContOnCl_ball hsub

/-- Poisson reproduces the antiholomorphic correction after reflecting
the boundary circle. -/
theorem regularForwardGerm_conj_poisson
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    Real.circleAverage
      (fun ζ : ℂ => (poissonKernel 0 z ζ) •
        regularForwardGerm s F (conj ζ)) 0 1 =
      regularForwardGerm s F (conj z) := by
  have hzc : conj z ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, Complex.norm_conj] using hz
  have hP := (regularForwardGerm_diffContOnCl_unitDisk F hc hs0 hs1)
    |>.circleAverage_poissonKernel_smul hzc
  calc
    Real.circleAverage
        (fun ζ : ℂ => (poissonKernel 0 z ζ) •
          regularForwardGerm s F (conj ζ)) 0 1 =
      Real.circleAverage
        (fun ζ : ℂ => (poissonKernel 0 (conj z) (conj ζ)) •
          regularForwardGerm s F (conj ζ)) 0 1 := by
            congr 1
            funext ζ
            rw [poissonKernel_conj_zero]
    _ = Real.circleAverage
        (fun ζ : ℂ => (poissonKernel 0 (conj z) ζ) •
          regularForwardGerm s F ζ) 0 1 :=
      circleAverage_comp_conj_zero
        (fun ζ : ℂ => (poissonKernel 0 (conj z) ζ) •
          regularForwardGerm s F ζ) 1
    _ = regularForwardGerm s F (conj z) := hP

end SpringerLean
