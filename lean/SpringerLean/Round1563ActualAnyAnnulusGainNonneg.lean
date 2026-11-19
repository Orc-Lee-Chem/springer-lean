import SpringerLean.Round1562SelectedTwoInteriorDiskGains
import SpringerLean.Round747ActualAnnulusConvex

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The ordinary convex order makes the positive-power gain
nonnegative on every compact annulus inside the unit disk. -/
theorem actualHarmonic_positivePower_annulus_gain_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ ∫ z in greenPolarRegion a b,
      (max (2*z.re) 0)^m-
        (max ((conj ξ*actualHarmonic F z).re) 0)^m := by
  let Y : ℂ → ℝ := fun z => (max (2*z.re) 0)^m
  let X : ℂ → ℝ := fun z =>
    (max ((conj ξ*actualHarmonic F z).re) 0)^m
  have hsub : closedBall (0:ℂ) b ⊆ ball 0 1 := by
    intro z hz
    have hn : ‖z‖ ≤ b := by simpa only [mem_closedBall,dist_zero_right] using hz
    simpa only [mem_ball,dist_zero_right] using hn.trans_lt hb
  have hH := (actualHarmonic_continuousOn_unitBall F hc).mono hsub
  have hX : ContinuousOn X (closedBall (0:ℂ) b) := by
    have hproj : ContinuousOn
        (fun z : ℂ => (conj ξ*actualHarmonic F z).re)
        (closedBall (0:ℂ) b) :=
      Complex.continuous_re.comp_continuousOn
        (continuousOn_const.mul hH)
    exact (continuous_max.comp_continuousOn
      (hproj.prodMk continuousOn_const)).pow m
  have hY : ContinuousOn Y (closedBall (0:ℂ) b) := by
    dsimp [Y]
    fun_prop
  have hregion : greenPolarRegion a b ⊆ closedBall (0:ℂ) b := by
    intro z hz
    exact mem_closedBall.mpr (by simpa only [dist_zero_right] using le_of_lt hz.2)
  have hXi : IntegrableOn X (greenPolarRegion a b) :=
    (hX.integrableOn_compact (isCompact_closedBall _ _)).mono_set hregion
  have hYi : IntegrableOn Y (greenPolarRegion a b) :=
    (hY.integrableOn_compact (isCompact_closedBall _ _)).mono_set hregion
  have horder := actualHarmonic_annulus_convex_le F hc ξ hξ
    (fun x : ℝ => (max x 0)^m) (positivePart_pow_convexOn m hm)
    ha hab hb
  change Real.pi⁻¹*(∫ z in greenPolarRegion a b, X z) ≤
    Real.pi⁻¹*(∫ z in greenPolarRegion a b, Y z) at horder
  have hle : (∫ z in greenPolarRegion a b, X z) ≤
      ∫ z in greenPolarRegion a b, Y z :=
    le_of_mul_le_mul_left horder (inv_pos.mpr Real.pi_pos)
  change 0 ≤ ∫ z in greenPolarRegion a b, Y z-X z
  rw [integral_sub hYi hXi]
  linarith

end SpringerLean

#print axioms SpringerLean.actualHarmonic_positivePower_annulus_gain_nonneg
