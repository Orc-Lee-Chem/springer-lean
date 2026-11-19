import SpringerLean.Round29AuxInfinity
import SpringerLean.Round27VerticalCircleSwap

open MeasureTheory Set Metric

namespace SpringerLean

/-- A jointly continuous circle kernel has a parameter-continuous normalized
circle average, with the circle center and radius fixed. -/
theorem circleAverage_continuous_in_parameter
    (f : ℂ → ℂ → ℝ)
    (hf : Continuous (fun p : ℂ × ℂ => f p.1 p.2))
    (c : ℂ) (ρ : ℝ) :
    Continuous (fun z : ℂ => Real.circleAverage (f z) c ρ) := by
  have hpair : Continuous (fun p : ℂ × ℝ => (p.1, circleMap c ρ p.2)) :=
    continuous_fst.prodMk ((continuous_circleMap c ρ).comp continuous_snd)
  have hangle : Continuous (fun p : ℂ × ℝ =>
      f p.1 (circleMap c ρ p.2)) := hf.comp hpair
  have hint : Continuous (fun z : ℂ => ∫ θ in (0:ℝ)..2 * Real.pi,
      f z (circleMap c ρ θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hangle 0 (2 * Real.pi)
  change Continuous (fun z : ℂ =>
    ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in (0:ℝ)..2 * Real.pi, f z (circleMap c ρ θ))
  convert ((continuous_const : Continuous (fun _ : ℂ => ((2 * Real.pi)⁻¹ : ℝ))).smul hint) using 1

/-- A clipped comparison logarithmic potential is continuous everywhere.
The clip will be removed on any region separated from the real segment. -/
noncomputable def comparisonSegmentPotentialClipped (δ : ℝ) (z : ℂ) : ℝ :=
  Real.circleAverage (fun ζ : ℂ =>
    Real.log (max δ ‖z - ((2 * ζ.re : ℝ) : ℂ)‖)) 0 1

theorem comparisonSegmentPotentialClipped_continuous
    {δ : ℝ} (hδ : 0 < δ) :
    Continuous (comparisonSegmentPotentialClipped δ) := by
  let Y : ℂ → ℂ := fun ζ => ((2 * ζ.re : ℝ) : ℂ)
  let K : ℂ → ℂ → ℝ := fun z ζ => Real.log (max δ ‖z - Y ζ‖)
  have hbase : Continuous (fun p : ℂ × ℂ => ‖p.1 - Y p.2‖) := by
    dsimp [Y]
    fun_prop
  have hmax : Continuous (fun p : ℂ × ℂ => max δ ‖p.1 - Y p.2‖) :=
    continuous_const.max hbase
  have hK : Continuous (fun p : ℂ × ℂ => K p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hp : 0 < max δ ‖p.1 - Y p.2‖ :=
      lt_of_lt_of_le hδ (le_max_left _ _)
    change ContinuousAt (fun p : ℂ × ℂ => Real.log (max δ ‖p.1 - Y p.2‖)) p
    exact ContinuousAt.comp (f := fun q : ℂ × ℂ => max δ ‖q.1 - Y q.2‖)
      (x := p) (Real.continuousAt_log (ne_of_gt hp)) hmax.continuousAt
  exact circleAverage_continuous_in_parameter K hK 0 1

end SpringerLean
