import SpringerLean.Round27PotentialHarmonic

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean

/-- The actual regularized boundary logarithmic potential is nonnegative
at every target, by the proven image and omitted-value formulas. -/
theorem regularExterior_boundary_potential_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (w : ℂ) :
    0 ≤ Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1 := by
  let G := rescaleExterior s F
  by_cases hw : w ∈ G '' exteriorDisk
  · obtain ⟨v, hv, rfl⟩ := hw
    rw [regularExterior_image_boundary_log_potential F hc hs0 hs1 hv]
    exact Real.log_nonneg (le_of_lt hv)
  · have hzero := regularExterior_omitted_boundary_log_potential_zero_all
      F hc hs0 hs1 hw
    rw [hzero]

/-- Local circle submean for the actual regularized logarithmic potential.
At positive centers it is harmonic by the analytic local inverse; at
zero centers its nonnegativity gives the submean inequality directly. -/
theorem regularExterior_boundary_potential_local_circle_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (w : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
      Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1 ≤
      Real.circleAverage
        (fun u : ℂ => Real.circleAverage
          (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - u‖) 0 1) w ρ := by
  let P : ℂ → ℝ := fun u => Real.circleAverage
    (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - u‖) 0 1
  by_cases hwpos : 0 < P w
  · have hH : InnerProductSpace.HarmonicAt P w :=
      regularExterior_boundary_potential_harmonicAt_of_pos F hc hs0 hs1 hwpos
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hH.eventually
    refine ⟨ε, hε, ?_⟩
    intro ρ hρ hρε
    have hOn : InnerProductSpace.HarmonicOnNhd P (closedBall w |ρ|) := by
      intro u hu
      apply hball
      change dist u w < ε
      have hdist : dist u w ≤ |ρ| := hu
      rw [abs_of_pos hρ] at hdist
      exact lt_of_le_of_lt hdist hρε
    change P w ≤ Real.circleAverage P w ρ
    rw [hOn.circleAverage_eq]
  · have hwzero : P w = 0 := le_antisymm (le_of_not_gt hwpos)
      (regularExterior_boundary_potential_nonneg F hc hs0 hs1 w)
    refine ⟨1, by norm_num, ?_⟩
    intro ρ hρ hρ1
    change P w ≤ Real.circleAverage P w ρ
    rw [hwzero]
    apply Real.circleAverage_nonneg_of_nonneg
    intro u hu
    exact regularExterior_boundary_potential_nonneg F hc hs0 hs1 u

end SpringerLean
