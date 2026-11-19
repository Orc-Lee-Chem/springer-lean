import SpringerLean.Round28PotentialOffCurve

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual regularized rotated boundary logarithmic potential is
continuous on the entire complex plane, including its boundary curve. -/
theorem regularExterior_rotated_potential_continuous
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    Continuous (regularExteriorRotatedPotential F s ξ) := by
  let b : ℂ → ℂ := fun ζ => conj ξ * rescaleExterior s F ζ
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : ContinuousOn (rescaleExterior s F) (sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hζ
    have hz : ζ ∈ exteriorAbove s := by
      change s < ‖ζ‖
      rw [hnorm]
      exact hs1
    exact (rescaleExterior_analyticAt hs0 hF hz).continuousAt.continuousWithinAt
  have hb : ContinuousOn b (sphere (0 : ℂ) 1) :=
    continuousOn_const.mul hG
  obtain ⟨M, hM0, hM⟩ :=
    regularExterior_boundary_curve_norm_bounded F hc hs0 hs1
  have hbM : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖b ζ‖ ≤ M := by
    intro ζ hζ
    dsimp [b]
    rw [norm_mul, Complex.norm_conj, hξ, one_mul]
    exact hM ζ hζ
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ b '' sphere (0 : ℂ) 1
  · obtain ⟨ζ, hζ, rfl⟩ := hz
    have hζnorm : ‖ζ‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hζ
    exact regularExterior_rotated_potential_continuousAt_curve
      F hc hs0 hs1 ξ hξ hζnorm
  · have h := boundary_log_potential_continuousAt_off_curve
      b hb M hM0 hbM z hz
    change ContinuousAt (fun w : ℂ => Real.circleAverage
      (fun ζ : ℂ => Real.log ‖w - b ζ‖) 0 1) z
    exact h

end SpringerLean