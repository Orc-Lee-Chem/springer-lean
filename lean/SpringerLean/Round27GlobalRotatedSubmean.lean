import SpringerLean.Round27GlobalPotentialSubmean

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual rotated boundary potential satisfies the circle submean
inequality at every center and every positive radius. In particular, its
radius can be chosen uniformly for every point of a vertical optimizer. -/
theorem regularExterior_rotated_potential_circle_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (w : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    regularExteriorRotatedPotential F s ξ w ≤
      Real.circleAverage (regularExteriorRotatedPotential F s ξ) w ρ := by
  let G := rescaleExterior s F
  let b : ℂ → ℂ := fun ζ => conj ξ * G ζ
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : ContinuousOn G (sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hζ
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
  by_cases hw : w ∈ b '' sphere (0 : ℂ) 1
  · obtain ⟨ζ, hζ, rfl⟩ := hw
    have hζnorm : ‖ζ‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hζ
    have hzero := regularExterior_curve_boundary_log_potential_zero
      F hc hs0 hs1 hζnorm
    have hunit : ξ * conj ξ = 1 := by
      rw [RCLike.mul_conj, hξ]
      norm_num
    have hrot : regularExteriorRotatedPotential F s ξ (b ζ) = 0 := by
      rw [regularExterior_rotated_potential_eq F s ξ hξ]
      have heq : ξ * b ζ = G ζ := by
        dsimp [b]
        rw [← mul_assoc, hunit, one_mul]
      rw [heq]
      exact hzero
    rw [hrot]
    apply Real.circleAverage_nonneg_of_nonneg
    intro u hu
    exact regularExterior_rotated_boundary_potential_nonneg
      F hc hs0 hs1 ξ hξ u
  · have h := boundary_log_potential_circle_submean_of_not_mem_curve
        b hb M hbM w hw ρ hρ
    exact h

end SpringerLean