import SpringerLean.Round27MaxLogHarmonic

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- The actual rotated logarithmic potential is harmonic at every point
where it is strictly positive. Rotation is incorporated into the analytic
local inverse, so no separate circle-average rotation identity is needed. -/
theorem regularExterior_rotated_potential_harmonicAt_of_pos
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) {z : ℂ}
    (hpos : 0 < regularExteriorRotatedPotential F s ξ z) :
    InnerProductSpace.HarmonicAt
      (regularExteriorRotatedPotential F s ξ) z := by
  let G := rescaleExterior s F
  let Pbase : ℂ → ℝ := fun w => Real.circleAverage
    (fun ζ : ℂ => Real.log ‖G ζ - w‖) 0 1
  have hbasepos : 0 < Pbase (ξ * z) := by
    simpa only [Pbase, G, regularExterior_rotated_potential_eq F s ξ hξ z] using hpos
  have hwS : ξ * z ∈ G '' exteriorAbove s := by
    by_contra hw
    have hwomit : ξ * z ∈ exteriorOmitted G := by
      intro himage
      obtain ⟨v, hv, heq⟩ := himage
      exact hw ⟨v, lt_trans hs1 hv, heq⟩
    have hzero := regularExterior_omitted_boundary_log_potential_zero_all
      F hc hs0 hs1 hwomit
    change Pbase (ξ * z) = 0 at hzero
    rw [hzero] at hbasepos
    exact (lt_irrefl (0 : ℝ)) hbasepos
  obtain ⟨v, hv, hvEq⟩ := hwS
  have hF : ∀ w ∈ exteriorDisk, AnalyticAt ℂ F w :=
    fun w hw => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hw)
  have hG : AnalyticAt ℂ G v := rescaleExterior_analyticAt hs0 hF hv
  have hd : deriv G v ≠ 0 := rescaleExterior_deriv_ne_zero_above F hc hs0 hv
  let R : ℂ → ℂ := hG.hasStrictDerivAt.localInverse G (deriv G v) v hd
  have hR0 : R (G v) = v :=
    HasStrictFDerivAt.localInverse_apply_image
      (hG.hasStrictDerivAt.hasStrictFDerivAt_equiv hd)
  have hRanalytic : AnalyticAt ℂ R (G v) := hG.analyticAt_localInverse hd
  have hRcont : ContinuousAt R (G v) := hRanalytic.continuousAt
  have hUopen : IsOpen (exteriorAbove s) := by
    simpa [exteriorAbove, Set.preimage] using
      (isOpen_Ioi.preimage (continuous_norm : Continuous (fun w : ℂ => ‖w‖)))
  have hRin : ∀ᶠ w in 𝓝 (G v), R w ∈ exteriorAbove s := by
    apply hRcont.eventually
    rw [hR0]
    exact hUopen.mem_nhds hv
  have hright : ∀ᶠ w in 𝓝 (G v), G (R w) = w :=
    hG.hasStrictDerivAt.eventually_right_inverse hd
  have hNearBase : Pbase =ᶠ[𝓝 (G v)]
      (fun w => max (Real.log ‖R w‖) 0) := by
    filter_upwards [hRin, hright] with w hw hGw
    have hvalue := regularExterior_enlarged_image_boundary_log_potential
      F hc hs0 hs1 hw
    change Pbase (G (R w)) = max (Real.log ‖R w‖) 0 at hvalue
    rwa [hGw] at hvalue
  let Q : ℂ → ℂ := fun u => R (ξ * u)
  have hmul : AnalyticAt ℂ (fun u : ℂ => ξ * u) z := by fun_prop
  have hQ : AnalyticAt ℂ Q z := by
    have hR' : AnalyticAt ℂ R (ξ * z) := by simpa only [← hvEq] using hRanalytic
    exact hR'.comp hmul
  have hQ0 : Q z ≠ 0 := by
    change R (ξ * z) ≠ 0
    rw [← hvEq, hR0]
    exact norm_pos_iff.mp (lt_trans hs0 hv)
  have hmulCont : ContinuousAt (fun u : ℂ => ξ * u) z := hmul.continuousAt
  have hmulTendsto : Tendsto (fun u : ℂ => ξ * u) (𝓝 z) (𝓝 (G v)) := by
    change Tendsto (fun u : ℂ => ξ * u) (𝓝 z) (𝓝 (ξ * z)) at hmulCont
    simpa only [hvEq] using hmulCont
  have hNearRot : regularExteriorRotatedPotential F s ξ =ᶠ[𝓝 z]
      (fun u => max (Real.log ‖Q u‖) 0) := by
    have hcomp := hNearBase.comp_tendsto hmulTendsto
    filter_upwards [hcomp] with u hu
    change regularExteriorRotatedPotential F s ξ u =
      max (Real.log ‖R (ξ * u)‖) 0
    rw [regularExterior_rotated_potential_eq F s ξ hξ u]
    exact hu
  exact harmonicAt_of_eventuallyEq_max_log_norm_of_pos hQ hQ0 hNearRot hpos

end SpringerLean
