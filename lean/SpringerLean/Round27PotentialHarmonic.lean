import SpringerLean.Round27MaxHarmonic

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- At every point where the actual regularized logarithmic boundary
potential is positive, it is harmonic. The proof uses the analytic local
inverse of the same regularized map; the zero-potential region is handled
separately when establishing a submean inequality. -/
theorem regularExterior_boundary_potential_harmonicAt_of_pos
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {w : ℂ}
    (hwpos : 0 < Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1) :
    InnerProductSpace.HarmonicAt
      (fun u : ℂ => Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - u‖) 0 1) w := by
  let G := rescaleExterior s F
  let P : ℂ → ℝ := fun u => Real.circleAverage
    (fun ζ : ℂ => Real.log ‖G ζ - u‖) 0 1
  let S := G '' exteriorAbove s
  have hwS : w ∈ S := by
    by_contra hw
    have hwomit : w ∈ exteriorOmitted G := by
      intro himage
      obtain ⟨v, hv, rfl⟩ := himage
      exact hw ⟨v, lt_trans hs1 hv, rfl⟩
    have hzero := regularExterior_omitted_boundary_log_potential_zero_all
      F hc hs0 hs1 hwomit
    rw [hzero] at hwpos
    exact (lt_irrefl (0 : ℝ)) hwpos
  obtain ⟨v, hv, rfl⟩ := hwS
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
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
      (isOpen_Ioi.preimage (continuous_norm : Continuous (fun z : ℂ => ‖z‖)))
  have hRin : ∀ᶠ u in 𝓝 (G v), R u ∈ exteriorAbove s := by
    apply hRcont.eventually
    rw [hR0]
    exact hUopen.mem_nhds hv
  have hright : ∀ᶠ u in 𝓝 (G v), G (R u) = u :=
    hG.hasStrictDerivAt.eventually_right_inverse hd
  have hnear : P =ᶠ[𝓝 (G v)] (fun u => max (Real.log ‖R u‖) 0) := by
    filter_upwards [hRin, hright] with u hu hGu
    have hvalue := regularExterior_enlarged_image_boundary_log_potential
      F hc hs0 hs1 hu
    change P (G (R u)) = max (Real.log ‖R u‖) 0 at hvalue
    rwa [hGu] at hvalue
  have hvpos : 0 < ‖v‖ := lt_trans hs0 hv
  have hlogCont : ContinuousAt (fun u : ℂ => Real.log ‖R u‖) (G v) := by
    apply (Real.continuousAt_log ?_).comp hRcont.norm
    rw [hR0]
    exact ne_of_gt hvpos
  have hlogpos : 0 < Real.log ‖R (G v)‖ := by
    have hvalue := regularExterior_enlarged_image_boundary_log_potential
      F hc hs0 hs1 hv
    change P (G v) = max (Real.log ‖v‖) 0 at hvalue
    rw [hR0]
    have hPpos : 0 < P (G v) := hwpos
    rw [hvalue] at hPpos
    by_contra hn
    have hnonpos : Real.log ‖v‖ ≤ 0 := le_of_not_gt hn
    rw [max_eq_right hnonpos] at hPpos
    exact (lt_irrefl (0 : ℝ)) hPpos
  have hpositive : ∀ᶠ u in 𝓝 (G v), 0 < Real.log ‖R u‖ :=
    hlogCont.eventually (isOpen_Ioi.mem_nhds hlogpos)
  have heq : P =ᶠ[𝓝 (G v)] (fun u => Real.log ‖R u‖) := by
    filter_upwards [hnear, hpositive] with u hu hupos
    rw [hu]
    exact max_eq_left (le_of_lt hupos)
  have hlogH : InnerProductSpace.HarmonicAt
      (fun u : ℂ => Real.log ‖R u‖) (G v) :=
    hRanalytic.harmonicAt_log_norm (by rw [hR0]; exact norm_pos_iff.mp hvpos)
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr hlogH

end SpringerLean
