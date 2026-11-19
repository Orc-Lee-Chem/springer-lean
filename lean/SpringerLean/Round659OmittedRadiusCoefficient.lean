import SpringerLean.Round658ActualBoundaryMoment
import SpringerLean.Round639RegularBoundaryOmitted
import SpringerLean.Round401EndpointChoices

open Filter
open scoped Topology

namespace SpringerLean
set_option Elab.async false

theorem rescaleExterior_boundary_power_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) :
    CircleIntegrable (fun ζ => ‖rescaleExterior s F ζ‖^n) 0 1 := by
  have hcont : ContinuousOn (rescaleExterior s F) (Metric.sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hζ
    have hsrc : ζ ∈ exteriorAbove s := by change s < ‖ζ‖; rwa [hnorm]
    have ha := rescaleExterior_analyticAt hs0
      (fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)) hsrc
    exact ha.continuousAt.continuousWithinAt
  exact (hcont.norm.pow n).circleIntegrable (by norm_num)

/-- The omitted radius controls the actual inverse coefficient with its
essential factor n. Compact collar convergence replaces unproved boundary
traces of the original F. -/
theorem exteriorInverseCoeff_mul_norm_le_of_omitted_radius
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ w ∈ exteriorOmitted F, ‖w‖ ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ)*‖exteriorInverseCoeff F n‖ ≤ R^n := by
  have hscale (j : ℕ) :
      (n : ℝ)*‖exteriorInverseCoeff (rescaleExterior (omittedScaleSeq j) F) n‖ =
        (n : ℝ)*(omittedScaleSeq j^(n+1)*‖exteriorInverseCoeff F n‖) := by
    rw [rescaleExterior_inverseCoeff F hc (omittedScaleSeq_pos j)
      (omittedScaleSeq_lt_one j) hn,norm_mul,norm_pow]
    have hsN : ‖(omittedScaleSeq j : ℂ)‖=omittedScaleSeq j := by
      simp [abs_of_pos (omittedScaleSeq_pos j)]
    rw [hsN]
  have hleft : Tendsto
      (fun j : ℕ => (n : ℝ)*(omittedScaleSeq j^(n+1)*‖exteriorInverseCoeff F n‖))
      atTop (𝓝 ((n : ℝ)*‖exteriorInverseCoeff F n‖)) := by
    have h := (tendsto_const_nhds (x := (n : ℝ))).mul
      ((omittedScaleSeq_tendsto_one.pow (n+1)).mul
        (tendsto_const_nhds (x := ‖exteriorInverseCoeff F n‖)))
    simpa only [one_pow,one_mul] using h
  have hall (ε : ℝ) (hε : 0 < ε) :
      (n : ℝ)*‖exteriorInverseCoeff F n‖ ≤ (R+ε)^n := by
    have hclose := exteriorOmitted_rescale_inequality_eventually_scaleSeq F hc
      Set.univ isClosed_univ (fun w : ℂ => ‖w‖-R)
      (continuous_norm.sub continuous_const)
      (fun w hw _ => sub_nonpos.mpr (hR w hw)) hε
    have hbound : ∀ᶠ j : ℕ in atTop,
        (n : ℝ)*‖exteriorInverseCoeff (rescaleExterior (omittedScaleSeq j) F) n‖ ≤
          (R+ε)^n := by
      filter_upwards [hclose] with j hj
      apply (rescaleExterior_inverseCoeff_mul_norm_le_boundary_moment F hc
        (omittedScaleSeq_pos j) (omittedScaleSeq_lt_one j) n hn).trans
      apply Real.circleAverage_mono_on_of_le_circle
        (rescaleExterior_boundary_power_circleIntegrable F hc
          (omittedScaleSeq_pos j) (omittedScaleSeq_lt_one j) n)
      intro ζ hζ
      have hζn : ‖ζ‖=1 := by
        simpa only [abs_one,Metric.mem_sphere,dist_zero_right] using hζ
      have hmem := rescaleExterior_unitCircle_mem_omitted F hc
        (omittedScaleSeq_pos j) (omittedScaleSeq_lt_one j) hζn
      have hnorm := hj _ hmem (Set.mem_univ _)
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) n
    simp only [hscale] at hbound
    exact le_of_tendsto hleft hbound
  have hpow0 : Tendsto (fun ε : ℝ => (R+ε)^n) (𝓝[>] (0 : ℝ)) (𝓝 (R^n)) := by
    have hC : Continuous (fun ε : ℝ => (R+ε)^n) := by fun_prop
    simpa only [add_zero] using (hC.tendsto 0).mono_left nhdsWithin_le_nhds
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hpow0 (heps.mono hall)

/-- A single genuine radius-maximizing omitted point works for all positive
inverse coefficient indices. This is an actual Section6 endpoint budget. -/
theorem exteriorOmitted_exists_maximizer_with_inverseCoeff_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ P : ℂ, P ∈ exteriorOmitted F ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P‖) ∧
      ∀ n : ℕ, 1 ≤ n → (n : ℝ)*‖exteriorInverseCoeff F n‖ ≤ ‖P‖^n := by
  obtain ⟨P,hP,hmax⟩ := exteriorOmitted_exists_radius_maximizer F hc
  refine ⟨P,hP,hmax,?_⟩
  intro n hn
  exact exteriorInverseCoeff_mul_norm_le_of_omitted_radius F hc (norm_nonneg P)
    (fun w hw => hmax w (subset_convexHull ℝ _ hw)) n hn

end SpringerLean
