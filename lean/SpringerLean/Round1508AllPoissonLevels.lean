import SpringerLean.Round1507OneTurnRestriction

open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The cap comparison on proper arcs, the empty/full threshold cases,
and the flattened profile's zero mean give one inequality for every
positive Poisson level under the same regularized actual map. -/
theorem regularExterior_all_poisson_levels_le_flattened_eventually
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {ε : ℝ} (hε : 0 < ε)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0 < t →
      let E : Set ℝ :=
        {θ | t ≤ poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)}
      let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) (2*Real.pi))
      (∫ θ in E,
        (conj ξ*rescaleExterior (omittedScaleSeq n) F
          (circleMap 0 1 θ)).re ∂μ) ≤
      (∫ θ in E, cappedAngularCosine (2*Real.sin h/h) h θ ∂μ) +
        ε*μ.real E := by
  let I : Set ℝ := Ioc (0:ℝ) (2*Real.pi)
  let μ : Measure ℝ := volume.restrict I
  let u : ℝ → ℝ := cappedAngularCosine (2*Real.sin h/h) h
  have hbal : 2*h*(2*Real.sin h/h)=4*Real.sin h := by
    field_simp
    ring
  have he := regularExterior_poisson_level_le_flattened_eventually
    F hc ξ hξ h hh0 hhpi hcap hε hr0 hr1
  filter_upwards [he] with n hn t ht
  let E : Set ℝ :=
    {θ | t ≤ poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)}
  let f : ℝ → ℝ := fun θ =>
    (conj ξ*rescaleExterior (omittedScaleSeq n) F
      (circleMap 0 1 θ)).re
  let a : ℝ := ((1+r^2)*t-(1-r^2))/(r*t)
  have hEm : MeasurableSet E :=
    measurableSet_le measurable_const
      (centeredPoisson_weight_continuous hr0 hr1).measurable
  have hIm : MeasurableSet I := measurableSet_Ioc
  have hμ0 : 0 ≤ μ.real E := by positivity
  by_cases haLo : a ≤ -2
  · have hfull := centeredPoisson_level_full_of_low_threshold
      hr0 hr1 ht a rfl haLo
    have hEq : I ∩ E = I ∩ I := by
      dsimp [I,E] at hfull ⊢
      rw [hfull,inter_self]
    have hfEq := oneTurn_setIntegral_congr_inter E I hEm hIm hEq f
    have huEq := oneTurn_setIntegral_congr_inter E I hEm hIm hEq u
    have hfZero := regularExterior_projected_raw_turn_zero
      F hc (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) ξ
    have huZero := cappedAngularCosine_full_turn_zero hh0 hhpi hbal
    have hfZero' : (∫ θ in I, f θ ∂μ) = 0 := by
      have hr : (∫ θ in I, f θ ∂μ) = ∫ θ in I, f θ := by
        dsimp [μ]
        rw [Measure.restrict_restrict_of_subset (subset_refl I)]
      rw [hr]
      exact hfZero
    have huZero' : (∫ θ in I, u θ ∂μ) = 0 := by
      have hr : (∫ θ in I, u θ ∂μ) = ∫ θ in I, u θ := by
        dsimp [μ]
        rw [Measure.restrict_restrict_of_subset (subset_refl I)]
      rw [hr]
      exact huZero
    change (∫ θ in E, f θ ∂μ) ≤
      (∫ θ in E, u θ ∂μ)+ε*μ.real E
    rw [hfEq,huEq,hfZero',huZero']
    simpa only [zero_add] using mul_nonneg hε.le hμ0
  by_cases haHi : 2 < a
  · have hempty := centeredPoisson_level_empty_of_high_threshold
      hr0 hr1 ht a rfl haHi
    have hEq : I ∩ E = I ∩ (∅ : Set ℝ) := by
      dsimp [I,E] at hempty ⊢
      rw [hempty]
      simp
    have hfEq := oneTurn_setIntegral_congr_inter E ∅ hEm MeasurableSet.empty hEq f
    have huEq := oneTurn_setIntegral_congr_inter E ∅ hEm MeasurableSet.empty hEq u
    change (∫ θ in E, f θ ∂μ) ≤
      (∫ θ in E, u θ ∂μ)+ε*μ.real E
    rw [hfEq,huEq,setIntegral_empty,setIntegral_empty]
    simpa only [zero_add] using mul_nonneg hε.le hμ0
  · have haLo' : -2 < a := lt_of_not_ge haLo
    have haHi' : a ≤ 2 := le_of_not_gt haHi
    let q : ℝ := Real.arccos (a/2)
    obtain ⟨hq0,hqpi,hEq⟩ := centeredPoisson_proper_level_eq_arc
      hr0 hr1 ht a rfl haLo' haHi'
    have hcos : 2*Real.cos q = a := by
      dsimp [q]
      rw [Real.cos_arccos (by linarith) (by linarith)]
      ring
    have htEq : t = poissonKernel 0 (r:ℂ) (circleMap 0 1 q) :=
      centeredPoisson_threshold_eq_of_cosine_parameter
        hr0 hr1 ht (by rw [hcos])
    have hq := hn q hq0 hqpi
    rw [←htEq] at hq
    have hArcSub : centeredAngularArc q ⊆ I := by
      intro θ hθ
      rcases hθ with hl|hr
      · exact ⟨hl.1,by linarith [hl.2]⟩
      · exact ⟨by linarith [hr.1],hr.2⟩
    have hEq2 : I ∩ E = I ∩ centeredAngularArc q := by
      dsimp [I,E] at hEq ⊢
      rw [hEq,inter_eq_right.mpr hArcSub]
    have hArcMeas : MeasurableSet (centeredAngularArc q) :=
      measurableSet_Ioc.union measurableSet_Icc
    have huEq := oneTurn_setIntegral_congr_inter E
      (centeredAngularArc q) hEm hArcMeas hEq2 u
    have huArc : (∫ θ in centeredAngularArc q, u θ ∂μ) =
        ∫ θ in centeredAngularArc q, u θ := by
      dsimp [μ]
      rw [Measure.restrict_restrict_of_subset hArcSub]
    have hmass := poissonKernel_centered_superlevel_raw_mass
      hr0 hr1 q hq0 hqpi
    rw [←htEq] at hmass
    change μ.real E=2*q at hmass
    change (∫ θ in E, f θ ∂μ) ≤
      (∫ θ in E, u θ ∂μ)+ε*μ.real E
    rw [huEq,huArc,hmass]
    nlinarith [hq]

end SpringerLean

#print axioms SpringerLean.regularExterior_all_poisson_levels_le_flattened_eventually
