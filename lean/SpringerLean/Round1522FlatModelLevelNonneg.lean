import SpringerLean.Round1521ActualClippedCircleMoment
import SpringerLean.Round1508AllPoissonLevels

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Every centered Poisson superlevel set has nonnegative total mass
under the mean-preserving flattened cosine comparison. -/
theorem cappedAngularCosine_poisson_level_nonneg
    (h : ℝ) (hh0 : 0 < h) (hhpi : h < Real.pi)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ ∫ θ : ℝ in
      {θ | t ≤ poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)},
      cappedAngularCosine (2*Real.sin h/h) h θ
      ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi))) := by
  let I : Set ℝ := Ioc (0:ℝ) (2*Real.pi)
  let μ : Measure ℝ := volume.restrict I
  let u : ℝ → ℝ := cappedAngularCosine (2*Real.sin h/h) h
  let E : Set ℝ :=
    {θ | t ≤ poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)}
  let a : ℝ := ((1+r^2)*t-(1-r^2))/(r*t)
  have hEm : MeasurableSet E :=
    measurableSet_le measurable_const
      (centeredPoisson_weight_continuous hr0 hr1).measurable
  have hIm : MeasurableSet I := measurableSet_Ioc
  have hbal : 2*h*(2*Real.sin h/h)=4*Real.sin h := by
    field_simp
    ring
  change 0 ≤ ∫ θ in E, u θ ∂μ
  by_cases haLo : a ≤ -2
  · have hfull := centeredPoisson_level_full_of_low_threshold
      hr0 hr1 ht a rfl haLo
    have hEq : I ∩ E = I ∩ I := by
      dsimp [I,E] at hfull ⊢
      rw [hfull,inter_self]
    have huEq := oneTurn_setIntegral_congr_inter E I hEm hIm hEq u
    have huZero := cappedAngularCosine_full_turn_zero hh0 hhpi hbal
    have huZero' : (∫ θ in I, u θ ∂μ) = 0 := by
      have hr : (∫ θ in I, u θ ∂μ) = ∫ θ in I, u θ := by
        dsimp [μ]
        rw [Measure.restrict_restrict_of_subset (subset_refl I)]
      rw [hr]
      exact huZero
    rw [huEq,huZero']
  by_cases haHi : 2 < a
  · have hempty := centeredPoisson_level_empty_of_high_threshold
      hr0 hr1 ht a rfl haHi
    have hEq : I ∩ E = I ∩ (∅ : Set ℝ) := by
      dsimp [I,E] at hempty ⊢
      rw [hempty]
      simp
    have huEq := oneTurn_setIntegral_congr_inter E ∅ hEm MeasurableSet.empty hEq u
    rw [huEq,setIntegral_empty]
  · have haLo' : -2 < a := lt_of_not_ge haLo
    have haHi' : a ≤ 2 := le_of_not_gt haHi
    let q : ℝ := Real.arccos (a/2)
    obtain ⟨hq0,hqpi,hEq⟩ := centeredPoisson_proper_level_eq_arc
      hr0 hr1 ht a rfl haLo' haHi'
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
    have hmodel := cappedAngularCosine_arc_integral_eq_min
      hh0 hhpi hq0 hqpi
    have hR : 0 ≤ 2*Real.sin h/h := by
      exact (div_pos (mul_pos (by norm_num)
        (Real.sin_pos_of_pos_of_lt_pi hh0 hhpi)) hh0).le
    have hsinq : 0 ≤ Real.sin q :=
      Real.sin_nonneg_of_nonneg_of_le_pi hq0 hqpi.le
    have hqR : 0 ≤ 2*q*(2*Real.sin h/h) := by positivity
    rw [huEq,huArc,hmodel]
    exact le_min hqR (by positivity)

end SpringerLean

#print axioms SpringerLean.cappedAngularCosine_poisson_level_nonneg
