import SpringerLean.Round36WeightedLayer

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The centered Poisson denominator is positive on every angle. -/
theorem centeredPoissonDenominator_pos
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    0 < 1 + r^2 - 2*r*Real.cos θ := by
  have hc := Real.cos_le_one θ
  have hs : 0 < (1-r)^2 := sq_pos_of_pos (sub_pos.mpr hr1)
  nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr hc)]

/-- Every positive kernel threshold is exactly a comparator projection
threshold, even when its superlevel set is empty or the full circle. -/
theorem centeredPoisson_superlevel_iff_comparator_superlevel
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    t ≤ poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) ↔
      (((1+r^2)*t-(1-r^2))/(r*t)) ≤ 2*Real.cos θ := by
  rw [poissonKernel_centered_cosine_formula hr0.le hr1]
  have hd := centeredPoissonDenominator_pos hr0 hr1 θ
  have hrt : 0 < r*t := mul_pos hr0 ht
  constructor
  · intro h
    have h' : t*(1+r^2-2*r*Real.cos θ) ≤ 1-r^2 :=
      (le_div_iff₀ hd).mp h
    apply (div_le_iff₀ hrt).mpr
    nlinarith
  · intro h
    have h' : ((1+r^2)*t-(1-r^2)) ≤ (2*Real.cos θ)*(r*t) :=
      (div_le_iff₀ hrt).mp h
    apply (le_div_iff₀ hd).mpr
    nlinarith

/-- The centered Poisson weight is nonnegative and bounded by its peak. -/
theorem centeredPoisson_weight_bounds
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    0 ≤ poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) ∧
      poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) ≤
        (1-r^2)/(1-r)^2 := by
  rw [poissonKernel_centered_cosine_formula hr0.le hr1]
  have hn : 0 < 1-r^2 := by nlinarith
  have hd := centeredPoissonDenominator_pos hr0 hr1 θ
  have hs : 0 < (1-r)^2 := sq_pos_of_pos (sub_pos.mpr hr1)
  have hden : (1-r)^2 ≤ 1+r^2-2*r*Real.cos θ := by
    nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr (Real.cos_le_one θ))]
  constructor
  · exact div_nonneg hn.le hd.le
  · apply (div_le_div_iff₀ hd hs).mpr
    exact mul_le_mul_of_nonneg_left hden hn.le


/-- The original F, not an abstract boundary function, obeys the sharp
comparison on every centered Poisson-kernel superlevel set. -/
theorem regularExterior_projected_poisson_level_le_comparator
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {t : ℝ} (ht : 0 < t) :
    (∫ θ in {θ : ℝ | t ≤ poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)},
      (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re
        ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) ≤
    (∫ θ in {θ : ℝ | t ≤ poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)},
      2 * (circleMap 0 1 θ).re
        ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  let a : ℝ := ((1+r^2)*t-(1-r^2))/(r*t)
  let A : Set ℝ :=
    {θ : ℝ | t ≤ poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)}
  have hset : A = {θ : ℝ | a ≤ 2 * (circleMap 0 1 θ).re} := by
    ext θ
    simpa [A, a, circleMap_zero_re] using
      centeredPoisson_superlevel_iff_comparator_superlevel hr0 hr1 ht θ
  have hA : MeasurableSet A := by
    rw [hset]
    have hc : Continuous (fun θ : ℝ => 2 * (circleMap 0 1 θ).re) := by fun_prop
    exact measurableSet_Ici.preimage hc.measurable
  have hmass :
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real A =
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real
        {θ : ℝ | a ≤ 2 * (circleMap 0 1 θ).re} := by rw [hset]
  have h := regularExterior_projected_set_le_comparator_superlevel
    F hc hs0 hs1 ξ hξ a A hA hmass
  rw [← hset] at h
  exact h
end SpringerLean