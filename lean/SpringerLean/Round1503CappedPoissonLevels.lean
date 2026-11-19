import SpringerLean.Round1502FlattenedArcTop
import SpringerLean.Round34PoissonComparator

open MeasureTheory Set Filter
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- At every proper Poisson superlevel arc, the actual regularized
boundary top integral lies below the mean-preserving flattened model,
up to the explicit raw-mass error `2q ε`. -/
theorem regularExterior_poisson_level_le_flattened_eventually
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {ε : ℝ} (hε : 0 < ε)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℝ, 0 ≤ q → q < Real.pi →
      let E : Set ℝ :=
        {θ | poissonKernel 0 (r:ℂ) (circleMap 0 1 q) ≤
          poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)}
      let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) (2*Real.pi))
      (∫ θ in E,
        (conj ξ*rescaleExterior (omittedScaleSeq n) F
          (circleMap 0 1 θ)).re ∂μ) ≤
        (∫ θ in centeredAngularArc q,
          cappedAngularCosine (2*Real.sin h/h) h θ) + 2*q*ε := by
  have he := regularExterior_poisson_level_two_caps_eventually
    F hc ξ hξ (2*Real.sin h/h) hcap hε hr0 hr1
  filter_upwards [he] with n hn q hq0 hqpi
  let t : ℝ := poissonKernel 0 (r:ℂ) (circleMap 0 1 q)
  have ht : 0 < t := by
    dsimp [t]
    rw [poissonKernel_centered_cosine_formula hr0.le hr1]
    exact div_pos (by nlinarith [hr0,hr1])
      (centeredPoissonDenominator_pos hr0 hr1 q)
  have htwo := hn t ht
  have hmass := poissonKernel_centered_superlevel_raw_mass
    hr0 hr1 q hq0 hqpi
  have hsin := regularExterior_projected_poisson_superlevel_le_sine
    F hc (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
      ξ hξ hr0 hr1 q hq0 hqpi
  have hmodel := cappedAngularCosine_arc_integral_eq_min
    hh0 hhpi hq0 hqpi
  have hswitch := capped_cosine_top_min_switch
    hh0 hhpi.le hq0 hqpi.le
  dsimp only [t] at htwo
  have hcap' := htwo.2
  rw [hmass] at hcap'
  rw [hswitch] at hmodel
  by_cases hqh : q ≤ h
  · rw [if_pos hqh] at hmodel
    rw [hmodel]
    nlinarith [hcap']
  · rw [if_neg hqh] at hmodel
    rw [hmodel]
    nlinarith [hsin,mul_nonneg hq0 hε.le]

end SpringerLean

#print axioms SpringerLean.regularExterior_poisson_level_le_flattened_eventually
