import SpringerLean.Round1511RegularFillingCap

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The genuine harmonic filling obeys the sharpened pointwise capped
Poisson bound at every positive real source radius. The regularization
and epsilon limits are both discharged from the actual mapping class. -/
theorem actualHarmonic_flattened_pointwise_cap
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (conj ξ*actualHarmonic F (r:ℂ)).re ≤
      flattenedCosinePoissonAtReal h r := by
  let K : ℝ := centeredPoissonRawMass r
  have hz : ‖(r:ℂ)‖ < 1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0] using hr1
  have hs : Tendsto omittedScaleSeq atTop (𝓝[<] (1:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨omittedScaleSeq_tendsto_one,
      Eventually.of_forall omittedScaleSeq_lt_one⟩
  have hreg : Tendsto
      (fun n : ℕ => regularHarmonic (omittedScaleSeq n) F (r:ℂ))
      atTop (𝓝 (actualHarmonic F (r:ℂ))) := by
    simpa only [actualHarmonic,Function.comp_def] using
      (regularHarmonic_tendsto F hc hz).comp hs
  have hcont : Continuous (fun z : ℂ => (conj ξ*z).re) := by fun_prop
  have hproj : Tendsto
      (fun n : ℕ => (conj ξ*regularHarmonic (omittedScaleSeq n) F (r:ℂ)).re)
      atTop (𝓝 ((conj ξ*actualHarmonic F (r:ℂ)).re)) :=
    (hcont.tendsto _).comp hreg
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hden : 0 < |K|+1 := by positivity
  let ε : ℝ := δ/(|K|+1)
  have hε : 0 < ε := div_pos hδ hden
  have he := regularHarmonic_flattened_cap_eventually
    F hc ξ hξ h hh0 hhpi hcap hε hr0 hr1
  have hlim : (conj ξ*actualHarmonic F (r:ℂ)).re ≤
      flattenedCosinePoissonAtReal h r + ε*K :=
    le_of_tendsto_of_tendsto hproj tendsto_const_nhds he
  have hKle : K ≤ |K| := le_abs_self K
  have hm := mul_le_mul_of_nonneg_left hKle hε.le
  have hid : ε*(|K|+1)=δ := by
    dsimp [ε]
    field_simp
  dsimp [K] at hlim ⊢
  change (conj ξ*actualHarmonic F (r:ℂ)).re ≤
    flattenedCosinePoissonAtReal h r+δ
  dsimp [K] at hm hid
  linarith

end SpringerLean

#print axioms SpringerLean.actualHarmonic_flattened_pointwise_cap
