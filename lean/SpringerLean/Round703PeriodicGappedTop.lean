import SpringerLean.Round702PeriodicLevelMass

open MeasureTheory Set Metric
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- A nonconstant analytic projection will supply the null-level premise.
Continuity, rather than positive measure alone, supplies the included gap.
The cut is placed at a strictly lower value, so both ends are excluded. -/
theorem periodic_superlevel_exists_gapped_representative
    (f : ℝ → ℝ) (hf : Continuous f) {T m : ℝ}
    (hT : 0 < T) (hm : 0 < m) (hmT : m < T)
    (hp : Function.Periodic f T) (ell : ℝ)
    (hlevel : volume {t | f t = ell} = 0)
    (hmass : volume ({t | ell ≤ f t} ∩ Ioc 0 T) = ENNReal.ofReal m) :
    ∃ (q p δ : ℝ) (E : Set ℝ),
      0 < δ ∧ E = {t | ell ≤ f t} ∩ Ioc q (q+T) ∧
      MeasurableSet E ∧ volume E = ENNReal.ofReal m ∧
      Icc (p-δ) (p+δ) ⊆ E ∧ E ⊆ Icc (q+δ) (q+T-δ) := by
  classical
  obtain ⟨q, hq⟩ := periodic_superlevel_exists_lt f ell hT hm.le hmT hmass
  have hlow : IsOpen {t | f t < ell} := isOpen_lt hf continuous_const
  obtain ⟨eL, heL, hL⟩ := Metric.isOpen_iff.mp hlow q hq
  have hqT : f (q+T) < ell := by rw [hp q]; exact hq
  obtain ⟨eR, heR, hR⟩ := Metric.isOpen_iff.mp hlow (q+T) hqT
  let d0 : ℝ := min eL eR / 2
  have hd0 : 0 < d0 := by dsimp [d0]; positivity
  have hdL : d0 ≤ eL := by dsimp [d0]; linarith [min_le_left eL eR, lt_min heL heR]
  have hdR : d0 ≤ eR := by dsimp [d0]; linarith [min_le_right eL eR, lt_min heL heR]
  let E : Set ℝ := {t | ell ≤ f t} ∩ Ioc q (q+T)
  have hEm : MeasurableSet E :=
    (measurableSet_le measurable_const hf.measurable).inter measurableSet_Ioc
  have hmassE : volume E = ENNReal.ofReal m :=
    (periodic_superlevel_turn_volume f hf hT hp ell q).trans hmass
  have hgap : E ⊆ Icc (q+d0) (q+T-d0) := by
    intro t ht
    obtain ⟨htop, htq, htT⟩ := ht
    constructor
    · by_contra hn
      have hb : t ∈ ball q eL := by
        rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr htq)]
        linarith [lt_of_not_ge hn]
      exact (not_lt_of_ge (show ell ≤ f t from htop))
        (show f t < ell from hL hb)
    · by_contra hn
      have hb : t ∈ ball (q+T) eR := by
        rw [mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr htT)]
        linarith [lt_of_not_ge hn]
      exact (not_lt_of_ge (show ell ≤ f t from htop))
        (show f t < ell from hR hb)
  have hpExists : ∃ p ∈ E, ell < f p := by
    by_contra hn
    have hsub : E ⊆ {t | f t = ell} := by
      intro t ht
      exact le_antisymm (le_of_not_gt (fun h => hn ⟨t, ht, h⟩)) ht.1
    have hz : volume E = 0 := le_antisymm
      ((measure_mono hsub).trans (le_of_eq hlevel)) bot_le
    rw [hmassE] at hz
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hm)) hz
  obtain ⟨p, hpE, hpHigh⟩ := hpExists
  obtain ⟨eP, heP, hP⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const hf : IsOpen {t | ell < f t}) p hpHigh
  let δ : ℝ := min (d0/2) (eP/2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδd : δ ≤ d0/2 := min_le_left _ _
  have hδP : δ < eP := by
    have h := min_le_right (d0/2) (eP/2)
    dsimp [δ]
    linarith
  have hpGap := hgap hpE
  refine ⟨q, p, δ, E, hδ, rfl, hEm, hmassE, ?_, ?_⟩
  · intro t ht
    have hb : t ∈ ball p eP := by
      rw [mem_ball, Real.dist_eq]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) hδP
    refine ⟨show ell ≤ f t from (show ell < f t from hP hb).le, ?_, ?_⟩
    · linarith [ht.1, hpGap.1]
    · linarith [ht.2, hpGap.2]
  · intro t ht
    have hg := hgap ht
    exact ⟨by linarith [hg.1], by linarith [hg.2]⟩

end SpringerLean

#print axioms SpringerLean.periodic_superlevel_exists_gapped_representative
