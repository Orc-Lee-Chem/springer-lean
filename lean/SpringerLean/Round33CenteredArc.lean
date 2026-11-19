import SpringerLean.Round32SignApplications

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- A centered angular arc of half-width q, represented in (0,2π]. -/
def centeredAngularArc (q : ℝ) : Set ℝ :=
  Ioc 0 q ∪ Icc (2 * Real.pi - q) (2 * Real.pi)

/-- The comparator's upper level set is exactly the centered arc within one turn. -/
theorem comparator_superlevel_inter_turn_eq_centeredAngularArc
    (q : ℝ) (hq0 : 0 ≤ q) (hqpi : q ≤ Real.pi) :
    (Ioc (0 : ℝ) (2 * Real.pi) ∩
      {θ : ℝ | 2 * Real.cos q ≤ 2 * (circleMap 0 1 θ).re}) =
      centeredAngularArc q := by
  ext θ
  have hreal : (circleMap 0 1 θ).re = Real.cos θ := by
    simp [circleMap_zero_re]
  simp only [mem_inter_iff, mem_setOf_eq, hreal,
    centeredAngularArc, mem_union, mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨⟨hθ0, hθ2pi⟩, hcos⟩
    have hcos1 : Real.cos q ≤ Real.cos θ := by linarith
    by_cases hθpi : θ ≤ Real.pi
    · left
      have hq : q ∈ Icc (0:ℝ) Real.pi := ⟨hq0, hqpi⟩
      have hθ : θ ∈ Icc (0:ℝ) Real.pi := ⟨hθ0.le, hθpi⟩
      have hθq : θ ≤ q :=
        (Real.strictAntiOn_cos.le_iff_ge hq hθ).mp hcos1
      exact ⟨hθ0, hθq⟩
    · right
      have hθpi' : Real.pi < θ := lt_of_not_ge hθpi
      have ht : 2 * Real.pi - θ ∈ Icc (0:ℝ) Real.pi := by
        constructor <;> linarith
      have hq : q ∈ Icc (0:ℝ) Real.pi := ⟨hq0, hqpi⟩
      have hcos' : Real.cos q ≤ Real.cos (2 * Real.pi - θ) := by
        rw [Real.cos_two_pi_sub]
        exact hcos1
      have htq : 2 * Real.pi - θ ≤ q :=
        (Real.strictAntiOn_cos.le_iff_ge hq ht).mp hcos'
      exact ⟨by linarith, hθ2pi⟩
  · intro h
    rcases h with hleft | hright
    · have hq : q ∈ Icc (0:ℝ) Real.pi := ⟨hq0, hqpi⟩
      have hθ : θ ∈ Icc (0:ℝ) Real.pi := ⟨hleft.1.le, le_trans hleft.2 hqpi⟩
      refine ⟨⟨hleft.1, ?_⟩, ?_⟩
      · linarith [Real.pi_pos]
      · have hc := (Real.strictAntiOn_cos.le_iff_ge hq hθ).mpr hleft.2
        linarith
    · have hθ0 : 0 < θ := by linarith [Real.pi_pos]
      have ht : 2 * Real.pi - θ ∈ Icc (0:ℝ) Real.pi := by
        constructor <;> linarith [hqpi]
      have hq : q ∈ Icc (0:ℝ) Real.pi := ⟨hq0, hqpi⟩
      refine ⟨⟨hθ0, hright.2⟩, ?_⟩
      have hcos := (Real.strictAntiOn_cos.le_iff_ge hq ht).mpr (by linarith [hright.1])
      rw [Real.cos_two_pi_sub] at hcos
      linarith

/-- The raw angular length of a nondegenerate centered arc is 2q. -/
theorem centeredAngularArc_volume
    (q : ℝ) (hq0 : 0 ≤ q) (hqpi : q < Real.pi) :
    volume (centeredAngularArc q) = ENNReal.ofReal (2 * q) := by
  have hdisj : Disjoint (Ioc (0:ℝ) q) (Icc (2 * Real.pi - q) (2 * Real.pi)) := by
    apply disjoint_left.mpr
    intro θ hleft hright
    have hθq : θ ≤ q := hleft.2
    have hqθ : 2 * Real.pi - q ≤ θ := hright.1
    linarith
  rw [centeredAngularArc, measure_union hdisj measurableSet_Icc,
    Real.volume_Ioc, Real.volume_Icc]
  have hq : 0 ≤ 2 * Real.pi - (2 * Real.pi - q) := by linarith
  simp only [sub_zero]
  rw [← ENNReal.ofReal_add hq0 hq]
  congr 1
  ring
/-- The raw comparator integral over the centered arc is 4 sin q. -/
theorem centeredAngularArc_comparator_integral
    (q : ℝ) (hq0 : 0 ≤ q) (hqpi : q < Real.pi) :
    (∫ θ in centeredAngularArc q, 2 * Real.cos θ) =
      4 * Real.sin q := by
  let f : ℝ → ℝ := fun θ => 2 * Real.cos θ
  have hdisj : Disjoint (Ioc (0:ℝ) q) (Icc (2 * Real.pi - q) (2 * Real.pi)) := by
    apply disjoint_left.mpr
    intro θ hleft hright
    linarith [hleft.2, hright.1]
  have hfi : IntegrableOn f (Ioc (0:ℝ) q) := by
    exact ((by fun_prop : Continuous f).continuousOn.integrableOn_compact
      (isCompact_Icc : IsCompact (Icc (0:ℝ) q))).mono_set Ioc_subset_Icc_self
  have hgi : IntegrableOn f (Icc (2 * Real.pi - q) (2 * Real.pi)) := by
    exact (by fun_prop : Continuous f).continuousOn.integrableOn_compact isCompact_Icc
  rw [centeredAngularArc, setIntegral_union hdisj measurableSet_Icc hfi hgi,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hq0,
    ← intervalIntegral.integral_of_le (by linarith [hq0] : 2 * Real.pi - q ≤ 2 * Real.pi)]
  dsimp [f]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos, integral_cos]
  have hsin : Real.sin (2 * Real.pi - q) = -Real.sin q := by
    rw [Real.sin_two_pi_sub]
  simp only [Real.sin_zero, Real.sin_two_pi, hsin]
  ring
/-- The comparator threshold 2 cos q has raw angular mass 2q. -/
theorem comparator_superlevel_raw_angular_mass
    (q : ℝ) (hq0 : 0 ≤ q) (hqpi : q < Real.pi) :
    (volume.restrict (Ioc (0:ℝ) (2 * Real.pi))).real
      {θ : ℝ | 2 * Real.cos q ≤ 2 * (circleMap 0 1 θ).re} =
      2 * q := by
  let A : Set ℝ := {θ | 2 * Real.cos q ≤ 2 * (circleMap 0 1 θ).re}
  have hAm : MeasurableSet A := by
    have hc : Continuous (fun θ : ℝ => 2 * (circleMap 0 1 θ).re) := by fun_prop
    exact measurableSet_Ici.preimage hc.measurable
  change ((volume.restrict (Ioc (0:ℝ) (2*Real.pi))) A).toReal = 2*q
  rw [Measure.restrict_apply hAm, inter_comm,
    comparator_superlevel_inter_turn_eq_centeredAngularArc q hq0 hqpi.le,
    centeredAngularArc_volume q hq0 hqpi]
  exact ENNReal.toReal_ofReal (by positivity)
/-- The comparator's actual restricted-measure upper-level integral. -/
theorem comparator_superlevel_raw_integral
    (q : ℝ) (hq0 : 0 ≤ q) (hqpi : q < Real.pi) :
    (∫ θ in {θ : ℝ | 2 * Real.cos q ≤ 2 * (circleMap 0 1 θ).re},
        2 * (circleMap 0 1 θ).re
        ∂(volume.restrict (Ioc (0:ℝ) (2 * Real.pi)))) =
      4 * Real.sin q := by
  let A : Set ℝ := {θ | 2 * Real.cos q ≤ 2 * (circleMap 0 1 θ).re}
  have hAm : MeasurableSet A := by
    have hc : Continuous (fun θ : ℝ => 2 * (circleMap 0 1 θ).re) := by fun_prop
    exact measurableSet_Ici.preimage hc.measurable
  have hfun : (fun θ : ℝ => 2 * (circleMap 0 1 θ).re) =
      (fun θ : ℝ => 2 * Real.cos θ) := by
    funext θ
    simp [circleMap_zero_re]
  change ∫ θ in A, 2 * (circleMap 0 1 θ).re
      ∂(volume.restrict (Ioc (0:ℝ) (2 * Real.pi))) =
    4 * Real.sin q
  rw [hfun]
  change ∫ θ : ℝ, 2 * Real.cos θ
      ∂((volume.restrict (Ioc (0:ℝ) (2*Real.pi))).restrict A) =
    4 * Real.sin q
  rw [Measure.restrict_restrict hAm, inter_comm,
    comparator_superlevel_inter_turn_eq_centeredAngularArc q hq0 hqpi.le]
  exact centeredAngularArc_comparator_integral q hq0 hqpi
end SpringerLean