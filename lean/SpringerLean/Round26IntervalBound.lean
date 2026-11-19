import SpringerLean.Round26IntervalShift

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace SpringerLean

/-- The positive part of the signed indicator difference is precisely the
indicator of the right-translation difference. -/
theorem realSet_indicator_sub_le_sdiff_indicator
    (E : Set ℝ) (d t : ℝ) :
    realSetIndicator E t - realSetIndicator E (t - d) ≤
      realSetIndicator (E \ verticalShiftPlus E d) t := by
  by_cases htE : t ∈ E
  · by_cases htshift : t - d ∈ E
    · simp [realSetIndicator, verticalShiftPlus, htE, htshift, Set.indicator]
    · simp [realSetIndicator, verticalShiftPlus, htE, htshift, Set.indicator]
  · by_cases htshift : t - d ∈ E
    · simp [realSetIndicator, verticalShiftPlus, htE, htshift, Set.indicator]
    · simp [realSetIndicator, verticalShiftPlus, htE, htshift, Set.indicator]

/-- On each oriented interval the signed translation difference is
bounded by the local mass of `E \ (E+d)`. -/
theorem realSet_interval_shift_le_local_sdiff
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a b d : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, realSetIndicator E t - realSetIndicator E (t - d)) ≤
      ∫ t in Ioc a b,
        realSetIndicator (E \ verticalShiftPlus E d) t := by
  have hp : Integrable (realSetIndicator E) :=
    realSetIndicator_integrable E hE hEb
  have hps : Integrable (fun t : ℝ => realSetIndicator E (t - d)) :=
    hp.comp_sub_right d
  have hSmeas : MeasurableSet (E \ verticalShiftPlus E d) :=
    hE.diff (verticalShiftPlus_measurable hE d)
  have hSb : Bornology.IsBounded (E \ verticalShiftPlus E d) :=
    hEb.subset sdiff_subset
  have hq : Integrable (realSetIndicator (E \ verticalShiftPlus E d)) :=
    realSetIndicator_integrable _ hSmeas hSb
  have hle := intervalIntegral.integral_mono hab
    (hp.intervalIntegrable.sub hps.intervalIntegrable)
    hq.intervalIntegrable
    (fun t => realSet_indicator_sub_le_sdiff_indicator E d t)
  simpa only [intervalIntegral.integral_of_le hab] using hle

/-- A single interval contribution is at most the total mass lost under
translation. -/
theorem realSet_interval_shift_le_sdiff
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a b d : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, realSetIndicator E t - realSetIndicator E (t - d)) ≤
      volume.real (E \ verticalShiftPlus E d) := by
  let S : Set ℝ := E \ verticalShiftPlus E d
  let q := realSetIndicator S
  have hSmeas : MeasurableSet S :=
    hE.diff (verticalShiftPlus_measurable hE d)
  have hSb : Bornology.IsBounded S := hEb.subset sdiff_subset
  have hq : Integrable q := realSetIndicator_integrable S hSmeas hSb
  have hqnonneg : ∀ t : ℝ, 0 ≤ q t := by
    intro t
    by_cases ht : t ∈ S <;> simp [q, realSetIndicator, ht]
  have hlocal := realSet_interval_shift_le_local_sdiff E hE hEb a b d hab
  have hglobal : (∫ t in Ioc a b, q t) ≤ ∫ t : ℝ, q t :=
    setIntegral_le_integral hq (ae_of_all _ hqnonneg)
  have htotal : (∫ t : ℝ, q t) = volume.real S :=
    integral_indicator_one hSmeas
  dsimp [q, S] at hglobal htotal
  linarith

/-- The two separated interval contributions share a single global
difference-mass bound; no factor of two is lost. -/
theorem realSet_two_interval_shift_le_sdiff
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a₁ b₁ a₂ b₂ d : ℝ)
    (hab₁ : a₁ ≤ b₁) (hsep : b₁ ≤ a₂) (hab₂ : a₂ ≤ b₂) :
    (∫ t in a₁..b₁, realSetIndicator E t - realSetIndicator E (t - d)) +
      (∫ t in a₂..b₂, realSetIndicator E t - realSetIndicator E (t - d)) ≤
        volume.real (E \ verticalShiftPlus E d) := by
  let S : Set ℝ := E \ verticalShiftPlus E d
  let q := realSetIndicator S
  have hSmeas : MeasurableSet S :=
    hE.diff (verticalShiftPlus_measurable hE d)
  have hSb : Bornology.IsBounded S := hEb.subset sdiff_subset
  have hq : Integrable q := realSetIndicator_integrable S hSmeas hSb
  have hqnonneg : ∀ t : ℝ, 0 ≤ q t := by
    intro t
    by_cases ht : t ∈ S
    · simp [q, realSetIndicator, Set.indicator, ht]
    · simp [q, realSetIndicator, Set.indicator, ht]
  have hdisj : Disjoint (Ioc a₁ b₁) (Ioc a₂ b₂) := by
    apply disjoint_left.mpr
    intro t ht₁ ht₂
    have h1 : t ≤ b₁ := ht₁.2
    have h2 : a₂ < t := ht₂.1
    linarith
  have hle₁ := realSet_interval_shift_le_local_sdiff E hE hEb a₁ b₁ d hab₁
  have hle₂ := realSet_interval_shift_le_local_sdiff E hE hEb a₂ b₂ d hab₂
  have hunion :
      (∫ t in Ioc a₁ b₁, q t) + (∫ t in Ioc a₂ b₂, q t) =
        ∫ t in (Ioc a₁ b₁ ∪ Ioc a₂ b₂), q t := by
    exact (setIntegral_union hdisj measurableSet_Ioc
      hq.integrableOn hq.integrableOn).symm
  have hglobal : (∫ t in (Ioc a₁ b₁ ∪ Ioc a₂ b₂), q t) ≤
      ∫ t : ℝ, q t :=
    setIntegral_le_integral hq (ae_of_all _ hqnonneg)
  have htotal : (∫ t : ℝ, q t) = volume.real S := by
    exact integral_indicator_one hSmeas
  dsimp [S, q] at hunion hglobal htotal
  linarith

end SpringerLean
