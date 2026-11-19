import SpringerLean.Round26IntervalBound

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace SpringerLean

/-- Two separated transitions of the primitive, each from derivative zero
to derivative one, force the translation difference to have at least the
translation length for every sufficiently small positive translation. -/
theorem realSet_shift_sdiff_lower_of_two_derivative_pairs
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a₁ b₁ a₂ b₂ : ℝ)
    (hab₁ : a₁ < b₁) (hsep : b₁ < a₂) (hab₂ : a₂ < b₂)
    (ha₁ : HasDerivAt (realSetPrimitive E) 0 a₁)
    (hb₁ : HasDerivAt (realSetPrimitive E) 1 b₁)
    (ha₂ : HasDerivAt (realSetPrimitive E) 0 a₂)
    (hb₂ : HasDerivAt (realSetPrimitive E) 1 b₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ, 0 < d → d < δ →
      d ≤ volume.real (E \ verticalShiftPlus E d) := by
  let q (x d : ℝ) : ℝ :=
    (realSetPrimitive E x - realSetPrimitive E (x - d)) / d
  have hqa₁ : Tendsto (q a₁) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    SpringerLean.HasDerivAt.tendsto_left_difference_quotient ha₁
  have hqb₁ : Tendsto (q b₁) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    SpringerLean.HasDerivAt.tendsto_left_difference_quotient hb₁
  have hqa₂ : Tendsto (q a₂) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    SpringerLean.HasDerivAt.tendsto_left_difference_quotient ha₂
  have hqb₂ : Tendsto (q b₂) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    SpringerLean.HasDerivAt.tendsto_left_difference_quotient hb₂
  let K : ℝ → ℝ := fun d => (q b₁ d - q a₁ d) + (q b₂ d - q a₂ d)
  have hK : Tendsto K (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    convert (hqb₁.sub hqa₁).add (hqb₂.sub hqa₂) using 1 <;> norm_num [K]
  have hev : ∀ᶠ d in 𝓝[>] (0 : ℝ), (3 / 2 : ℝ) < K d :=
    hK.eventually (eventually_gt_nhds (by norm_num : (3 / 2 : ℝ) < 2))
  obtain ⟨δ, hδ, hδK⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨δ, hδ, ?_⟩
  intro d hd0 hdδ
  have hKbound : (3 / 2 : ℝ) < K d := hδK ⟨hd0, hdδ.le⟩
  have hJ := realSet_two_interval_shift_le_sdiff
    E hE hEb a₁ b₁ a₂ b₂ d hab₁.le hsep.le hab₂.le
  have hJq :
      ((∫ t in a₁..b₁, realSetIndicator E t - realSetIndicator E (t - d)) +
        (∫ t in a₂..b₂, realSetIndicator E t - realSetIndicator E (t - d))) / d = K d := by
    rw [realSet_interval_shift_integral_eq E hE hEb a₁ b₁ d,
      realSet_interval_shift_integral_eq E hE hEb a₂ b₂ d]
    dsimp [K, q]
    ring
  have hJpos : d <
      (∫ t in a₁..b₁, realSetIndicator E t - realSetIndicator E (t - d)) +
        (∫ t in a₂..b₂, realSetIndicator E t - realSetIndicator E (t - d)) := by
    have hquot : 1 <
      ((∫ t in a₁..b₁, realSetIndicator E t - realSetIndicator E (t - d)) +
        (∫ t in a₂..b₂, realSetIndicator E t - realSetIndicator E (t - d))) / d := by
      rw [hJq]
      linarith
    simpa only [one_mul] using (lt_div_iff₀ hd0).mp hquot
  exact (hJpos.trans_le hJ).le

end SpringerLean
