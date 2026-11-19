import SpringerLean.Round22Costs

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SpringerLean

set_option maxHeartbeats 30000

/-- For a finite measurable real set, the left cumulative mass changes by
at most the length of the interval. -/
theorem measureReal_inter_Iic_increment_le
    (S : Set ℝ) (hS : MeasurableSet S) (hfin : volume S ≠ ∞)
    {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ volume.real (S ∩ Iic y) - volume.real (S ∩ Iic x) ∧
      volume.real (S ∩ Iic y) - volume.real (S ∩ Iic x) ≤ y - x := by
  have hset : S ∩ Iic y = (S ∩ Iic x) ∪ (S ∩ Ioc x y) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_union, mem_Ioc]
    constructor
    · rintro ⟨htS, hty⟩
      by_cases htx : t ≤ x
      · exact Or.inl ⟨htS, htx⟩
      · exact Or.inr ⟨htS, lt_of_not_ge htx, hty⟩
    · rintro (ht | ht)
      · exact ⟨ht.1, ht.2.trans hxy⟩
      · exact ⟨ht.1, ht.2.2⟩
  have hdisj : Disjoint (S ∩ Iic x) (S ∩ Ioc x y) := by
    apply disjoint_left.mpr
    intro t ht₁ ht₂
    exact (not_lt_of_ge ht₁.2) ht₂.2.1
  have hfin₁ : volume (S ∩ Iic x) ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfin)).ne
  have hfin₂ : volume (S ∩ Ioc x y) ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfin)).ne
  have hadd : volume.real (S ∩ Iic y) =
      volume.real (S ∩ Iic x) + volume.real (S ∩ Ioc x y) := by
    rw [hset]
    exact measureReal_union hdisj (hS.inter measurableSet_Ioc) hfin₁ hfin₂
  have hbound : volume.real (S ∩ Ioc x y) ≤ y - x := by
    have hmono : volume.real (S ∩ Ioc x y) ≤ volume.real (Ioc x y) :=
      measureReal_mono inter_subset_right (measure_Ioc_lt_top.ne)
    change (volume (S ∩ Ioc x y)).toReal ≤ (volume (Ioc x y)).toReal at hmono
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)] at hmono
    exact hmono
  constructor
  · rw [hadd]
    have hnonneg : 0 ≤ volume.real (S ∩ Ioc x y) := measureReal_nonneg
    linarith
  · rw [hadd]
    linarith

/-- The cumulative mass of a finite measurable real set is 1-Lipschitz. -/
theorem measureReal_inter_Iic_lipschitz
    (S : Set ℝ) (hS : MeasurableSet S) (hfin : volume S ≠ ∞) :
    LipschitzWith 1 (fun x : ℝ => volume.real (S ∩ Iic x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with hxy | hyx
  · obtain ⟨hmono, hbound⟩ :=
      measureReal_inter_Iic_increment_le S hS hfin hxy
    rw [Real.dist_eq, abs_sub_comm
      (volume.real (S ∩ Iic x)) (volume.real (S ∩ Iic y)),
      abs_of_nonneg hmono, Real.dist_eq]
    simp only [NNReal.coe_one, one_mul]
    rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact hbound
  · have h := measureReal_inter_Iic_increment_le S hS hfin hyx
    rw [Real.dist_eq, abs_of_nonneg h.1, Real.dist_eq]
    simp only [NNReal.coe_one, one_mul]
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact h.2

/-- Exact atomless cutting on the real line: every intermediate mass of a
bounded measurable set is attained by intersecting it with a half-line. -/
theorem bounded_measurable_exists_subset_volume_eq
    (S : Set ℝ) (hS : MeasurableSet S) (hSb : Bornology.IsBounded S)
    (q : ℝ) (hq0 : 0 ≤ q) (hqS : q ≤ volume.real S) :
    ∃ T : Set ℝ, MeasurableSet T ∧ T ⊆ S ∧
      volume T = ENNReal.ofReal q := by
  have hfin : volume S ≠ ∞ := hSb.measure_lt_top.ne
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hSb
  let M₀ : ℝ := max M 0
  have hM₀ : ∀ t ∈ S, |t| ≤ M₀ := by
    intro t ht
    exact (show |t| ≤ M from by simpa [Real.norm_eq_abs] using hM t ht).trans
      (le_max_left _ _)
  let L : ℝ := -M₀ - 1
  let U : ℝ := M₀ + 1
  let g : ℝ → ℝ := fun x => volume.real (S ∩ Iic x)
  have hlow : S ∩ Iic L = ∅ := by
    ext t
    constructor
    · intro ht
      have htM := hM₀ t ht.1
      have hleft := (abs_le.mp htM).1
      have htL : t ≤ L := ht.2
      dsimp [L] at htL
      linarith
    · simp
  have hupp : S ∩ Iic U = S := by
    apply inter_eq_left.mpr
    intro t htS
    have htM := hM₀ t htS
    have hright := (abs_le.mp htM).2
    change t ≤ U
    dsimp [U]
    linarith
  have hgL : g L = 0 := by simp [g, hlow]
  have hgU : g U = volume.real S := by simp [g, hupp]
  have hLU : L ≤ U := by
    dsimp [L, U, M₀]
    have h0 : 0 ≤ max M 0 := le_max_right _ _
    linarith
  have hcont : ContinuousOn g (Icc L U) :=
    ((measureReal_inter_Iic_lipschitz S hS hfin).continuous).continuousOn
  have hmem : q ∈ Icc (g L) (g U) := by
    rw [hgL, hgU]
    exact ⟨hq0, hqS⟩
  obtain ⟨u, hu, hgu⟩ := (intermediate_value_Icc hLU hcont) hmem
  let T : Set ℝ := S ∩ Iic u
  refine ⟨T, hS.inter measurableSet_Iic, inter_subset_left, ?_⟩
  have hTfin : volume T ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfin)).ne
  have hqT : q = volume.real T := hgu.symm
  rw [hqT, Measure.real_def]
  exact (ENNReal.ofReal_toReal hTfin).symm

end SpringerLean
