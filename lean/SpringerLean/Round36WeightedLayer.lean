import SpringerLean.Round35SlitSharpness

open MeasureTheory Set

namespace SpringerLean

variable {M c b : ℝ}

theorem interval_indicator_const_integral (h0 : 0 ≤ c) (hM : c ≤ M) : (∫ t in Ioc (0:ℝ) M, if t ≤ c then b else 0) = c * b := by
  change ∫ t : ℝ, (Iic c).indicator (fun _ => b) t
    ∂(volume.restrict (Ioc (0:ℝ) M)) = c * b
  rw [integral_indicator_const b measurableSet_Iic]
  simp only [smul_eq_mul]
  have hset : Ioc (0:ℝ) M ∩ Iic c = Ioc 0 c := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨ht0,htM⟩, htc⟩
      exact ⟨ht0, htc⟩
    · rintro ⟨ht0,htc⟩
      exact ⟨⟨ht0, htc.trans hM⟩, htc⟩
  change (((volume.restrict (Ioc (0:ℝ) M)) (Iic c)).toReal) * b = c * b
  rw [Measure.restrict_apply measurableSet_Iic, inter_comm (Iic c) (Ioc 0 M), hset, Real.volume_Ioc]
  simp [ENNReal.toReal_ofReal h0]
theorem bounded_indicator_prod_integrable
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (f w : α → ℝ) (hf : Measurable f) (hw : Measurable w)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ B) :
    Integrable (fun p : α × ℝ => if p.2 ≤ w p.1 then f p.1 else 0)
      (μ.prod ν) := by
  have hcond : MeasurableSet {p : α × ℝ | p.2 ≤ w p.1} :=
    measurableSet_le measurable_snd (hw.comp measurable_fst)
  have hms : Measurable (fun p : α × ℝ => if p.2 ≤ w p.1 then f p.1 else 0) :=
    Measurable.ite hcond (hf.comp measurable_fst) measurable_const
  apply Integrable.mono' (g := fun _ : α × ℝ => B) (integrable_const B)
    hms.aestronglyMeasurable
  filter_upwards [] with p
  by_cases h : p.2 ≤ w p.1 <;> simp [h, Real.norm_eq_abs, hbound, hB]
theorem bounded_weighted_layercake_identity
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (h w : α → ℝ) (hh : Measurable h) (hw : Measurable w)
    (B M : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |h x| ≤ B)
    (hw0 : ∀ x, 0 ≤ w x) (hwM : ∀ x, w x ≤ M) :
    (∫ x, h x * w x ∂μ) =
      ∫ t in Ioc (0:ℝ) M, ∫ x in {x | t ≤ w x}, h x ∂μ := by
  let ν : Measure ℝ := volume.restrict (Ioc (0:ℝ) M)
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  have hp : Integrable (fun p : α × ℝ =>
      if p.2 ≤ w p.1 then h p.1 else 0) (μ.prod ν) :=
    bounded_indicator_prod_integrable μ ν h w hh hw B hB hbound
  calc
    (∫ x, h x * w x ∂μ) =
      ∫ x, ∫ t, (if t ≤ w x then h x else 0) ∂ν ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hs := interval_indicator_const_integral (b := h x) (hw0 x) (hwM x)
        change (∫ t, (if t ≤ w x then h x else 0) ∂ν) = w x * h x at hs
        rw [hs]
        ring
    _ = ∫ t, ∫ x, (if t ≤ w x then h x else 0) ∂μ ∂ν :=
      integral_integral_swap hp
    _ = ∫ t in Ioc (0:ℝ) M, ∫ x in {x | t ≤ w x}, h x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hset : MeasurableSet {x : α | t ≤ w x} :=
        measurableSet_le measurable_const hw
      change ∫ x, ({x : α | t ≤ w x}).indicator h x ∂μ = _
      exact integral_indicator hset
theorem bounded_weighted_integral_nonpos_of_levels
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (h w : α → ℝ) (hh : Measurable h) (hw : Measurable w)
    (B M : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |h x| ≤ B)
    (hw0 : ∀ x, 0 ≤ w x) (hwM : ∀ x, w x ≤ M)
    (hlevels : ∀ t : ℝ, 0 < t → t ≤ M →
      (∫ x in {x | t ≤ w x}, h x ∂μ) ≤ 0) :
    (∫ x, h x * w x ∂μ) ≤ 0 := by
  rw [bounded_weighted_layercake_identity μ h w hh hw B M hB hbound hw0 hwM]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hlevels t ht.1 ht.2
end SpringerLean
