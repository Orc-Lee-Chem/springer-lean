import SpringerLean.Round2110PeriodicThresholdMass
import SpringerLean.Round2111PeriodicPairedTop

open Set MeasureTheory Real
open scoped ENNReal

namespace SpringerLean

/-- Keep all strict superlevels and fill the remaining mass from the
threshold level inside the prescribed cut margins. A strict superlevel
point supplies an included interval. -/
theorem periodicTopIntegral_exists_gapped_of_cut
    (f : ℝ → ℝ) (hf : Continuous f) (T m : ℝ) (hT : 0 < T)
    (hp : Function.Periodic f T) (hm : 0 < m) (hmt : m < T)
    (q a δ : ℝ) (hδ : 0 < δ)
    (hH : ({t | a < f t} ∩ Ioc q (q+T)).Nonempty)
    (hcut : {t | a < f t} ∩ Ioc q (q+T) ⊆ Icc (q+δ) (q+T-δ))
    (hlo : volume.real ({t | a < f t} ∩ Ioc q (q+T)) ≤ m)
    (hhi : m ≤ volume.real ({t | a ≤ f t} ∩ Icc (q+δ) (q+T-δ))) :
    ∃ (p d : ℝ) (E : Set ℝ), 0 < d ∧ MeasurableSet E ∧ volume.real E = m ∧
      Icc (p-d) (p+d) ⊆ E ∧ E ⊆ Icc (q+d) (q+T-d) ∧
      periodicTopIntegral f T m = ∫ t in E, f t := by
  let H := {t | a < f t} ∩ Ioc q (q+T)
  let C := Icc (q+δ) (q+T-δ)
  let L := {t | f t = a} ∩ C
  have hC : C ⊆ Ioc q (q+T) := fun _ ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hHm : MeasurableSet H := (measurableSet_lt measurable_const hf.measurable).inter measurableSet_Ioc
  have hLm : MeasurableSet L := (measurableSet_eq_fun hf.measurable measurable_const).inter measurableSet_Icc
  have hLsub : L ⊆ Ioc q (q+T) := inter_subset_right.trans hC
  have hdis : Disjoint H L := Set.disjoint_left.mpr (fun t ht hu => (ne_of_gt ht.1) hu.1)
  have hweak : H ∪ L = {t | a ≤ f t} ∩ C := by
    ext t
    refine ⟨?_,?_⟩
    · rintro (ht | ht)
      · exact ⟨(show a < f t from ht.1).le,hcut ht⟩
      · exact ⟨(show f t = a from ht.1).ge,ht.2⟩
    · intro ht
      rcases lt_or_eq_of_le (show a ≤ f t from ht.1) with h | h
      · exact Or.inl ⟨h,hC ht.2⟩
      · exact Or.inr ⟨h.symm,ht.2⟩
  have hfin (A : Set ℝ) (hA : A ⊆ Ioc q (q+T)) : volume A ≠ ∞ :=
    ((Metric.isBounded_Ioc _ _).subset hA).measure_lt_top.ne
  have hs : m-volume.real H ≤ volume.real L := by
    rw [←hweak,measureReal_union hdis hLm (hfin H inter_subset_right) (hfin L hLsub)] at hhi
    linarith only [hhi]
  obtain ⟨c,_,hc⟩ := exists_angular_level_slice L hLm (by linarith : q ≤ q+T) hLsub
    (sub_nonneg.mpr hlo) hs
  let L' := L ∩ Ioc q c
  let E := H ∪ L'
  have hL'm : MeasurableSet L' := hLm.inter measurableSet_Ioc
  have hEm : MeasurableSet E := hHm.union hL'm
  have hEC : E ⊆ C := union_subset hcut (inter_subset_left.trans inter_subset_right)
  have hEI : E ⊆ Ioc q (q+T) := hEC.trans hC
  have hEvol : volume.real E = m := by
    rw [show E = H ∪ L' from rfl, measureReal_union (hdis.mono_right inter_subset_left) hL'm
      (hfin H inter_subset_right) (hfin L' (inter_subset_left.trans hLsub)),hc]
    ring
  have hval : periodicTopIntegral f T m = ∫ t in E, f t := by
    apply periodicTopIntegral_eq_of_threshold_set f hf T m hT hp hm.le hmt.le q a E hEm hEI hEvol
    · intro t ht
      rcases ht with ht | ht
      · exact (show a < f t from ht.1).le
      · exact (show f t = a from ht.1.1).ge
    · intro t ht htn
      exact le_of_not_gt (fun hlt => htn (Or.inl ⟨hlt,ht⟩))
  obtain ⟨p,hpH⟩ := hH
  let O := {t | a < f t} ∩ Ioo q (q+T)
  have hO : IsOpen O := (isOpen_lt continuous_const hf).inter isOpen_Ioo
  have hpO : p ∈ O := by
    have h := hcut hpH
    exact ⟨hpH.1, by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨r,hr,hrO⟩ := Metric.isOpen_iff.mp hO p hpO
  let d := min δ (r/2)
  have hd : 0 < d := lt_min hδ (half_pos hr)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdr : d < r := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨p,d,E,hd,hEm,hEvol,?_,?_,hval⟩
  · intro t ht
    have hdist : dist t p < r := by
      rw [Real.dist_eq]
      exact (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans_lt hdr
    have ho := hrO (Metric.mem_ball.mpr hdist)
    exact Or.inl ⟨ho.1,ho.2.1,ho.2.2.le⟩
  · intro t ht
    have he := hEC ht
    exact ⟨by linarith [he.1],by linarith [he.2]⟩

end SpringerLean
