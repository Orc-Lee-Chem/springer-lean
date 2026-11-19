import SpringerLean.Round689PeriodicThreshold

open MeasureTheory Set Real
open scoped ENNReal

namespace SpringerLean

/-- A dual formula for the integral of the top mass `m` in a single
period. It applies to continuous periodic functions with level plateaux. -/
noncomputable def periodicTopIntegral (f : ℝ → ℝ) (T m : ℝ) : ℝ :=
  sInf (Set.range (fun a : ℝ => a*m + ∫ t in Ioc 0 T, max (f t-a) 0))

private theorem periodicTopIntegral_bddBelow
    (f : ℝ → ℝ) (hf : Continuous f) (T m : ℝ) (hT : 0 < T)
    (hp : Function.Periodic f T) (hm : 0 ≤ m) (hmt : m ≤ T) :
    BddBelow (Set.range (fun a : ℝ => a*m + ∫ t in Ioc 0 T, max (f t-a) 0)) := by
  refine ⟨∫ t in Ioc 0 m, f t,?_⟩
  rintro _ ⟨a,rfl⟩
  have h := periodic_setIntegral_le_threshold f hf hT hp a 0 (Ioc 0 m) measurableSet_Ioc
    (by simpa only [zero_add] using Ioc_subset_Ioc_right hmt)
  simpa only [volume_real_Ioc_of_le hm,sub_zero] using h

theorem periodicTopIntegral_candidate_le
    (f : ℝ → ℝ) (hf : Continuous f) (T m : ℝ) (hT : 0 < T)
    (hp : Function.Periodic f T) (q : ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (hsub : E ⊆ Ioc q (q+T)) (hvol : volume.real E = m) :
    (∫ t in E, f t) ≤ periodicTopIntegral f T m := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨a,rfl⟩
  simpa only [hvol] using periodic_setIntegral_le_threshold f hf hT hp a q E hE hsub

theorem periodicTopIntegral_le_threshold
    (f : ℝ → ℝ) (hf : Continuous f) (T m : ℝ) (hT : 0 < T)
    (hp : Function.Periodic f T) (hm : 0 ≤ m) (hmt : m ≤ T) (a : ℝ) :
    periodicTopIntegral f T m ≤ a*m + ∫ t in Ioc 0 T, max (f t-a) 0 :=
  csInf_le (periodicTopIntegral_bddBelow f hf T m hT hp hm hmt) ⟨a,rfl⟩

/-- The optimizing set may include any portion of the cutoff level.
This handles the zero plateau of a clipped Green function. -/
theorem periodicTopIntegral_eq_of_threshold_set
    (f : ℝ → ℝ) (hf : Continuous f) (T m : ℝ) (hT : 0 < T)
    (hp : Function.Periodic f T) (hm : 0 ≤ m) (hmt : m ≤ T)
    (q a : ℝ) (E : Set ℝ) (hE : MeasurableSet E) (hsub : E ⊆ Ioc q (q+T))
    (hvol : volume.real E = m)
    (h₁ : ∀ t ∈ E, a ≤ f t)
    (h₂ : ∀ t ∈ Ioc q (q+T), t ∉ E → f t ≤ a) :
    periodicTopIntegral f T m = ∫ t in E, f t := by
  let I := Ioc q (q+T)
  let μ := volume.restrict I
  let P (t : ℝ) := max (f t-a) 0
  have hInt : Integrable f μ :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hP : Integrable P μ :=
    (((hf.sub continuous_const).max continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hzero : (∫ t in Eᶜ, P t ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    rw [Measure.restrict_restrict hE.compl]
    filter_upwards [ae_restrict_mem (hE.compl.inter measurableSet_Ioc)] with t ht
    exact max_eq_right (sub_nonpos.mpr (h₂ t ht.2 ht.1))
  have hshift : (∫ t in E, P t) = (∫ t in E, f t) - a*m := by
    have hfi : IntegrableOn f E := (show IntegrableOn f I volume from hInt).mono_set hsub
    have hfin : volume E ≠ ∞ := ((Metric.isBounded_Ioc _ _).subset hsub).measure_lt_top.ne
    have he : (∫ t in E, P t) = ∫ t in E, f t-a := by
      apply setIntegral_congr_fun hE
      exact fun t ht => max_eq_left (sub_nonneg.mpr (h₁ t ht))
    rw [he,integral_sub hfi (integrableOn_const hfin),setIntegral_const,smul_eq_mul,hvol,mul_comm]
  have hh := integral_add_compl (μ := μ) hE hP
  rw [hzero,add_zero,show μ.restrict E = volume.restrict E from
    Measure.restrict_restrict_of_subset hsub] at hh
  change (∫ t in E, P t) = ∫ t in I, P t at hh
  rw [show (∫ t in I, P t) = ∫ t in Ioc 0 T, P t from
    periodic_positivePart_turn_integral f hT hp a q,hshift] at hh
  have hbound := periodicTopIntegral_le_threshold f hf T m hT hp hm hmt a
  change periodicTopIntegral f T m ≤ a*m+∫ t in Ioc 0 T, P t at hbound
  rw [← hh] at hbound
  exact le_antisymm (by linarith only [hbound])
    (periodicTopIntegral_candidate_le f hf T m hT hp q E hE hsub hvol)

end SpringerLean
