import SpringerLean.Round678AnalyticLevelNull
import SpringerLean.Round2107OddGreenChart

open Filter MeasureTheory Set Real
open scoped Topology

namespace SpringerLean

/-- If a continuous real function is real analytic at each positive
level, a nonconstant function has null positive level sets. The proof
allows an arbitrary closed zero set. -/
theorem continuous_positive_analytic_level_volume_zero
    (f : ℝ → ℝ) (hfc : Continuous f) (hfa : ∀ t, 0 < f t → AnalyticAt ℝ f t)
    (hnot : ¬∃ c : ℝ, ∀ t : ℝ, f t = c) (a : ℝ) (ha : 0 < a) :
    volume {t | f t = a} = 0 := by
  let E := {t : ℝ | f t = a}
  let V := interior E
  have hE : IsClosed E := isClosed_eq hfc continuous_const
  have hVc : IsClosed V := by
    apply isClosed_of_closure_subset
    intro t ht
    by_contra hnotV
    have htE := closure_minimal interior_subset hE ht
    have htEq : f t = a := htE
    have hat := hfa t (htEq ▸ ha)
    haveI : NeBot (𝓝[V] t) := mem_closure_iff_nhdsWithin_neBot.mp ht
    have hsub : V ⊆ ({t} : Set ℝ)ᶜ := by
      intro x hx hxt
      exact hnotV ((mem_singleton_iff.mp hxt) ▸ hx)
    have hAt : ∀ᶠ x in 𝓝[V] t, f x = a :=
      (show ∀ᶠ x in 𝓝[V] t, x ∈ V from self_mem_nhdsWithin).mono (fun x hx =>
        show x ∈ E from interior_subset hx)
    have hfreq : ∃ᶠ x in 𝓝[≠] t, f x = a :=
      hAt.frequently.filter_mono (nhdsWithin_mono t hsub)
    have hEv := (hat.frequently_eq_iff_eventually_eq
      (show AnalyticAt ℝ (fun _ : ℝ => a) t from analyticAt_const)).mp hfreq
    exact hnotV (mem_interior_iff_mem_nhds.mpr hEv)
  have hV : V = ∅ := (isClopen_iff.mp ⟨hVc,isOpen_interior⟩).resolve_right (by
    intro h
    apply hnot
    refine ⟨a,fun t => ?_⟩
    have ht : t ∈ V := by rw [h]; exact mem_univ _
    exact (show t ∈ E from interior_subset ht))
  have hdis : {t : ℝ | f t ≠ a} ∈ codiscreteWithin (univ : Set ℝ) := by
    apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
    intro t ht
    have he (h : f t = a) : ∀ᶠ x in 𝓝[≠] t, f x ≠ a := by
      have hpos : 0 < f t := by rwa [h]
      rcases (hfa t hpos).eventually_eq_or_eventually_ne
        (show AnalyticAt ℝ (fun _ : ℝ => a) t from analyticAt_const) with hL | hR
      · have hT : t ∈ V := mem_interior_iff_mem_nhds.mpr hL
        exact (show t ∉ V by simp [hV]) hT |>.elim
      · exact hR
    by_cases heq : f t = a
    · filter_upwards [he heq] with x hx
      exact Or.inl hx
    · filter_upwards [((hfc.continuousAt.eventually_ne heq).filter_mono nhdsWithin_le_nhds)] with x hx
      exact Or.inl hx
  have hle : ae (volume : Measure ℝ) ≤ codiscreteWithin (univ : Set ℝ) := by
    simpa only [Measure.restrict_univ] using
      (ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ)
  simpa only [ne_eq,not_not] using ae_iff.mp (hle hdis)

theorem oddGreenChart_positive_level_volume_zero
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (x : ℝ)
    (hn : ¬∃ c : ℝ, ∀ t : ℝ,
      exteriorGreenCoordinate F (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I)) = c)
    (a : ℝ) (ha : 0 < a) :
    volume {t : ℝ | exteriorGreenCoordinate F (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))=a} = 0 := by
  let g (t : ℝ) := exteriorGreenCoordinate F (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))
  have he : g = fun t => exteriorGreenCoordinate F (circleMap 0 (exp (x/2)) (π/2+t/2)) :=
    funext fun t => congrArg (exteriorGreenCoordinate F) (oddGreenChart_eq_circleMap x t)
  apply continuous_positive_analytic_level_volume_zero g _ _ hn a ha
  · rw [he]
    exact (exteriorGreenCoordinate_continuous F hF).comp ((continuous_circleMap _ _).comp (by fun_prop))
  · intro t ht
    rw [he] at ht ⊢
    have hs := (exteriorGreenCoordinate_pos_iff F _).mp ht
    exact (exteriorGreenCoordinate_angular_analyticAt F hF _ _ hs).comp
      (f := fun t : ℝ => π/2+t/2) (x := t) (by fun_prop)

end SpringerLean
