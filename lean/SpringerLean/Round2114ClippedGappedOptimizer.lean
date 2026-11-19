import SpringerLean.Round2112GappedPeriodicOptimizer
import SpringerLean.Round2108PositiveAnalyticLevels

open Set MeasureTheory Real Metric Filter
open scoped ENNReal Topology

namespace SpringerLean

private theorem periodic_superlevel_inside_trimmed_turn
    (f : ℝ → ℝ) (hf : Continuous f) {T : ℝ} (hp : Function.Periodic f T)
    (q a : ℝ) (hq : f q < a) :
    ∃ δ > 0, ∀ d > 0, d ≤ δ → {t | a ≤ f t} ∩ Ioc q (q+T) ⊆ Icc (q+d) (q+T-d) := by
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp (isOpen_lt hf continuous_const) q hq
  refine ⟨R/2,half_pos hR,?_⟩
  intro d hd hdR t ht
  have hlt : d < R := hdR.trans_lt (by linarith)
  refine ⟨?_,?_⟩
  · by_contra! hn
    have htb : t ∈ ball q R := by
      rw [mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.2.1.le)]
      linarith
    exact (not_lt_of_ge (show a ≤ f t from ht.1)) (hball htb)
  · by_contra! hn
    have htb : t-T ∈ ball q R := by
      rw [mem_ball,Real.dist_eq,abs_of_nonpos (by linarith [ht.2.2])]
      linarith
    have hh : f (t-T) < a := hball htb
    have eq := hp (t-T)
    rw [sub_add_cancel] at eq
    exact (not_lt_of_ge (show a ≤ f t from ht.1)) (eq.symm ▸ hh)

private theorem strict_level_mass_eq_weak_of_null
    (f : ℝ → ℝ) (a : ℝ) (h : volume {t | f t = a} = 0) (I : Set ℝ) :
    volume.real ({t | a < f t} ∩ I) = volume.real ({t | a ≤ f t} ∩ I) := by
  have ha : ∀ᵐ t : ℝ ∂volume, f t ≠ a := by simpa only [ae_iff,ne_eq,not_not] using h
  have he : ({t | a < f t} ∩ I) =ᵐ[volume] ({t | a ≤ f t} ∩ I) := by
    filter_upwards [ha] with t ht
    change (a < f t ∧ t ∈ I) = (a ≤ f t ∧ t ∈ I)
    apply propext
    rw [lt_iff_le_and_ne]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,ht.symm⟩,h.2⟩⟩
  exact congrArg ENNReal.toReal (measure_congr he)

private theorem exists_period_representative
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (hp : Function.Periodic f T) (q t : ℝ) :
    ∃ s ∈ Ioc q (q+T), f s = f t := by
  refine ⟨toIocMod hT q t,toIocMod_mem_Ioc hT q t,?_⟩
  exact hp.sub_zsmul_eq (x := t) (toIocDiv hT q t)

/-- On a turn of a clipped Green-type profile, an exact top set has
both an included interval and margins at some cut. Positive levels
are null. The zero plateau is sliced to the remaining mass. -/
theorem clipped_periodic_exists_gapped_topIntegral
    (g : ℝ → ℝ) (hgc : Continuous g) (T m τ : ℝ) (hT : 0 < T)
    (hgp : Function.Periodic g T) (hm : 0 < m) (hmt : m < T) (hτ : 0 < τ)
    (hnull : (¬∃ b : ℝ, ∀ t, g t = b) → ∀ a > 0, volume {t | g t = a} = 0) :
    let f := fun t => max (g t-τ) 0
    ∃ (q p d : ℝ) (E : Set ℝ), 0 < d ∧ MeasurableSet E ∧ volume.real E = m ∧
      Icc (p-d) (p+d) ⊆ E ∧ E ⊆ Icc (q+d) (q+T-d) ∧
      periodicTopIntegral f T m = ∫ t in E, f t := by
  let f (t : ℝ) := max (g t-τ) 0
  have hfc : Continuous f := (hgc.sub continuous_const).max continuous_const
  have hfp : Function.Periodic f T := fun t => congrArg (fun v : ℝ => max (v-τ) 0) (hgp t)
  have hf0 (t : ℝ) : 0 ≤ f t := le_max_right _ _
  have him (q : ℝ) : volume.real (Ioc q (q+T)) = T := by
    rw [volume_real_Ioc_of_le (by linarith : q ≤ q+T)]
    ring
  by_cases hc : ∃ b : ℝ, ∀ t, f t = b
  · obtain ⟨b,hb⟩ := hc
    let p := T/2
    let d := min (m/4) ((T-m)/4)
    let E := Ioc (p-m/2) (p+m/2)
    have hd : 0 < d := lt_min (by linarith) (by linarith)
    have hd1 : d ≤ m/4 := min_le_left _ _
    have hd2 : d ≤ (T-m)/4 := min_le_right _ _
    have hvol : volume.real E = m := by
      rw [show E = Ioc (p-m/2) (p+m/2) from rfl,volume_real_Ioc_of_le (by linarith)]
      ring
    have houter : E ⊆ Icc (0+d) (0+T-d) := by
      intro t ht
      change p-m/2 < t ∧ t ≤ p+m/2 at ht
      dsimp [p] at ht
      exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have sub : E ⊆ Ioc 0 (0+T) := by
      intro t ht
      have h := houter ht
      exact ⟨by linarith [h.1],by linarith [h.2]⟩
    refine ⟨0,p,d,E,hd,measurableSet_Ioc,hvol,?_,houter,?_⟩
    · intro t ht
      exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
    · exact periodicTopIntegral_eq_of_threshold_set f hfc T m hT hfp hm.le hmt.le 0 b E
        measurableSet_Ioc sub hvol (fun t _ => (hb t).ge) (fun t _ _ => (hb t).le)
  have hgn : ¬∃ b : ℝ, ∀ t, g t = b := by
    rintro ⟨b,hb⟩
    exact hc ⟨max (b-τ) 0,fun t => congrArg (fun v : ℝ => max (v-τ) 0) (hb t)⟩
  obtain ⟨a,hv⟩ := periodic_exists_threshold_mass f hfc T m hT hfp hm hmt
  have ha : 0 ≤ a := by
    by_contra! hn
    have he : {t | a < f t} ∩ Ioc 0 (0+T) = Ioc 0 (0+T) := by
      ext t; exact ⟨fun h => h.2,fun h => ⟨hn.trans_le (hf0 t),h⟩⟩
    have h := (hv 0).1
    rw [he,him 0] at h
    exact (not_le_of_gt hmt) h
  rcases lt_or_eq_of_le ha with hap | ha0
  · have hNull : volume {t | f t = a} = 0 := by
      apply measure_mono_null _ (hnull hgn (a+τ) (add_pos hap hτ))
      intro t ht
      have ht' : max (g t-τ) 0 = a := ht
      rcases max_choice (g t-τ) 0 with h | h
      · change g t = a+τ
        linarith only [ht',h]
      · exact (hap.ne' (ht'.symm.trans h)).elim
    have hmass (q : ℝ) : volume.real ({t | a < f t} ∩ Ioc q (q+T)) = m :=
      le_antisymm (hv q).1 ((hv q).2.trans_eq (strict_level_mass_eq_weak_of_null f a hNull _).symm)
    obtain ⟨q,hq⟩ : ∃ q : ℝ, f q < a := by
      by_contra! hq
      have he : {t | a ≤ f t} ∩ Ioc 0 (0+T) = Ioc 0 (0+T) := by
        ext t; exact ⟨fun h => h.2,fun h => ⟨hq t,h⟩⟩
      have hh := hmass 0
      rw [strict_level_mass_eq_weak_of_null f a hNull _,he,him 0] at hh
      exact hmt.ne hh.symm
    obtain ⟨d,hd,hcut⟩ := periodic_superlevel_inside_trimmed_turn f hfc hfp q a hq
    have hc' := hcut d hd le_rfl
    have hweak : {t | a ≤ f t} ∩ Ioc q (q+T) = {t | a ≤ f t} ∩ Icc (q+d) (q+T-d) := by
      apply Subset.antisymm
      · intro t ht
        exact ⟨ht.1,hc' ht⟩
      · intro t ht
        exact ⟨ht.1, by exact ⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩⟩
    have hne : ({t | a < f t} ∩ Ioc q (q+T)).Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      intro he
      have h := hmass q
      rw [he,measureReal_empty] at h
      exact hm.ne' h.symm
    obtain ⟨p,r,E,hr,hEm,hEv,hEin,hEout,hval⟩ := periodicTopIntegral_exists_gapped_of_cut
      f hfc T m hT hfp hm hmt q a d hd hne
      (fun _ h => hc' ⟨(show a < f _ from h.1).le,h.2⟩)
      (hv q).1 (by rw [← hweak]; exact (hv q).2)
    exact ⟨q,p,r,E,hr,hEm,hEv,hEin,hEout,hval⟩
  · have ha' : a = 0 := ha0.symm
    obtain ⟨q,hq⟩ : ∃ q : ℝ, g q < τ := by
      by_contra! hq
      have he : {t | 0 < f t} = {t | τ < g t} := by
        ext t
        change 0 < max (g t-τ) 0 ↔ τ < g t
        simp [lt_max_iff,sub_pos]
      have h := (hv 0).1
      rw [ha',he,strict_level_mass_eq_weak_of_null g τ (hnull hgn τ hτ) _] at h
      have he' : {t | τ ≤ g t} ∩ Ioc 0 (0+T) = Ioc 0 (0+T) := by
        ext t; exact ⟨fun ht => ht.2,fun ht => ⟨hq t,ht⟩⟩
      rw [he',him 0] at h
      exact hmt.not_ge h
    obtain ⟨d,hd,hcut⟩ := periodic_superlevel_inside_trimmed_turn g hgc hgp q τ hq
    let r := min d ((T-m)/4)
    have hr : 0 < r := lt_min hd (by linarith)
    have hrm : r ≤ (T-m)/4 := min_le_right _ _
    have hc' := hcut r hr (min_le_left _ _)
    obtain ⟨t,ht⟩ : ∃ t, 0 < f t := by
      by_contra! ht
      exact hc ⟨0,fun t => le_antisymm (ht t) (hf0 t)⟩
    obtain ⟨s,hs,hst⟩ := exists_period_representative f hT hfp q t
    have hp : a < f s := by simpa only [ha',hst] using ht
    have hne : ({t | a < f t} ∩ Ioc q (q+T)).Nonempty := ⟨s,hp,hs⟩
    have hle : m ≤ volume.real ({t | a ≤ f t} ∩ Icc (q+r) (q+T-r)) := by
      have he : {t | a ≤ f t} = univ := by ext t; simp [ha',hf0 t]
      rw [he,univ_inter,volume_real_Icc_of_le (by linarith)]
      linarith
    obtain ⟨p,d',E,hd',hEm,hEv,hEin,hEout,hval⟩ := periodicTopIntegral_exists_gapped_of_cut
      f hfc T m hT hfp hm hmt q a r hr hne (by
        intro t ht'
        have hgt : τ < g t := by
          have hp : a < f t := ht'.1
          simpa only [ha',f,lt_max_iff,lt_self_iff_false,or_false,sub_pos] using hp
        exact hc' ⟨hgt.le,ht'.2⟩) (hv q).1 hle
    exact ⟨q,p,d',E,hd',hEm,hEv,hEin,hEout,hval⟩

end SpringerLean
