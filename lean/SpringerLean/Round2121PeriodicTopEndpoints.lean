import SpringerLean.Round2115PeriodicTopStability

open Set MeasureTheory Real

namespace SpringerLean

theorem periodicTopIntegral_const (c T m : ℝ) (hT : 0 < T) (hm : 0 ≤ m) (hmt : m ≤ T) :
    periodicTopIntegral (fun _ => c) T m = c*m := by
  have h := periodicTopIntegral_eq_of_threshold_set (fun _ => c) continuous_const T m hT
    (fun _ => rfl) hm hmt 0 c (Ioc 0 m) measurableSet_Ioc
    (by simpa only [zero_add] using Ioc_subset_Ioc_right hmt)
    (by rw [volume_real_Ioc_of_le hm,sub_zero]) (fun _ _ => le_rfl) (fun _ _ _ => le_rfl)
  rw [h,setIntegral_const,smul_eq_mul,volume_real_Ioc_of_le hm,sub_zero,mul_comm]

theorem periodicTopIntegral_zero (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) (hT : 0 < T)
    (hp : Function.Periodic f T) : periodicTopIntegral f T 0 = 0 := by
  obtain ⟨B,hB⟩ := (hp.isBounded_of_continuous hT.ne' hf).exists_norm_le
  have hb (t : ℝ) : f t ≤ B := (le_abs_self _).trans (hB (f t) (mem_range_self t))
  have h := periodicTopIntegral_eq_of_threshold_set f hf T 0 hT hp le_rfl hT.le 0 B
    ∅ MeasurableSet.empty (empty_subset _) measureReal_empty (fun _ h => h.elim) (fun t _ _ => hb t)
  simpa using h

theorem periodicTopIntegral_full_of_nonneg (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) (hT : 0 < T)
    (hp : Function.Periodic f T) (h₀ : ∀ t, 0 ≤ f t) (q : ℝ) :
    periodicTopIntegral f T T = ∫ t in Ioc q (q+T), f t := by
  apply periodicTopIntegral_eq_of_threshold_set f hf T T hT hp hT.le le_rfl q 0
    _ measurableSet_Ioc Subset.rfl
  · rw [volume_real_Ioc_of_le (by linarith : q ≤ q+T)]
    ring
  · exact fun t _ => h₀ t
  · exact fun t ht hn => (hn ht).elim

theorem periodicTopIntegral_mono (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (T m : ℝ) (hT : 0 < T) (hm : 0 ≤ m) (hmt : m ≤ T)
    (hp : Function.Periodic f T) (h : ∀ t ∈ Ioc 0 T, f t ≤ g t) :
    periodicTopIntegral f T m ≤ periodicTopIntegral g T m := by
  have h' := periodicTopIntegral_le_add_of_forall_le_add f g hf hg T m 0 hT hm hmt hp le_rfl
    (fun t ht => by simpa only [add_zero] using h t ht)
  simpa only [mul_zero,add_zero] using h'

/-- If a clipped profile has a zero arc, dropping any part of the
allowed mass inside that arc does not decrease the full-period value. -/
theorem periodicTopIntegral_full_le_of_zero_arc
    (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) (hT : 0 < T)
    (hp : Function.Periodic f T) (h₀ : ∀ t, 0 ≤ f t)
    (q d : ℝ) (hd0 : 0 ≤ d) (hdT : d ≤ T) (hz : ∀ t ∈ Ioc q (q+d), f t = 0) :
    periodicTopIntegral f T T ≤ periodicTopIntegral f T (T-d) := by
  rw [periodicTopIntegral_full_of_nonneg f hf T hT hp h₀ q]
  have hright : (∫ t in Ioc (q+d) (q+T), f t) ≤ periodicTopIntegral f T (T-d) :=
    periodicTopIntegral_candidate_le f hf T (T-d) hT hp q _ measurableSet_Ioc
      (Ioc_subset_Ioc_left (by linarith)) (by
        rw [volume_real_Ioc_of_le (by linarith : q+d ≤ q+T)]
        ring)
  have hleft : (∫ t in Ioc q (q+d), f t) = 0 := setIntegral_eq_zero_of_forall_eq_zero hz
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) q (q+d)) (hf.intervalIntegrable (μ := volume) (q+d) (q+T))
  rw [intervalIntegral.integral_of_le (by linarith : q ≤ q+d),
    intervalIntegral.integral_of_le (by linarith : q+d ≤ q+T),
    intervalIntegral.integral_of_le (by linarith : q ≤ q+T),hleft,zero_add] at hsum
  rwa [← hsum]

end SpringerLean
