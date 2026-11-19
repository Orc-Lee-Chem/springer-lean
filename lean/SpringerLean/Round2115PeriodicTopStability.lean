import SpringerLean.Round2106PeriodicTopIntegral

open Set MeasureTheory Real

namespace SpringerLean

/-- Uniform control of the input profile gives uniform control of its
top integral, even when the optimizing level has a plateau. -/
theorem periodicTopIntegral_le_add_of_forall_le_add
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (T m ε : ℝ) (hT : 0 < T) (hm : 0 ≤ m) (hmt : m ≤ T)
    (hfp : Function.Periodic f T) (hε : 0 ≤ ε)
    (hle : ∀ t ∈ Ioc 0 T, f t ≤ g t+ε) :
    periodicTopIntegral f T m ≤ periodicTopIntegral g T m+T*ε := by
  apply sub_le_iff_le_add.mp
  unfold periodicTopIntegral
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨a,rfl⟩
  have h := periodicTopIntegral_le_threshold f hf T m hT hfp hm hmt a
  have hi (u : ℝ → ℝ) (hu : Continuous u) : IntegrableOn u (Ioc 0 T) :=
    (hu.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hI : (∫ t in Ioc 0 T, max (f t-a) 0) ≤ ∫ t in Ioc 0 T, max (g t-a) 0+ε := by
    apply setIntegral_mono_on (hi _ (by fun_prop)) (hi _ (by fun_prop)) measurableSet_Ioc
    intro t ht
    refine max_le ?_ (add_nonneg (le_max_right _ _) hε)
    linarith [hle t ht, le_max_left (g t-a) (0:ℝ)]
  rw [integral_add (hi _ (by fun_prop)) (hi _ continuous_const),setIntegral_const,smul_eq_mul,
    volume_real_Ioc_of_le hT.le,sub_zero] at hI
  change periodicTopIntegral f T m - T*ε ≤ a*m + ∫ t in Ioc 0 T, max (g t-a) 0
  exact sub_le_iff_le_add.mpr (by linarith only [h,hI])

/-- Varying the angular mass has Lipschitz constant equal to a bound
for a nonnegative angular profile. This includes both end masses. -/
theorem periodicTopIntegral_le_add_of_mass
    (f : ℝ → ℝ) (hf : Continuous f) (T B m n : ℝ) (hT : 0 < T)
    (hp : Function.Periodic f T) (hm : 0 ≤ m) (hmT : m ≤ T) (hn : 0 ≤ n) (hnT : n ≤ T)
    (hB : 0 ≤ B) (hb : ∀ t ∈ Ioc 0 T, 0 ≤ f t ∧ f t ≤ B) :
    periodicTopIntegral f T m ≤ periodicTopIntegral f T n+B*|m-n| := by
  apply sub_le_iff_le_add.mp
  unfold periodicTopIntegral
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨a,rfl⟩
  let c := max 0 (min B a)
  have hc : 0 ≤ c := le_max_left _ _
  have hcB : c ≤ B := max_le hB (min_le_left _ _)
  have hM : c*m ≤ c*n+B*|m-n| := by
    have h0 := mul_le_mul_of_nonneg_left (le_abs_self (m-n)) hc
    have h1 := mul_le_mul_of_nonneg_right hcB (abs_nonneg (m-n))
    linarith only [h0,h1]
  have hI : c*n+(∫ t in Ioc 0 T, max (f t-c) 0) ≤
      a*n+∫ t in Ioc 0 T, max (f t-a) 0 := by
    have hIoc : IntegrableOn f (Ioc 0 T) :=
      (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hpos (a : ℝ) (ha : a ≤ 0) : (∫ t in Ioc 0 T, max (f t-a) 0) =
        (∫ t in Ioc 0 T, f t)-T*a := by
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t => f t-a)
        (fun t ht => max_eq_left (sub_nonneg.mpr (ha.trans (hb t ht).1))),
        integral_sub hIoc (integrableOn_const (Metric.isBounded_Ioc (0:ℝ) T).measure_lt_top.ne),
        setIntegral_const,smul_eq_mul,volume_real_Ioc_of_le hT.le,sub_zero]
    have hzero (a : ℝ) (ha : B ≤ a) : (∫ t in Ioc 0 T, max (f t-a) 0) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      exact fun t ht => max_eq_right (sub_nonpos.mpr ((hb t ht).2.trans ha))
    by_cases h0 : a ≤ 0
    · have he : c = 0 := max_eq_left ((min_le_right _ _).trans h0)
      rw [he,hpos 0 le_rfl,hpos a h0]
      nlinarith only [mul_nonneg_of_nonpos_of_nonpos h0 (show n-T ≤ 0 by linarith only [hnT])]
    by_cases h1 : B ≤ a
    · have he : c = B := by simp [c,min_eq_left h1,max_eq_right hB]
      rw [he,hzero B le_rfl,hzero a h1]
      linarith only [mul_le_mul_of_nonneg_right h1 hn]
    · have he : c = a := by simp [c,min_eq_right (le_of_not_ge h1),max_eq_right (le_of_not_ge h0)]
      rw [he]
  have h := periodicTopIntegral_le_threshold f hf T m hT hp hm hmT c
  change periodicTopIntegral f T m - B*|m-n| ≤ a*n + ∫ t in Ioc 0 T, max (f t-a) 0
  exact sub_le_iff_le_add.mpr (by linarith only [h,hI,hM])

end SpringerLean
