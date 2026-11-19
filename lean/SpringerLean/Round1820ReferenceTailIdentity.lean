import SpringerLean.Round1819NormalizedReferenceTest

open MeasureTheory Metric Set

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 900000

theorem normalizedReferenceTest_continuous (m : ℕ) (c : ℝ) :
    Continuous (normalizedReferenceTest m c) := by
  unfold normalizedReferenceTest
  fun_prop

/-- Exact one-dimensional excess integral, with the original disk
area normalization. There is no tail estimate in this identity. -/
theorem alignedPhaseReferenceCost_excess_integral
    (k : ℕ) (hk : 751 ≤ k) (a : ℝ) (ha : 6 ≤ a)
    (hau : a ≤ ((2*k-2 : ℕ) : ℝ)/5) :
    let m := 2*k-2
    let c := 1-a/(m : ℝ)
    alignedPhaseReferenceCost k a-comparisonPositiveDiskMoment m=
      (2*Real.pi⁻¹)*(∫ x in Ioo 0 c,
        Real.sqrt (1-x^2)*(x^(m-8)*(c^8-x^8))) := by
  let m := 2*k-2
  let c := 1-a/(m : ℝ)
  have hm : 1500 ≤ m := by dsimp [m]; omega
  have hm' : (1500 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hadiv : a/(m : ℝ) ≤ 1/5 := (div_le_iff₀ hm0).mpr (by dsimp [m]; linarith)
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hcup : c ≤ 1 := by
    dsimp [c]
    have hh : 0 ≤ a/(m : ℝ) := by positivity
    linarith
  have hi : 2*k-12+10=m := by dsimp [m]; omega
  have htest (x : ℝ) : twoPowerPhaseTest (2*c) (2*k-12) (2*x)/(2 : ℝ)^m=
      normalizedReferenceTest m c x := by
    simpa only [hi] using twoPowerPhaseTest_normalized (2*k-12) c x
  have href : alignedPhaseReferenceCost k a=
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, normalizedReferenceTest m c z.re) := by
    unfold alignedPhaseReferenceCost
    exact congrArg (fun v : ℝ => Real.pi⁻¹*v) (integral_congr_ae (Filter.Eventually.of_forall (fun z => htest z.re)))
  have htestI : IntegrableOn (fun z : ℂ => normalizedReferenceTest m c z.re) (ball (0 : ℂ) 1) := by
    have hh := comparisonDisk_test_integrableOn (fun x : ℝ => normalizedReferenceTest m c (x/2))
      ((normalizedReferenceTest_continuous m c).comp (by fun_prop))
    simpa only [show ∀ x : ℝ, 2*x/2=x from fun x => by ring] using hh
  have hpowerI : IntegrableOn (fun z : ℂ => (max z.re 0)^m) (ball (0 : ℂ) 1) := by
    have hh := comparisonDisk_test_integrableOn (fun x : ℝ => (max (x/2) 0)^m) (by fun_prop)
    simpa only [show ∀ x : ℝ, 2*x/2=x from fun x => by ring] using hh
  have hdensity := comparisonDisk_re_integral_density
    (fun x => normalizedReferenceTest m c x-(max x 0)^m)
    ((normalizedReferenceTest_continuous m c).sub (by fun_prop))
  have hpoint : (fun x : ℝ => Real.sqrt (1-x^2)*(normalizedReferenceTest m c x-(max x 0)^m))=
      (Ioo 0 c).indicator (fun x => Real.sqrt (1-x^2)*(x^(m-8)*(c^8-x^8))) := by
    funext x
    rw [normalizedReferenceTest_excess m (by omega) hc]
    by_cases hx : 0 < x ∧ x < c
    · rw [if_pos hx,Set.indicator_of_mem (show x ∈ Ioo 0 c from hx)]
    · rw [if_neg hx,Set.indicator_of_notMem (show x ∉ Ioo 0 c from hx),mul_zero]
  rw [hpoint,setIntegral_indicator measurableSet_Ioo] at hdensity
  have hset : Ioo (-1 : ℝ) 1 ∩ Ioo 0 c=Ioo 0 c := by
    apply inter_eq_right.mpr
    intro x hx
    exact ⟨by linarith [hx.1],hx.2.trans_le hcup⟩
  rw [hset,integral_sub htestI hpowerI] at hdensity
  change alignedPhaseReferenceCost k a-comparisonPositiveDiskMoment m=_
  rw [href]
  unfold comparisonPositiveDiskMoment
  nlinarith [hdensity]

end
end SpringerLean

#print axioms SpringerLean.alignedPhaseReferenceCost_excess_integral
