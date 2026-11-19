import SpringerLean.Round715AngularHarmonicSwap

open Set MeasureTheory Real

namespace SpringerLean

/-- A circle average can be interchanged with a bounded measurable
vertical slice of any continuous function. -/
theorem continuous_vertical_setIntegral_circleAverage
    (u : ℂ → ℝ) (hu : Continuous u) (E : Set ℝ) (hEm : MeasurableSet E)
    (hEb : Bornology.IsBounded E) (x : ℂ) (r : ℝ) :
    CircleIntegrable (fun z => ∫ t in E, u (z+(t:ℂ)*Complex.I)) x r ∧
      IntegrableOn (fun t : ℝ => circleAverage u (x+(t:ℂ)*Complex.I) r) E ∧
      circleAverage (fun z => ∫ t in E, u (z+(t:ℂ)*Complex.I)) x r =
        ∫ t in E, circleAverage u (x+(t:ℂ)*Complex.I) r := by
  let J := Ioc (0:ℝ) (2*π)
  let μ := volume.restrict E
  let ν := volume.restrict J
  let K (t : ℝ) (θ : ℝ) := u (circleMap x r θ+(t:ℂ)*Complex.I)
  have hKc : Continuous (Function.uncurry K) := hu.comp (by fun_prop)
  have hKi : Integrable (Function.uncurry K) (μ.prod ν) := by
    change Integrable _ ((volume.restrict E).prod (volume.restrict J))
    rw [Measure.prod_restrict]
    exact (hKc.continuousOn.integrableOn_compact (μ := volume.prod volume)
      (hEb.isCompact_closure.prod isCompact_Icc)).mono_set
      (Set.prod_mono subset_closure Ioc_subset_Icc_self)
  have hAng (t : ℝ) : circleAverage u (x+(t:ℂ)*Complex.I) r =
      (2*π)⁻¹ * ∫ θ, K t θ ∂ν := by
    rw [circleAverage_eq_angle_Ioc_general]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun θ => congrArg u (by simp only [circleMap]; ring)
  have hI : IntegrableOn (fun t : ℝ => circleAverage u (x+(t:ℂ)*Complex.I) r) E := by
    simp_rw [hAng]
    exact (hKi.integral_prod_left).const_mul _
  refine ⟨?_,hI,?_⟩
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mpr
    exact hKi.integral_prod_right
  · rw [circleAverage_eq_angle_Ioc_general]
    simp_rw [hAng]
    rw [integral_const_mul]
    congr 1
    exact (integral_integral_swap hKi).symm

end SpringerLean
