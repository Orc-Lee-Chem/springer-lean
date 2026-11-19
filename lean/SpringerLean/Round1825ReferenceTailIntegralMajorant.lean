import SpringerLean.Round1824ReferenceTailMajorant

open MeasureTheory Set

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 1200000

theorem reference_tail_integral_majorant
    {a m c : ℝ} (ha : 0 < a) (hm : 0 < m) (hc : 0 < c)
    (hrel : a+m*c=m) (ell : ℕ) (hell : 1 ≤ ell) :
    (∫ x in Ioo 0 c, Real.sqrt (1-x^2)*(x^ell*(c^8-x^8))) ≤
      (8*c^(ell+7)*Real.sqrt (2/m))*
        (Real.sqrt a/((ell : ℝ)/c)^2+m/(Real.sqrt a*((ell : ℝ)/c)^3)) := by
  let ρ := (ell : ℝ)/c
  let K := 8*c^(ell+7)*Real.sqrt (2/m)
  let J : ℝ → ℝ := fun x =>
    Real.sqrt a*((c-x)*Real.exp (-(ρ*(c-x))))+
      (m/(2*Real.sqrt a))*((c-x)^2*Real.exp (-(ρ*(c-x))))
  have hell0 : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  have hρ : 0 < ρ := div_pos hell0 hc
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hI₁ := integrableOn_reflected_Iio (fun t => t*Real.exp (-(ρ*t))) c
    (exponential_tail_first_integrable hρ)
  have hI₂ := integrableOn_reflected_Iio (fun t => t^2*Real.exp (-(ρ*t))) c
    (exponential_tail_second_integrable hρ)
  have hJ : IntegrableOn J (Iio c) := (hI₁.const_mul (Real.sqrt a)).add (hI₂.const_mul (m/(2*Real.sqrt a)))
  have hJsmall : IntegrableOn J (Ioo 0 c) := hJ.mono_set (fun _ hx => hx.2)
  have hP : IntegrableOn (fun x : ℝ => Real.sqrt (1-x^2)*(x^ell*(c^8-x^8))) (Ioo 0 c) :=
    ((show Continuous (fun x : ℝ => Real.sqrt (1-x^2)*(x^ell*(c^8-x^8))) by fun_prop).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hpoint : (fun x : ℝ => Real.sqrt (1-x^2)*(x^ell*(c^8-x^8))) ≤ᵐ[volume.restrict (Ioo 0 c)]
      (fun x => K*J x) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo 0 c))] with x hx
    have hh := reference_tail_pointwise_majorant ha hm hc hrel hx.1.le hx.2.le ell
    dsimp [K,J,ρ]
    convert hh using 1 <;> ring
  have hle := integral_mono_ae hP (hJsmall.const_mul K) hpoint
  rw [integral_const_mul] at hle
  have hJnonneg : 0 ≤ᵐ[volume.restrict (Iio c)] J := by
    filter_upwards [ae_restrict_mem (measurableSet_Iio : MeasurableSet (Iio c))] with x hx
    have hcx : 0 ≤ c-x := sub_nonneg.mpr (le_of_lt hx)
    dsimp [J]
    positivity
  have hsub : Ioo (0 : ℝ) c ≤ᵐ[volume] Iio c :=
    Filter.Eventually.of_forall (fun x hx => hx.2)
  have hbig := setIntegral_mono_set hJ hJnonneg hsub
  have hJvalue : (∫ x in Iio c, J x)=Real.sqrt a/ρ^2+m/(Real.sqrt a*ρ^3) := by
    obtain ⟨h₁,h₂⟩ := reflected_exponential_tail_moments c hρ
    dsimp [J]
    rw [integral_add (hI₁.const_mul (Real.sqrt a)) (hI₂.const_mul (m/(2*Real.sqrt a))),
      integral_const_mul,integral_const_mul,h₁,h₂]
    field_simp
    <;> ring
  have hh := hle.trans (mul_le_mul_of_nonneg_left hbig hK)
  rw [hJvalue] at hh
  exact hh

end
end SpringerLean

#print axioms SpringerLean.reference_tail_integral_majorant
