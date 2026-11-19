import SpringerLean.Round55DiskPolar
import SpringerLean.Round08Lp

open MeasureTheory Filter Set
open scoped Topology ENNReal ComplexConjugate

namespace SpringerLean

/-- Polar Fubini away from the origin: disk integrability controls the
unweighted integral on almost every terminal radius.  No radial trace
or boundary extension is part of the hypotheses. -/
theorem ae_radial_integrableOn_of_disk_integrable
    (f : ℂ → ℂ)
    (hcont : ContinuousOn f (Metric.ball (0 : ℂ) 1))
    (hint : IntegrableOn f (Metric.ball (0 : ℂ) 1)) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      IntegrableOn (fun r : ℝ => f (Complex.polarCoord.symm (r, θ)))
        (Ioo (1 / 2 : ℝ) 1) := by
  classical
  let D : Set ℂ := Metric.ball 0 1
  let q : ℂ → ℝ := D.piecewise (fun z => ‖f z‖) (fun _ => 0)
  let Q : ℝ × ℝ → ENNReal := fun p =>
    ENNReal.ofReal p.1 * ENNReal.ofReal (q (Complex.polarCoord.symm p))
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hq : Measurable q :=
    ContinuousOn.measurable_piecewise hcont.norm continuousOn_const hD
  have hpolar : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hQ : Measurable Q := by
    exact (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp (hq.comp hpolar.measurable))
  have hmem {r θ : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
      Complex.polarCoord.symm (r, θ) ∈ D := by
    simpa only [D, Metric.mem_ball, dist_zero_right,
      Complex.norm_polarCoord_symm, abs_of_pos hr.1] using hr.2
  have hfinite :
      (∫⁻ r in Ioo (0 : ℝ) 1, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        Q (r, θ)) < ∞ := by
    have heq := unitDisk_lintegral_polar (fun z => ENNReal.ofReal (q z))
      (ENNReal.measurable_ofReal.comp hq)
    have hsame : (∫⁻ z in D, ENNReal.ofReal (q z)) =
        ∫⁻ z in D, ENNReal.ofReal ‖f z‖ := by
      apply setLIntegral_congr_fun hD
      intro z hz
      simp only [q, piecewise_eq_of_mem D _ _ hz]
    rw [← heq]
    rw [hsame]
    exact (hasFiniteIntegral_iff_norm f).1 hint.2
  have hswap := lintegral_lintegral_swap
    (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (ν := volume.restrict (Ioo (-Real.pi) Real.pi))
    (f := fun r θ => Q (r, θ)) hQ.aemeasurable
  rw [hswap] at hfinite
  have hae := ae_lt_top (μ := volume.restrict (Ioo (-Real.pi) Real.pi))
    hQ.lintegral_prod_left' hfinite.ne
  filter_upwards [hae] with θ hθ
  have hradcont : ContinuousOn
      (fun r : ℝ => f (Complex.polarCoord.symm (r, θ))) (Ioo (1 / 2 : ℝ) 1) := by
    apply hcont.comp (hpolar.comp (continuous_id.prodMk continuous_const)).continuousOn
    intro r hr
    change Complex.polarCoord.symm (r, θ) ∈ D
    exact hmem ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1, hr.2⟩
  refine ⟨hradcont.aestronglyMeasurable measurableSet_Ioo,
    (hasFiniteIntegral_iff_norm _).2 ?_⟩
  calc
    (∫⁻ r in Ioo (1 / 2 : ℝ) 1,
        ENNReal.ofReal ‖f (Complex.polarCoord.symm (r, θ))‖) ≤
        ∫⁻ r in Ioo (1 / 2 : ℝ) 1, 2 * Q (r, θ) := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro r hr
      have hp := hmem (θ := θ) ⟨by linarith [hr.1], hr.2⟩
      have hr0 : 0 ≤ r := by linarith [hr.1]
      have hr1 : (1 : ENNReal) ≤ 2 * ENNReal.ofReal r := by
        have hh := ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2 * r by linarith [hr.1])
        simpa only [ENNReal.ofReal_one, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_ofNat] using hh
      dsimp only [Q, q]
      rw [piecewise_eq_of_mem D _ _ hp, ← mul_assoc]
      exact le_mul_of_one_le_left' hr1
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) 1, 2 * Q (r, θ) := by
      exact lintegral_mono_set (Ioo_subset_Ioo (by norm_num) le_rfl)
    _ = 2 * ∫⁻ r in Ioo (0 : ℝ) 1, Q (r, θ) := by
      exact lintegral_const_mul' 2 _ (by norm_num)
    _ < ∞ := ENNReal.mul_lt_top (by norm_num) hθ

/-- This is the actual forward germ supplied by the exterior class, not
an arbitrary analytic surrogate with a trace hypothesis. -/
theorem exteriorForwardGerm_deriv_ae_radial_integrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      IntegrableOn (fun r : ℝ =>
        deriv (exteriorForwardGerm F) (conj (Complex.polarCoord.symm (r, θ))))
        (Ioo (1 / 2 : ℝ) 1) := by
  apply ae_radial_integrableOn_of_disk_integrable
    (fun z : ℂ => deriv (exteriorForwardGerm F) (conj z))
  · have hconj : Continuous (fun z : ℂ => conj z) := by fun_prop
    apply (exteriorForwardGerm_analyticOnNhd_unitBall F hc).deriv.continuousOn.comp
      hconj.continuousOn
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
  · exact exteriorForwardGerm_deriv_integrableOn F hc

end SpringerLean

#print axioms SpringerLean.ae_radial_integrableOn_of_disk_integrable
#print axioms SpringerLean.exteriorForwardGerm_deriv_ae_radial_integrable
