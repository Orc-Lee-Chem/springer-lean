import SpringerLean.Round14AreaCircle

open MeasureTheory AddCircle Metric
open scoped ComplexConjugate

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- The real square mean of an analytic circle function with vanishing
square mean is half its square-modulus mean. -/
theorem real_square_circleAverage_eq_half_energy
    (h : ℂ → ℂ) (r : ℝ)
    (hcont : ContinuousOn h (sphere (0 : ℂ) |r|))
    (hsq : Real.circleAverage (fun z => h z ^ 2) 0 r = 0) :
    2 * Real.circleAverage (fun z => (h z).re ^ 2) 0 r =
      Real.circleAverage (fun z => ‖h z‖ ^ 2) 0 r := by
  let p := exteriorCirclePoint r
  have hpcont : Continuous p := by
    unfold p exteriorCirclePoint
    fun_prop
  have hpSphere : ∀ θ : AddCircle (2 * Real.pi), p θ ∈ sphere (0 : ℂ) |r| := by
    intro θ
    simp [p, exteriorCirclePoint]
  have hhcont : Continuous (fun θ : AddCircle (2 * Real.pi) => h (p θ)) :=
    hcont.comp_continuous hpcont hpSphere
  have hi : Integrable (fun θ : AddCircle (2 * Real.pi) => (h (p θ)) ^ 2) haarAddCircle :=
    by
      have hI : Integrable ((fun θ : AddCircle (2 * Real.pi) => h (p θ)) ^ 2)
          haarAddCircle := by
        simpa [IntegrableOn] using
          (hhcont.pow 2).continuousOn.integrableOn_compact
            (μ := haarAddCircle) isCompact_univ
      convert hI using 1
  have hreal :
      (∫ θ : AddCircle (2 * Real.pi), ((h (p θ)) ^ 2).re ∂haarAddCircle) = 0 := by
    have hre :
        (∫ θ : AddCircle (2 * Real.pi), ((h (p θ)) ^ 2).re ∂haarAddCircle) =
          (∫ θ : AddCircle (2 * Real.pi), (h (p θ)) ^ 2 ∂haarAddCircle).re := by
      simpa only [RCLike.re_eq_complex_re] using (integral_re hi)
    rw [hre]
    have hbridge := circleAverage_eq_haar_circle_complex (fun z : ℂ => h z ^ 2) r
    change Real.circleAverage (fun z : ℂ => h z ^ 2) 0 r =
      ∫ θ : AddCircle (2 * Real.pi), (h (p θ)) ^ 2 ∂haarAddCircle at hbridge
    rw [← hbridge, hsq]
    rfl
  have hpoint (θ : AddCircle (2 * Real.pi)) :
      2 * (h (p θ)).re ^ 2 = ‖h (p θ)‖ ^ 2 + ((h (p θ)) ^ 2).re := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, pow_two, Complex.mul_re]
    ring
  have hEq :
      2 * (∫ θ : AddCircle (2 * Real.pi), (h (p θ)).re ^ 2 ∂haarAddCircle) =
        (∫ θ : AddCircle (2 * Real.pi), ‖h (p θ)‖ ^ 2 ∂haarAddCircle) := by
    have hL : Integrable (fun θ : AddCircle (2 * Real.pi) => (h (p θ)).re ^ 2)
        haarAddCircle := by
          have hI : Integrable
              ((Complex.re ∘ fun θ : AddCircle (2 * Real.pi) => h (p θ)) ^ 2)
              haarAddCircle := by
            simpa [IntegrableOn] using
              ((Complex.continuous_re.comp hhcont).pow 2).continuousOn.integrableOn_compact
                (μ := haarAddCircle) isCompact_univ
          convert hI using 1
          funext θ
          rfl
    have hN : Integrable (fun θ : AddCircle (2 * Real.pi) => ‖h (p θ)‖ ^ 2)
        haarAddCircle := by
          have hI : Integrable
              ((fun θ : AddCircle (2 * Real.pi) => ‖h (p θ)‖) ^ 2)
              haarAddCircle := by
            simpa [IntegrableOn] using
              (hhcont.norm.pow 2).continuousOn.integrableOn_compact
                (μ := haarAddCircle) isCompact_univ
          convert hI using 1
    calc
      _ = ∫ θ : AddCircle (2 * Real.pi),
          2 * (h (p θ)).re ^ 2 ∂haarAddCircle := by
            rw [integral_const_mul]
      _ = ∫ θ : AddCircle (2 * Real.pi),
          (‖h (p θ)‖ ^ 2 + ((h (p θ)) ^ 2).re) ∂haarAddCircle := by
            apply integral_congr_ae
            filter_upwards [] with θ
            exact hpoint θ
      _ = _ := by
            have hiRe : Integrable
                (fun θ : AddCircle (2 * Real.pi) => (h (p θ) ^ 2).re)
                haarAddCircle := by
              simpa only [RCLike.re_eq_complex_re] using hi.re
            rw [integral_add hN hiRe, hreal, add_zero]
  simpa only [circleAverage_eq_haar_circle] using hEq

/-- Sharp second-moment comparison for every actual centered exterior map. -/
theorem actualHarmonic_projection_quadratic_circleAverage_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage
      (fun z => (Complex.re (conj ξ * actualHarmonic F z)) ^ 2) 0 r ≤
      2 * r ^ 2 := by
  let c := conj ξ
  let J := projectionAnalytic F c
  let p := exteriorCirclePoint r
  have hcNorm : ‖c‖ = 1 := by simpa [c] using hξ
  have hpNorm (θ : AddCircle (2 * Real.pi)) : ‖p θ‖ = r :=
    exteriorCirclePoint_norm hr0 θ
  have hpBall (θ : AddCircle (2 * Real.pi)) : p θ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, hpNorm]
    exact hr1
  have hpcont : Continuous p := by
    unfold p exteriorCirclePoint
    fun_prop
  have hgcont : Continuous (fun θ : AddCircle (2 * Real.pi) =>
      exteriorForwardGerm F (p θ)) :=
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc).continuousOn.comp_continuous
      hpcont hpBall
  have hJcont : Continuous (fun θ : AddCircle (2 * Real.pi) => J (p θ)) := by
    dsimp [J, projectionAnalytic]
    fun_prop
  have hJintegrable : Integrable
      (fun θ : AddCircle (2 * Real.pi) => ‖J (p θ)‖ ^ 2) haarAddCircle :=
    by
      have hI : Integrable ((fun θ : AddCircle (2 * Real.pi) => ‖J (p θ)‖) ^ 2)
          haarAddCircle := by
        simpa [IntegrableOn] using
          (hJcont.norm.pow 2).continuousOn.integrableOn_compact
            (μ := haarAddCircle) isCompact_univ
      convert hI using 1
  have hgintegrable : Integrable
      (fun θ : AddCircle (2 * Real.pi) => ‖exteriorForwardGerm F (p θ)‖ ^ 2)
      haarAddCircle :=
    by
      have hI : Integrable
          ((fun θ : AddCircle (2 * Real.pi) => ‖exteriorForwardGerm F (p θ)‖) ^ 2)
          haarAddCircle := by
        simpa [IntegrableOn] using
          (hgcont.norm.pow 2).continuousOn.integrableOn_compact
            (μ := haarAddCircle) isCompact_univ
      convert hI using 1
  have hbound (θ : AddCircle (2 * Real.pi)) :
      ‖J (p θ)‖ ^ 2 ≤
        2 * r ^ 2 + 2 * ‖exteriorForwardGerm F (p θ)‖ ^ 2 := by
    have hn := norm_add_le (conj c * p θ) (c * exteriorForwardGerm F (p θ))
    have hfirst : ‖conj c * p θ‖ = r := by
      rw [norm_mul, Complex.norm_conj, hcNorm, one_mul, hpNorm]
    have hsecond : ‖c * exteriorForwardGerm F (p θ)‖ =
        ‖exteriorForwardGerm F (p θ)‖ := by
      rw [norm_mul, hcNorm, one_mul]
    dsimp [J, projectionAnalytic]
    rw [hfirst, hsecond] at hn
    nlinarith [sq_nonneg (r - ‖exteriorForwardGerm F (p θ)‖),
      norm_nonneg (conj c * p θ + c * exteriorForwardGerm F (p θ))]
  have hJenergy :
      Real.circleAverage (fun z : ℂ => ‖J z‖ ^ 2) 0 r ≤ 4 * r ^ 2 := by
    rw [circleAverage_eq_haar_circle]
    have hupper :
        (∫ θ : AddCircle (2 * Real.pi), ‖J (p θ)‖ ^ 2 ∂haarAddCircle) ≤
          ∫ θ : AddCircle (2 * Real.pi),
            (2 * r ^ 2 + 2 * ‖exteriorForwardGerm F (p θ)‖ ^ 2) ∂haarAddCircle := by
      apply integral_mono hJintegrable
      · exact (integrable_const _).add (hgintegrable.const_mul _)
      · exact hbound
    have hgEnergy := exteriorForwardGerm_circle_energy_le F hc hr0 hr1
    rw [circleAverage_eq_haar_circle] at hgEnergy
    calc
      _ ≤ ∫ θ : AddCircle (2 * Real.pi),
            (2 * r ^ 2 + 2 * ‖exteriorForwardGerm F (p θ)‖ ^ 2) ∂haarAddCircle := hupper
      _ = 2 * r ^ 2 + 2 *
            (∫ θ : AddCircle (2 * Real.pi),
              ‖exteriorForwardGerm F (p θ)‖ ^ 2 ∂haarAddCircle) := by
        rw [integral_add (integrable_const _) (hgintegrable.const_mul _),
          integral_const, integral_const_mul]
        simp
      _ ≤ 4 * r ^ 2 := by linarith
  have hsub : sphere (0 : ℂ) |r| ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    have hzNorm : ‖z‖ = r := by
      simpa [mem_sphere, dist_zero_right, abs_of_pos hr0] using hz
    simpa [mem_ball, dist_zero_right, hzNorm] using hr1
  have hJcontCircle : ContinuousOn J (sphere (0 : ℂ) |r|) :=
    (projectionAnalytic_analyticOnNhd F hc c).continuousOn.mono hsub
  have hhalf := real_square_circleAverage_eq_half_energy J r hJcontCircle
    (projectionAnalytic_sq_circleAverage_zero F hc c hr0.le hr1)
  have hreflection :
      Real.circleAverage
        (fun z => (Complex.re (c * actualHarmonic F z)) ^ 2) 0 r =
      Real.circleAverage (fun z => (J z).re ^ 2) 0 r := by
    rw [← circleAverage_comp_conj_zero (fun z : ℂ =>
      (Complex.re (c * actualHarmonic F z)) ^ 2) r]
    apply Real.circleAverage_congr_sphere
    intro z hz
    exact congrArg (fun x : ℝ => x ^ 2)
      (actualHarmonic_projection_reflection F c z)
  change Real.circleAverage
      (fun z => (Complex.re (c * actualHarmonic F z)) ^ 2) 0 r ≤ _
  rw [hreflection]
  linarith

/-- The unrotated slit attains the quadratic-test constant on every
interior circle. -/
theorem slitMap_one_projection_quadratic_circleAverage_eq
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage
      (fun z => (Complex.re (conj (1 : ℂ) * actualHarmonic (slitMap 1) z)) ^ 2)
      0 r = 2 * r ^ 2 := by
  have hc : CenteredExteriorUnivalent (slitMap 1) :=
    slitMap_centeredExteriorUnivalent 1 (by norm_num)
  have hg : exteriorForwardGerm (slitMap 1) = fun z : ℂ => z := by
    funext z
    by_cases hz : z = 0
    · simp [exteriorForwardGerm, hz]
    · simp [exteriorForwardGerm, slitMap, hz, div_eq_mul_inv]
  have hJ : projectionAnalytic (slitMap 1) 1 = fun z : ℂ => 2 * z := by
    funext z
    simp [projectionAnalytic, hg]
    ring
  have hsub : sphere (0 : ℂ) |r| ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    have hzNorm : ‖z‖ = r := by
      simpa [mem_sphere, dist_zero_right, abs_of_pos hr0] using hz
    simpa [mem_ball, dist_zero_right, hzNorm] using hr1
  have hcont : ContinuousOn (projectionAnalytic (slitMap 1) 1)
      (sphere (0 : ℂ) |r|) :=
    (projectionAnalytic_analyticOnNhd _ hc 1).continuousOn.mono hsub
  have hhalf := real_square_circleAverage_eq_half_energy
    (projectionAnalytic (slitMap 1) 1) r hcont
    (projectionAnalytic_sq_circleAverage_zero _ hc 1 hr0.le hr1)
  have hpoly (z : ℂ) :
      (∑ j ∈ Finset.range 2, (if j = 1 then (2 : ℂ) else 0) * z ^ j) = 2 * z := by
    simp
  have hfinite := finiteTaylor_circleAverage_energy
    (fun j : ℕ => if j = 1 then (2 : ℂ) else 0) r hr0.le 2
  have henergy :
      Real.circleAverage (fun z : ℂ => ‖projectionAnalytic (slitMap 1) 1 z‖ ^ 2)
        0 r = 4 * r ^ 2 := by
    simp only [hJ, hpoly] at hfinite ⊢
    norm_num [Finset.sum_range_succ] at hfinite
    simpa [norm_mul] using hfinite
  have hpoint (z : ℂ) :
      (Complex.re (conj (1 : ℂ) * actualHarmonic (slitMap 1) z)) ^ 2 =
      (projectionAnalytic (slitMap 1) 1 z).re ^ 2 := by
    simp [actualHarmonic, hg, hJ, Complex.add_re, Complex.conj_re]
    ring
  have hcircle :
      Real.circleAverage
        (fun z => (Complex.re (conj (1 : ℂ) * actualHarmonic (slitMap 1) z)) ^ 2)
        0 r =
      Real.circleAverage
        (fun z => (projectionAnalytic (slitMap 1) 1 z).re ^ 2) 0 r := by
    apply Real.circleAverage_congr_sphere
    intro z _
    exact hpoint z
  rw [henergy] at hhalf
  rw [hcircle]
  linarith

end SpringerLean
