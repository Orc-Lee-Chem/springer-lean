import SpringerLean.Round88FaberActual

namespace SpringerLean

/-- An analytic reciprocal factor contributes both a leading Fourier
frequency and a derivative of its negative-frequency tail. The exact signs
are needed before the Faber boundary can be inserted in the signed Green
area formula. -/
theorem faberBoundaryFactor_angular_deriv
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R))
    (i : ℤ) (θ : ℝ) :
    deriv (fun t : ℝ =>
      fourier i (t : AddCircle (2 * Real.pi)) *
        h (fourier (-1) (t : AddCircle (2 * Real.pi)))) θ =
      Complex.I * fourier i (θ : AddCircle (2 * Real.pi)) *
        ((i : ℂ) * h (fourier (-1) (θ : AddCircle (2 * Real.pi))) -
          fourier (-1) (θ : AddCircle (2 * Real.pi)) *
            deriv h (fourier (-1) (θ : AddCircle (2 * Real.pi)))) := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
  have houter : HasDerivAt
      (fun t : ℝ => fourier i (t : AddCircle (2 * Real.pi)))
      (Complex.I * (i : ℂ) * fourier i
        (θ : AddCircle (2 * Real.pi))) θ := by
    convert hasDerivAt_fourier (2 * Real.pi) i θ using 1
    push_cast
    field_simp [hπ]
  have hinner : HasDerivAt
      (fun t : ℝ => fourier (-1) (t : AddCircle (2 * Real.pi)))
      (-Complex.I * fourier (-1)
        (θ : AddCircle (2 * Real.pi))) θ := by
    convert hasDerivAt_fourier (2 * Real.pi) (-1) θ using 1
    push_cast
    field_simp [hπ]
  have hu : fourier (-1) (θ : AddCircle (2 * Real.pi)) ∈
      Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, fourier_apply, Circle.norm_coe]
    exact hR
  have hA : DifferentiableAt ℂ h
      (fourier (-1) (θ : AddCircle (2 * Real.pi))) :=
    (hh _ hu).differentiableAt
  have hcomp := hA.hasDerivAt.comp θ hinner
  have hprod := houter.mul hcomp
  have hderiv := hprod.deriv
  have hfun :
      (fun t : ℝ => fourier i (t : AddCircle (2 * Real.pi))) *
        (h ∘ fun t : ℝ => fourier (-1)
          (t : AddCircle (2 * Real.pi))) =
      (fun t : ℝ => fourier i (t : AddCircle (2 * Real.pi)) *
        h (fourier (-1) (t : AddCircle (2 * Real.pi)))) := by
    funext t
    rfl
  rw [hfun] at hderiv
  have hderiv' : deriv (fun t : ℝ =>
      fourier i (t : AddCircle (2 * Real.pi)) *
        h (fourier (-1) (t : AddCircle (2 * Real.pi)))) θ =
      Complex.I * (i : ℂ) * fourier i
          (θ : AddCircle (2 * Real.pi)) *
          h (fourier (-1) (θ : AddCircle (2 * Real.pi))) +
        fourier i (θ : AddCircle (2 * Real.pi)) *
          (deriv h (fourier (-1) (θ : AddCircle (2 * Real.pi))) *
            (-Complex.I * fourier (-1)
              (θ : AddCircle (2 * Real.pi)))) := by
    simpa only [Function.comp_def] using hderiv
  rw [hderiv']
  ring

/-- The actual Faber boundary factor is differentiable at every real angle. -/
theorem faberBoundaryFactor_differentiable
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) (i : ℤ) :
    Differentiable ℝ (fun t : ℝ =>
      fourier i (t : AddCircle (2 * Real.pi)) *
        h (fourier (-1) (t : AddCircle (2 * Real.pi)))) := by
  intro θ
  have houter := hasDerivAt_fourier (2 * Real.pi) i θ
  have hinner := hasDerivAt_fourier (2 * Real.pi) (-1) θ
  have hu : fourier (-1) (θ : AddCircle (2 * Real.pi)) ∈
      Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, fourier_apply, Circle.norm_coe]
    exact hR
  have hcomp := ((hh _ hu).differentiableAt.hasDerivAt).comp θ hinner
  have hprod := houter.mul hcomp
  convert hprod.differentiableAt using 1
  funext t
  rfl

/-- The actual angular derivative is continuous; this supplies the
integrability side of the oriented Green boundary limit. -/
theorem faberBoundaryFactor_deriv_continuous
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) (i : ℤ) :
    Continuous (deriv (fun t : ℝ =>
      fourier i (t : AddCircle (2 * Real.pi)) *
        h (fourier (-1) (t : AddCircle (2 * Real.pi))))) := by
  have houter : Continuous (fun θ : ℝ =>
      fourier i (θ : AddCircle (2 * Real.pi))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hasDerivAt_fourier (2 * Real.pi) i θ).continuousAt
  have hinner : Continuous (fun θ : ℝ =>
      fourier (-1) (θ : AddCircle (2 * Real.pi))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hasDerivAt_fourier (2 * Real.pi) (-1) θ).continuousAt
  have hvalue : Continuous (fun θ : ℝ =>
      h (fourier (-1) (θ : AddCircle (2 * Real.pi)))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hu : fourier (-1) (θ : AddCircle (2 * Real.pi)) ∈
        Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right, fourier_apply, Circle.norm_coe]
      exact hR
    exact ContinuousAt.comp' (f := fun t : ℝ => fourier (-1)
      (t : AddCircle (2 * Real.pi)))
      ((hh _ hu).continuousAt) hinner.continuousAt
  have hvalueDeriv : Continuous (fun θ : ℝ =>
      deriv h (fourier (-1) (θ : AddCircle (2 * Real.pi)))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hu : fourier (-1) (θ : AddCircle (2 * Real.pi)) ∈
        Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right, fourier_apply, Circle.norm_coe]
      exact hR
    exact ContinuousAt.comp' (f := fun t : ℝ => fourier (-1)
      (t : AddCircle (2 * Real.pi)))
      (((hh.deriv) _ hu).continuousAt) hinner.continuousAt
  have hformula :
      (deriv (fun t : ℝ =>
        fourier i (t : AddCircle (2 * Real.pi)) *
          h (fourier (-1) (t : AddCircle (2 * Real.pi))))) =
      (fun θ : ℝ =>
        Complex.I * fourier i (θ : AddCircle (2 * Real.pi)) *
          ((i : ℂ) * h (fourier (-1) (θ : AddCircle (2 * Real.pi))) -
            fourier (-1) (θ : AddCircle (2 * Real.pi)) *
              deriv h (fourier (-1) (θ : AddCircle (2 * Real.pi))))) := by
    funext θ
    exact faberBoundaryFactor_angular_deriv h hR hh i θ
  rw [hformula]
  exact (continuous_const.mul houter).mul
    ((continuous_const.mul hvalue).sub (hinner.mul hvalueDeriv))

/-- A finite derivative-read Taylor polynomial differentiates by shifting
its coefficient index. This exact finite identity is later inserted into
the angular derivative of each actual Faber boundary approximation. -/
theorem actualTaylorPartial_deriv
    (c : ℕ → ℂ) (M : ℕ) (u : ℂ) :
    deriv (fun v : ℂ => ∑ j ∈ Finset.range (M + 1), c j * v ^ j) u =
      ∑ k ∈ Finset.range M, (k + 1 : ℂ) * c (k + 1) * u ^ k := by
  have hterm (j : ℕ) : HasDerivAt
      (fun v : ℂ => c j * v ^ j)
      (c j * ((j : ℂ) * u ^ (j - 1))) u := by
    simpa [id_eq] using
      ((hasDerivAt_id u).pow j).const_mul (c j)
  have hsum : HasDerivAt
      (∑ j ∈ Finset.range (M + 1), fun v : ℂ => c j * v ^ j)
      (∑ j ∈ Finset.range (M + 1),
        c j * ((j : ℂ) * u ^ (j - 1))) u := by
    apply HasDerivAt.sum
    intro j hj
    exact hterm j
  have hderiv := hsum.deriv
  have hfun :
      (∑ j ∈ Finset.range (M + 1), fun v : ℂ => c j * v ^ j) =
      (fun v : ℂ => ∑ j ∈ Finset.range (M + 1), c j * v ^ j) := by
    funext v
    simp only [Finset.sum_apply]
  rw [hfun] at hderiv
  change deriv (fun v : ℂ =>
    ∑ j ∈ Finset.range (M + 1), c j * v ^ j) u = _
  rw [hderiv, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.cast_add, Nat.cast_one]
  have hkidx : k + 1 - 1 = k := by omega
  rw [hkidx]
  ring

/-- The angular derivative of a finite Laurent/Faber boundary approximation
is expressed using the same coefficients in its value and derivative tails. -/
theorem faberBoundaryPartial_angular_deriv
    (c : ℕ → ℂ) (i : ℤ) (M : ℕ) (θ : ℝ) :
    deriv (fun t : ℝ =>
      fourier i (t : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          c j * (fourier (-1) (t : AddCircle (2 * Real.pi))) ^ j)) θ =
      Complex.I * fourier i (θ : AddCircle (2 * Real.pi)) *
        ((i : ℂ) *
            (∑ j ∈ Finset.range (M + 1),
              c j * (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j) -
          fourier (-1) (θ : AddCircle (2 * Real.pi)) *
            (∑ k ∈ Finset.range M,
              (k + 1 : ℂ) * c (k + 1) *
                (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ k)) := by
  let A : ℂ → ℂ := fun u =>
    ∑ j ∈ Finset.range (M + 1), c j * u ^ j
  have hA : AnalyticOnNhd ℂ A (Metric.ball 0 2) := by
    intro u hu
    dsimp [A]
    fun_prop
  have h := faberBoundaryFactor_angular_deriv A
    (by norm_num : (1 : ℝ) < 2) hA i θ
  rw [actualTaylorPartial_deriv c M] at h
  simpa only [A] using h

theorem faberBoundaryPartial_differentiable
    (c : ℕ → ℂ) (i : ℤ) (M : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
      fourier i (t : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          c j * (fourier (-1) (t : AddCircle (2 * Real.pi))) ^ j)) := by
  let A : ℂ → ℂ := fun u =>
    ∑ j ∈ Finset.range (M + 1), c j * u ^ j
  have hA : AnalyticOnNhd ℂ A (Metric.ball 0 2) := by
    intro u hu
    dsimp [A]
    fun_prop
  simpa only [A] using
    (faberBoundaryFactor_differentiable A
      (by norm_num : (1 : ℝ) < 2) hA i)

theorem faberBoundaryPartial_deriv_continuous
    (c : ℕ → ℂ) (i : ℤ) (M : ℕ) :
    Continuous (deriv (fun t : ℝ =>
      fourier i (t : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          c j * (fourier (-1) (t : AddCircle (2 * Real.pi))) ^ j))) := by
  let A : ℂ → ℂ := fun u =>
    ∑ j ∈ Finset.range (M + 1), c j * u ^ j
  have hA : AnalyticOnNhd ℂ A (Metric.ball 0 2) := by
    intro u hu
    dsimp [A]
    fun_prop
  simpa only [A] using
    (faberBoundaryFactor_deriv_continuous A
      (by norm_num : (1 : ℝ) < 2) hA i)

/-- The finite Faber Laurent boundary values converge uniformly in the
real angle, for any analytic reciprocal factor beyond the unit circle. -/
theorem faberBoundaryPartial_value_uniform
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) (i : ℤ) :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : ℝ =>
        fourier i (θ : AddCircle (2 * Real.pi)) *
          (∑ j ∈ Finset.range (M + 1),
            actualTaylorCoeff h j *
              (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j))
      (fun θ : ℝ =>
        fourier i (θ : AddCircle (2 * Real.pi)) *
          h (fourier (-1) (θ : AddCircle (2 * Real.pi))))
      Filter.atTop Set.univ := by
  have hbase := analytic_actualTaylor_uniform_unitCircle h hR hh
  have hshift : TendstoUniformlyOn
      (fun M : ℕ => fun θ : AddCircle (2 * Real.pi) =>
        ∑ j ∈ Finset.range (M + 1),
          actualTaylorCoeff h j * (fourier (-1) θ) ^ j)
      (fun θ => h (fourier (-1) θ)) Filter.atTop Set.univ := by
    intro u hu
    exact (Filter.tendsto_add_atTop_nat 1).eventually (hbase u hu)
  have hreal := (hshift.comp
    (fun θ : ℝ => (θ : AddCircle (2 * Real.pi)))).mono
      (by intro θ hθ; trivial : Set.univ ⊆
        (fun θ : ℝ => (θ : AddCircle (2 * Real.pi))) ⁻¹' Set.univ)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hreal ε hε)]
    with M hM θ hθ
  have ht := hM θ (Set.mem_univ θ)
  have hnorm : ‖fourier i (θ : AddCircle (2 * Real.pi))‖ = 1 := by
    rw [fourier_apply, Circle.norm_coe]
  rw [dist_eq_norm] at ht ⊢
  simp only [← mul_sub, norm_mul, hnorm, one_mul]
  exact ht

/-- The derivatives of finite Faber boundary approximations converge
uniformly to the derivative of the genuine analytic boundary curve. -/
theorem faberBoundaryPartial_angular_deriv_uniform
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) (i : ℤ) :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : ℝ =>
        deriv (fun t : ℝ =>
          fourier i (t : AddCircle (2 * Real.pi)) *
            (∑ j ∈ Finset.range (M + 1),
              actualTaylorCoeff h j *
                (fourier (-1) (t : AddCircle (2 * Real.pi))) ^ j)) θ)
      (fun θ : ℝ =>
        deriv (fun t : ℝ =>
          fourier i (t : AddCircle (2 * Real.pi)) *
            h (fourier (-1) (t : AddCircle (2 * Real.pi)))) θ)
      Filter.atTop Set.univ := by
  let A (M : ℕ) (θ : ℝ) :=
    ∑ j ∈ Finset.range (M + 1),
      actualTaylorCoeff h j *
        (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j
  let D (M : ℕ) (θ : ℝ) :=
    ∑ k ∈ Finset.range M,
      (k + 1 : ℂ) * actualTaylorCoeff h (k + 1) *
        (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ k
  let u (θ : ℝ) := fourier (-1) (θ : AddCircle (2 * Real.pi))
  have hv0 := analytic_actualTaylor_uniform_unitCircle h hR hh
  have hvshift : TendstoUniformlyOn
      (fun M : ℕ => fun θ : AddCircle (2 * Real.pi) =>
        ∑ j ∈ Finset.range (M + 1),
          actualTaylorCoeff h j * (fourier (-1) θ) ^ j)
      (fun θ => h (fourier (-1) θ)) Filter.atTop Set.univ := by
    intro v hv
    exact (Filter.tendsto_add_atTop_nat 1).eventually (hv0 v hv)
  have hvreal : TendstoUniformlyOn A (fun θ => h (u θ))
      Filter.atTop Set.univ := by
    simpa only [A, u, Function.comp_def, Set.preimage_univ] using
      (hvshift.comp (fun θ : ℝ => (θ : AddCircle (2 * Real.pi))))
  have hd0 := analytic_actualTaylor_deriv_uniform_unitCircle h hR hh
  have hdreal : TendstoUniformlyOn D (fun θ => deriv h (u θ))
      Filter.atTop Set.univ := by
    simpa only [D, u, Function.comp_def, Set.preimage_univ] using
      (hd0.comp (fun θ : ℝ => (θ : AddCircle (2 * Real.pi))))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ : ℝ := ε / (‖(i : ℂ)‖ + 2)
  have hden : 0 < ‖(i : ℂ)‖ + 2 := by positivity
  have hδpos : 0 < δ := div_pos hε hden
  have hδeq : (‖(i : ℂ)‖ + 2) * δ = ε := by
    dsimp [δ]
    field_simp [hden.ne']
  filter_upwards
      [(Metric.tendstoUniformlyOn_iff.mp hvreal δ hδpos),
       (Metric.tendstoUniformlyOn_iff.mp hdreal δ hδpos)]
    with M hv hd θ hθ
  have hvθ := hv θ (Set.mem_univ θ)
  have hdθ := hd θ (Set.mem_univ θ)
  have hnormu : ‖u θ‖ = 1 := by
    change ‖fourier (-1) (θ : AddCircle (2 * Real.pi))‖ = 1
    rw [fourier_apply, Circle.norm_coe]
  have hnormouter : ‖Complex.I * fourier i
      (θ : AddCircle (2 * Real.pi))‖ = 1 := by
    rw [norm_mul, Complex.norm_I, fourier_apply, Circle.norm_coe]
    norm_num
  rw [faberBoundaryPartial_angular_deriv
      (actualTaylorCoeff h) i M θ,
    faberBoundaryFactor_angular_deriv h hR hh i θ]
  rw [dist_comm]
  change dist
    (Complex.I * fourier i (θ : AddCircle (2 * Real.pi)) *
      ((i : ℂ) * A M θ - u θ * D M θ))
    (Complex.I * fourier i (θ : AddCircle (2 * Real.pi)) *
      ((i : ℂ) * h (u θ) - u θ * deriv h (u θ))) < ε
  rw [dist_eq_norm, ← mul_sub, norm_mul, hnormouter, one_mul]
  have hring :
      (i : ℂ) * A M θ - u θ * D M θ -
        ((i : ℂ) * h (u θ) - u θ * deriv h (u θ)) =
      (i : ℂ) * (A M θ - h (u θ)) -
        u θ * (D M θ - deriv h (u θ)) := by ring
  rw [hring]
  have hbound :
      ‖(i : ℂ) * (A M θ - h (u θ)) -
        u θ * (D M θ - deriv h (u θ))‖ ≤
      ‖(i : ℂ)‖ * ‖A M θ - h (u θ)‖ +
        ‖D M θ - deriv h (u θ)‖ := by
    calc
      _ ≤ ‖(i : ℂ) * (A M θ - h (u θ))‖ +
          ‖u θ * (D M θ - deriv h (u θ))‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul, hnormu, one_mul]
  rw [dist_comm, dist_eq_norm] at hvθ hdθ
  have hm : ‖(i : ℂ)‖ * ‖A M θ - h (u θ)‖ ≤
      ‖(i : ℂ)‖ * δ :=
    mul_le_mul_of_nonneg_left hvθ.le (norm_nonneg _)
  calc
    _ ≤ ‖(i : ℂ)‖ * ‖A M θ - h (u θ)‖ +
          ‖D M θ - deriv h (u θ)‖ := hbound
    _ ≤ ‖(i : ℂ)‖ * δ + ‖D M θ - deriv h (u θ)‖ :=
      by simpa only [add_comm] using
        add_le_add_right hm ‖D M θ - deriv h (u θ)‖
    _ < ‖(i : ℂ)‖ * δ + δ := by
      simpa only [add_comm] using add_lt_add_left hdθ (‖(i : ℂ)‖ * δ)
    _ < ε := by nlinarith [hδeq, hδpos]

/-- The oriented Green boundary integral of a single actual Faber factor
is the limit of the signed integrals of its finite Laurent approximants.
All continuity and integrability requirements are discharged from the
original analyticity on a disk larger than the unit circle. -/
theorem faberBoundaryFactor_oriented_integral_tendsto
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) (i : ℤ) :
    let γn : ℕ → ℝ → ℂ := fun M θ =>
      fourier i (θ : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          actualTaylorCoeff h j *
            (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)
    let γ : ℝ → ℂ := fun θ =>
      fourier i (θ : AddCircle (2 * Real.pi)) *
        h (fourier (-1) (θ : AddCircle (2 * Real.pi)))
    Filter.Tendsto
      (fun M => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γn M θ).re * deriv (fun t => (γn M t).im) θ)
      Filter.atTop
      (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γ θ).re * (deriv γ θ).im)) := by
  let γn : ℕ → ℝ → ℂ := fun M θ =>
    fourier i (θ : AddCircle (2 * Real.pi)) *
      (∑ j ∈ Finset.range (M + 1),
        actualTaylorCoeff h j *
          (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)
  let γ : ℝ → ℂ := fun θ =>
    fourier i (θ : AddCircle (2 * Real.pi)) *
      h (fourier (-1) (θ : AddCircle (2 * Real.pi)))
  have hval : TendstoUniformlyOn γn γ Filter.atTop
      (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    simpa only [γn, γ] using
      (faberBoundaryPartial_value_uniform h hR hh i).mono
        (Set.subset_univ _)
  have hder : TendstoUniformlyOn
      (fun M θ => deriv (γn M) θ) (deriv γ) Filter.atTop
      (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    simpa only [γn, γ] using
      (faberBoundaryPartial_angular_deriv_uniform h hR hh i).mono
        (Set.subset_univ _)
  have hγsmooth : Differentiable ℝ γ := by
    simpa only [γ] using faberBoundaryFactor_differentiable h hR hh i
  have hγdercont : Continuous (deriv γ) := by
    simpa only [γ] using faberBoundaryFactor_deriv_continuous h hR hh i
  have hsmooth : ∀ M, Differentiable ℝ (γn M) := by
    intro M
    simpa only [γn] using
      faberBoundaryPartial_differentiable (actualTaylorCoeff h) i M
  have hdercont : ∀ M, Continuous (deriv (γn M)) := by
    intro M
    simpa only [γn] using
      faberBoundaryPartial_deriv_continuous (actualTaylorCoeff h) i M
  exact oriented_boundary_integral_tendsto_of_uniform_value_deriv
    γn γ hval hder hγsmooth.continuous.continuousOn
    hγdercont.continuousOn hsmooth hdercont

end SpringerLean
