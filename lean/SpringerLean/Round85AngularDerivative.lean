import SpringerLean.Round84FaberLaurent

namespace SpringerLean

/-- The actual angular derivative of the regularized correction has the
expected `-i s² e^{-iθ}` factor. This is the same actual forward germ used
in the boundary Laurent expansion. -/
theorem rescaleExterior_boundary_correction_angular_deriv
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (θ : ℝ) :
    deriv (fun t : ℝ =>
      (s : ℂ) * exteriorForwardGerm F
        ((s : ℂ) * fourier (-1) (t : AddCircle (2 * Real.pi)))) θ =
      -(s : ℂ) ^ 2 * Complex.I * fourier (-1)
        (θ : AddCircle (2 * Real.pi)) *
        deriv (exteriorForwardGerm F)
          ((s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi))) := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
  have hFourier : HasDerivAt
      (fun t : ℝ => fourier (-1) (t : AddCircle (2 * Real.pi)))
      (-Complex.I * fourier (-1) (θ : AddCircle (2 * Real.pi))) θ := by
    convert hasDerivAt_fourier (2 * Real.pi) (-1) θ using 1
    push_cast
    field_simp [hπ]
  have hinner := hFourier.const_mul (s : ℂ)
  have hnorm : ‖(s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi))‖ = s := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0, fourier_apply, Circle.norm_coe, mul_one]
  have hu : (s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi)) ∈
      Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact hs1
  have hG : DifferentiableAt ℂ (exteriorForwardGerm F)
      ((s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi))) :=
    ((exteriorForwardGerm_analyticOnNhd_unitBall F hc) _ hu).differentiableAt
  have hcomp := hG.hasDerivAt.comp θ hinner
  have hout := hcomp.const_mul (s : ℂ)
  have hderiv := hout.deriv
  simp only [Function.comp_def] at hderiv
  rw [hderiv]
  ring


/-- The angular derivative of a finite regularized Laurent correction,
written with the derivative Taylor polynomial of one lower degree. -/
theorem regularizedLaurentPartial_angular_deriv
    (b : ℕ → ℂ) (s : ℝ) (M : ℕ) (θ : ℝ) :
    deriv (fun t : ℝ =>
      (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
        b j * ((s : ℂ) * fourier (-1)
          (t : AddCircle (2 * Real.pi))) ^ j) θ =
      -(s : ℂ) ^ 2 * Complex.I * fourier (-1)
        (θ : AddCircle (2 * Real.pi)) *
        (∑ k ∈ Finset.range M,
          (k + 1 : ℂ) * b (k + 1) *
            ((s : ℂ) * fourier (-1)
              (θ : AddCircle (2 * Real.pi))) ^ k) := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
  have hFourier : HasDerivAt
      (fun t : ℝ => fourier (-1) (t : AddCircle (2 * Real.pi)))
      (-Complex.I * fourier (-1) (θ : AddCircle (2 * Real.pi))) θ := by
    convert hasDerivAt_fourier (2 * Real.pi) (-1) θ using 1
    push_cast
    field_simp [hπ]
  let u : ℝ → ℂ := fun t => (s : ℂ) *
    fourier (-1) (t : AddCircle (2 * Real.pi))
  have hu : HasDerivAt u
      ((s : ℂ) * (-Complex.I * fourier (-1)
        (θ : AddCircle (2 * Real.pi)))) θ := hFourier.const_mul (s : ℂ)
  have hterm (j : ℕ) : HasDerivAt
      (fun t : ℝ => b j * (u t) ^ j)
      (b j * ((j : ℂ) * (u θ) ^ (j - 1) *
        ((s : ℂ) * (-Complex.I * fourier (-1)
          (θ : AddCircle (2 * Real.pi)))))) θ := by
    simpa only [Pi.pow_apply] using (hu.pow j).const_mul (b j)
  have hsum : HasDerivAt
      (∑ j ∈ Finset.range (M + 1), fun t : ℝ => b j * (u t) ^ j)
      (∑ j ∈ Finset.range (M + 1),
        b j * ((j : ℂ) * (u θ) ^ (j - 1) *
          ((s : ℂ) * (-Complex.I * fourier (-1)
            (θ : AddCircle (2 * Real.pi)))))) θ := by
    apply HasDerivAt.sum
    intro j hj
    exact hterm j
  have hout := hsum.const_mul (s : ℂ)
  have hderiv := hout.deriv
  simp only [Finset.sum_apply] at hderiv
  change deriv (fun t : ℝ => (s : ℂ) *
      ∑ j ∈ Finset.range (M + 1), b j * (u t) ^ j) θ = _
  rw [hderiv]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [u]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- The angular derivatives of the finite Laurent corrections converge
uniformly to the angular derivative of the actual regularized correction
on the entire real angle line. The proof uses the same `s²` factor in both
expressions and the already checked uniform derivative Taylor series. -/
theorem rescaleExterior_boundary_correction_angular_deriv_uniform
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : ℝ =>
        deriv (fun t : ℝ =>
          (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
            exteriorForwardCoeff F j *
              ((s : ℂ) * fourier (-1)
                (t : AddCircle (2 * Real.pi))) ^ j) θ)
      (fun θ : ℝ =>
        deriv (fun t : ℝ =>
          (s : ℂ) * exteriorForwardGerm F
            ((s : ℂ) * fourier (-1)
              (t : AddCircle (2 * Real.pi)))) θ)
      Filter.atTop Set.univ := by
  have hbase := rescaleExterior_boundary_germ_deriv_uniform F hc hs0 hs1
  have hreal := (hbase.comp
    (fun θ : ℝ => (θ : AddCircle (2 * Real.pi)))).mono
      (by intro θ hθ; trivial : Set.univ ⊆
        (fun θ : ℝ => (θ : AddCircle (2 * Real.pi))) ⁻¹' Set.univ)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hreal ε hε)]
    with M hM θ hθ
  have htail := hM θ (by trivial)
  have hfactor :
      ‖-(s : ℂ) ^ 2 * Complex.I * fourier (-1)
        (θ : AddCircle (2 * Real.pi))‖ ≤ 1 := by
    simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs0, Complex.norm_I,
      fourier_apply, Circle.norm_coe, mul_one]
    nlinarith
  rw [rescaleExterior_boundary_correction_angular_deriv F hc hs0 hs1 θ,
    regularizedLaurentPartial_angular_deriv
      (exteriorForwardCoeff F) s M θ,
    dist_eq_norm]
  have hnorm :
      ‖(-(s : ℂ) ^ 2 * Complex.I * fourier (-1)
          (θ : AddCircle (2 * Real.pi))) *
        (deriv (exteriorForwardGerm F)
            ((s : ℂ) * fourier (-1)
              (θ : AddCircle (2 * Real.pi))) -
          ∑ k ∈ Finset.range M,
            (k + 1 : ℂ) * exteriorForwardCoeff F (k + 1) *
              ((s : ℂ) * fourier (-1)
                (θ : AddCircle (2 * Real.pi))) ^ k)‖ ≤
      ‖deriv (exteriorForwardGerm F)
          ((s : ℂ) * fourier (-1)
            (θ : AddCircle (2 * Real.pi))) -
        ∑ k ∈ Finset.range M,
          (k + 1 : ℂ) * exteriorForwardCoeff F (k + 1) *
            ((s : ℂ) * fourier (-1)
              (θ : AddCircle (2 * Real.pi))) ^ k‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hfactor
  convert lt_of_le_of_lt hnorm (by simpa only [Function.comp_def, dist_eq_norm] using htail) using 1
  ring
end SpringerLean