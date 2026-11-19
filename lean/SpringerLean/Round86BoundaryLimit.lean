import SpringerLean.Round85AngularDerivative
import Mathlib.Order.Filter.AtTopBot.Basic

namespace SpringerLean

open MeasureTheory

/-- Multiplication of real and imaginary coordinates preserves uniform
convergence when the two limiting coordinates are bounded on the set. This
explicit bounded version applies to the compact Fourier angle interval. -/
theorem uniform_re_mul_im_of_uniform
    {f_n g_n : ℕ → ℝ → ℂ} {f g : ℝ → ℂ} {I : Set ℝ}
    (hf : TendstoUniformlyOn f_n f Filter.atTop I)
    (hg : TendstoUniformlyOn g_n g Filter.atTop I)
    (hC : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ I, |(f θ).re| ≤ C)
    (hD : ∃ D : ℝ, 0 ≤ D ∧ ∀ θ ∈ I, |(g θ).im| ≤ D) :
    TendstoUniformlyOn
      (fun n θ => (f_n n θ).re * (g_n n θ).im)
      (fun θ => (f θ).re * (g θ).im) Filter.atTop I := by
  obtain ⟨C, hC0, hC⟩ := hC
  obtain ⟨D, hD0, hD⟩ := hD
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ : ℝ := ε / (2 * (C + D + 3))
  have hden : 0 < 2 * (C + D + 3) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hf) δ hδ,
    (Metric.tendstoUniformlyOn_iff.mp hg) δ hδ,
    (Metric.tendstoUniformlyOn_iff.mp hg) 1 (by norm_num)]
      with n hfn hgn hgn1 θ hθ
  have hfa : |(f_n n θ).re - (f θ).re| < δ := by
    calc
      _ = |(f_n n θ - f θ).re| := by rw [Complex.sub_re]
      _ ≤ ‖f_n n θ - f θ‖ := Complex.abs_re_le_norm _
      _ < δ := by simpa only [dist_eq_norm, norm_sub_rev] using hfn θ hθ
  have hgb : |(g_n n θ).im - (g θ).im| < δ := by
    calc
      _ = |(g_n n θ - g θ).im| := by rw [Complex.sub_im]
      _ ≤ ‖g_n n θ - g θ‖ := Complex.abs_im_le_norm _
      _ < δ := by simpa only [dist_eq_norm, norm_sub_rev] using hgn θ hθ
  have hgb1 : |(g_n n θ).im - (g θ).im| < 1 := by
    calc
      _ = |(g_n n θ - g θ).im| := by rw [Complex.sub_im]
      _ ≤ ‖g_n n θ - g θ‖ := Complex.abs_im_le_norm _
      _ < 1 := by simpa only [dist_eq_norm, norm_sub_rev] using hgn1 θ hθ
  have hgbound : |(g_n n θ).im| ≤ D + 1 := by
    calc
      _ = |((g_n n θ).im - (g θ).im) + (g θ).im| := by ring
      _ ≤ |(g_n n θ).im - (g θ).im| + |(g θ).im| := abs_add_le _ _
      _ ≤ D + 1 := by linarith [hD θ hθ]
  have hfactor :
      |(f_n n θ).re * (g_n n θ).im -
        (f θ).re * (g θ).im| ≤
      |(f_n n θ).re - (f θ).re| * |(g_n n θ).im| +
        |(f θ).re| * |(g_n n θ).im - (g θ).im| := by
    calc
      _ = |((f_n n θ).re - (f θ).re) * (g_n n θ).im +
          (f θ).re * ((g_n n θ).im - (g θ).im)| := by congr 1; ring
      _ ≤ _ := by simpa only [abs_mul] using (abs_add_le
        (((f_n n θ).re - (f θ).re) * (g_n n θ).im)
        ((f θ).re * ((g_n n θ).im - (g θ).im)))
  have hsmall : δ * (C + D + 1) < ε := by
    have hratio : (C + D + 1) / (2 * (C + D + 3)) < 1 := by
      apply (div_lt_iff₀ hden).mpr
      linarith
    calc
      δ * (C + D + 1) = ε * ((C + D + 1) / (2 * (C + D + 3))) := by
        dsimp [δ]
        ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := by ring
  rw [Real.dist_eq]
  rw [abs_sub_comm]
  calc
    _ ≤ |(f_n n θ).re - (f θ).re| * |(g_n n θ).im| +
          |(f θ).re| * |(g_n n θ).im - (g θ).im| := hfactor
    _ ≤ δ * (D + 1) + C * δ := by
      have h1 : |(f_n n θ).re - (f θ).re| * |(g_n n θ).im| ≤
          δ * (D + 1) := by
        exact mul_le_mul hfa.le hgbound (abs_nonneg _) hδ.le
      have h2 : |(f θ).re| * |(g_n n θ).im - (g θ).im| ≤ C * δ := by
        exact mul_le_mul (hC θ hθ) hgb.le (abs_nonneg _) hC0
      linarith
    _ < ε := by nlinarith [hsmall]

/-- The oriented boundary circulation is continuous under uniform convergence
of a smooth complex curve and its angular derivative. This is the analytic
limit step needed to pass the finite signed Fourier identity to actual
regularized exterior boundary values. -/
theorem oriented_boundary_integral_tendsto_of_uniform
    (γn : ℕ → ℝ → ℂ) (γ : ℝ → ℂ)
    (hprod : TendstoUniformlyOn
      (fun n θ => (γn n θ).re * (deriv (γn n) θ).im)
      (fun θ => (γ θ).re * (deriv γ θ).im)
      Filter.atTop (Set.uIcc (0 : ℝ) (2 * Real.pi)))
    (hsmooth : ∀ n, Differentiable ℝ (γn n))
    (hdercont : ∀ n, Continuous (deriv (γn n))) :
    Filter.Tendsto
      (fun n => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γn n θ).re * deriv (fun t => (γn n t).im) θ)
      Filter.atTop
      (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γ θ).re * (deriv γ θ).im)) := by
  have hcont : ∀ᶠ n : ℕ in Filter.atTop,
      ContinuousOn
        (fun θ => (γn n θ).re * (deriv (γn n) θ).im)
        (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    apply Filter.Eventually.of_forall
    intro n
    exact ((Complex.continuous_re.comp (hsmooth n).continuous).mul
      (Complex.continuous_im.comp (hdercont n))).continuousOn
  have hint := hprod.tendsto_intervalIntegral_of_continuousOn
    (μ := (volume : MeasureTheory.Measure ℝ)) hcont
  convert hint using 1
  ext n
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hd : deriv (fun t => (γn n t).im) θ =
      (deriv (γn n) θ).im := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ
        ((hsmooth n θ).hasDerivAt)).deriv
  simpa only using congrArg (fun x : ℝ => (γn n θ).re * x) hd

/-- On the compact standard angle interval, separate uniform convergence of
the boundary values and angular derivatives suffices for convergence of the
oriented area integral. -/
theorem oriented_boundary_integral_tendsto_of_uniform_value_deriv
    (γn : ℕ → ℝ → ℂ) (γ : ℝ → ℂ)
    (hval : TendstoUniformlyOn γn γ Filter.atTop
      (Set.uIcc (0 : ℝ) (2 * Real.pi)))
    (hder : TendstoUniformlyOn
      (fun n θ => deriv (γn n) θ) (deriv γ) Filter.atTop
      (Set.uIcc (0 : ℝ) (2 * Real.pi)))
    (hγcont : ContinuousOn γ (Set.uIcc (0 : ℝ) (2 * Real.pi)))
    (hγdercont : ContinuousOn (deriv γ)
      (Set.uIcc (0 : ℝ) (2 * Real.pi)))
    (hsmooth : ∀ n, Differentiable ℝ (γn n))
    (hdercont : ∀ n, Continuous (deriv (γn n))) :
    Filter.Tendsto
      (fun n => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γn n θ).re * deriv (fun t => (γn n t).im) θ)
      Filter.atTop
      (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γ θ).re * (deriv γ θ).im)) := by
  let I : Set ℝ := Set.uIcc 0 (2 * Real.pi)
  have hcompact : IsCompact I := isCompact_uIcc
  obtain ⟨C, hC⟩ :=
    (hcompact.image_of_continuousOn hγcont).isBounded.exists_norm_le
  obtain ⟨D, hD⟩ :=
    (hcompact.image_of_continuousOn hγdercont).isBounded.exists_norm_le
  have hC' : ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ θ ∈ I, |(γ θ).re| ≤ C' := by
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro θ hθ
    exact (Complex.abs_re_le_norm _).trans
      ((hC _ (Set.mem_image_of_mem _ hθ)).trans (le_max_left _ _))
  have hD' : ∃ D' : ℝ, 0 ≤ D' ∧
      ∀ θ ∈ I, |(deriv γ θ).im| ≤ D' := by
    refine ⟨max D 0, le_max_right _ _, ?_⟩
    intro θ hθ
    exact (Complex.abs_im_le_norm _).trans
      ((hD _ (Set.mem_image_of_mem _ hθ)).trans (le_max_left _ _))
  exact oriented_boundary_integral_tendsto_of_uniform γn γ
    (uniform_re_mul_im_of_uniform hval hder hC' hD') hsmooth hdercont

/-- The angular derivative of the genuine boundary curve of the regularized
exterior map. The positive mode has coefficient `+i` and the correction
has coefficient `-i`, matching the signed Fourier area calculation. -/
theorem rescaleExterior_boundary_full_angular_deriv
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (θ : ℝ) :
    deriv (fun t : ℝ => rescaleExterior s F
      (fourier 1 (t : AddCircle (2 * Real.pi)))) θ =
      Complex.I * fourier 1 (θ : AddCircle (2 * Real.pi)) -
        (s : ℂ) ^ 2 * Complex.I * fourier (-1)
          (θ : AddCircle (2 * Real.pi)) *
          deriv (exteriorForwardGerm F)
            ((s : ℂ) * fourier (-1)
              (θ : AddCircle (2 * Real.pi))) := by
  let c : ℝ → ℂ := fun t =>
    (s : ℂ) * exteriorForwardGerm F
      ((s : ℂ) * fourier (-1) (t : AddCircle (2 * Real.pi)))
  have hcurve :
      (fun t : ℝ => rescaleExterior s F
        (fourier 1 (t : AddCircle (2 * Real.pi)))) =
      (fun t : ℝ => fourier 1 (t : AddCircle (2 * Real.pi)) + c t) := by
    funext t
    exact rescaleExterior_boundary_value_fourier F hs0 _
  have hpos : HasDerivAt
      (fun t : ℝ => fourier 1 (t : AddCircle (2 * Real.pi)))
      (Complex.I * fourier 1 (θ : AddCircle (2 * Real.pi))) θ := by
    convert hasDerivAt_fourier (2 * Real.pi) 1 θ using 1
    push_cast
    have hpi : (2 * (Real.pi : ℝ)) ≠ 0 := by positivity
    field_simp [hpi]
  have hneg : HasDerivAt
      (fun t : ℝ => fourier (-1) (t : AddCircle (2 * Real.pi)))
      (-Complex.I * fourier (-1) (θ : AddCircle (2 * Real.pi))) θ := by
    convert hasDerivAt_fourier (2 * Real.pi) (-1) θ using 1
    push_cast
    have hpi : (2 * (Real.pi : ℝ)) ≠ 0 := by positivity
    field_simp [hpi]
  have hinner := hneg.const_mul (s : ℂ)
  have hnorm :
      ‖(s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi))‖ = s := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
      fourier_apply, Circle.norm_coe, mul_one]
  have hu : (s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi)) ∈
      Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact hs1
  have hg : DifferentiableAt ℂ (exteriorForwardGerm F)
      ((s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi))) :=
    ((exteriorForwardGerm_analyticOnNhd_unitBall F hc) _ hu).differentiableAt
  have hcorr : HasDerivAt c
      ((s : ℂ) *
        (deriv (exteriorForwardGerm F)
          ((s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi))) *
        ((s : ℂ) * (-Complex.I * fourier (-1)
          (θ : AddCircle (2 * Real.pi)))))) θ := by
    simpa only [c, Function.comp_def] using
      (hg.hasDerivAt.comp θ hinner).const_mul (s : ℂ)
  have htotal := (hpos.add hcorr).deriv
  have hfun :
      (fun t : ℝ => fourier 1 (t : AddCircle (2 * Real.pi)) + c t) =
      ((fun t : ℝ => fourier 1 (t : AddCircle (2 * Real.pi))) + c) := by
    funext t
    rfl
  rw [hcurve, hfun, htotal]
  ring

/-- The actual boundary curve is differentiable at every real angle after
regularization; no boundary regularity of the original exterior map is
assumed. -/
theorem rescaleExterior_boundary_differentiable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Differentiable ℝ (fun t : ℝ => rescaleExterior s F
      (fourier 1 (t : AddCircle (2 * Real.pi)))) := by
  intro θ
  have hpos : DifferentiableAt ℝ
      (fun t : ℝ => fourier 1 (t : AddCircle (2 * Real.pi))) θ :=
    (hasDerivAt_fourier (2 * Real.pi) 1 θ).differentiableAt
  have hnorm :
      ‖(s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi))‖ = s := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
      fourier_apply, Circle.norm_coe, mul_one]
  have hu : (s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi)) ∈
      Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact hs1
  have hg : DifferentiableAt ℂ (exteriorForwardGerm F)
      ((s : ℂ) * fourier (-1) (θ : AddCircle (2 * Real.pi))) :=
    ((exteriorForwardGerm_analyticOnNhd_unitBall F hc) _ hu).differentiableAt
  have hcorr : DifferentiableAt ℝ
      (fun t : ℝ => (s : ℂ) * exteriorForwardGerm F
        ((s : ℂ) * fourier (-1) (t : AddCircle (2 * Real.pi)))) θ := by
    exact ((hg.hasDerivAt.comp θ
      ((hasDerivAt_fourier (2 * Real.pi) (-1) θ).const_mul (s : ℂ))).const_mul
        (s : ℂ)).differentiableAt
  have hcurve :
      (fun t : ℝ => rescaleExterior s F
        (fourier 1 (t : AddCircle (2 * Real.pi)))) =
      (fun t : ℝ => fourier 1 (t : AddCircle (2 * Real.pi)) +
        (s : ℂ) * exteriorForwardGerm F
          ((s : ℂ) * fourier (-1) (t : AddCircle (2 * Real.pi)))) := by
    funext t
    exact rescaleExterior_boundary_value_fourier F hs0 _
  rw [hcurve]
  exact hpos.add hcorr

/-- The genuine regularized boundary curve is uniformly approximated on all
real angles by its finite Laurent Fourier curves. The positive frequency
is exact; only the negative modes require an analytic limit. -/
theorem rescaleExterior_boundary_partial_value_uniform
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : ℝ =>
        fourier 1 (θ : AddCircle (2 * Real.pi)) +
          (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
            exteriorForwardCoeff F j *
              ((s : ℂ) * fourier (-1)
                (θ : AddCircle (2 * Real.pi))) ^ j)
      (fun θ : ℝ => rescaleExterior s F
        (fourier 1 (θ : AddCircle (2 * Real.pi))))
      Filter.atTop Set.univ := by
  have hbase := rescaleExterior_boundary_actual_laurent_uniform
    F hc hs0 hs1
  have hshift : TendstoUniformlyOn
      (fun M : ℕ => fun θ : AddCircle (2 * Real.pi) =>
        (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
          exteriorForwardCoeff F j *
            ((s : ℂ) * fourier (-1) θ) ^ j)
      (fun θ : AddCircle (2 * Real.pi) =>
        rescaleExterior s F (fourier 1 θ) - fourier 1 θ)
      Filter.atTop Set.univ := by
    intro u hu
    exact (Filter.tendsto_add_atTop_nat 1).eventually (hbase u hu)
  have hreal := hshift.comp
    (fun θ : ℝ => (θ : AddCircle (2 * Real.pi)))
  have hreal' : TendstoUniformlyOn
      (fun M : ℕ => fun θ : ℝ =>
        (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
          exteriorForwardCoeff F j *
            ((s : ℂ) * fourier (-1)
              (θ : AddCircle (2 * Real.pi))) ^ j)
      (fun θ : ℝ => rescaleExterior s F
        (fourier 1 (θ : AddCircle (2 * Real.pi))) -
          fourier 1 (θ : AddCircle (2 * Real.pi)))
      Filter.atTop Set.univ := by
    simpa only [Function.comp_def, Set.preimage_univ] using hreal
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hreal') ε hε]
    with M hM θ hθ
  have ht := hM θ (Set.mem_univ θ)
  change dist (rescaleExterior s F
      (fourier 1 (θ : AddCircle (2 * Real.pi))))
    (fourier 1 (θ : AddCircle (2 * Real.pi)) +
      (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
        exteriorForwardCoeff F j *
          ((s : ℂ) * fourier (-1)
            (θ : AddCircle (2 * Real.pi))) ^ j) < ε
  convert ht using 1 <;> simp only [dist_eq_norm]
  congr 1
  ring

/-- The finite Laurent boundary curve has the expected derivative: one
positive Fourier mode plus the derivative of the finite correction. -/
theorem rescaleExterior_boundary_partial_angular_deriv
    (F : ℂ → ℂ) (s : ℝ) (M : ℕ) (θ : ℝ) :
    deriv (fun t : ℝ =>
      fourier 1 (t : AddCircle (2 * Real.pi)) +
        (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
          exteriorForwardCoeff F j *
            ((s : ℂ) * fourier (-1)
              (t : AddCircle (2 * Real.pi))) ^ j) θ =
    Complex.I * fourier 1 (θ : AddCircle (2 * Real.pi)) -
      (s : ℂ) ^ 2 * Complex.I * fourier (-1)
        (θ : AddCircle (2 * Real.pi)) *
        (∑ k ∈ Finset.range M,
          (k + 1 : ℂ) * exteriorForwardCoeff F (k + 1) *
            ((s : ℂ) * fourier (-1)
              (θ : AddCircle (2 * Real.pi))) ^ k) := by
  have hpos : HasDerivAt
      (fun t : ℝ => fourier 1 (t : AddCircle (2 * Real.pi)))
      (Complex.I * fourier 1 (θ : AddCircle (2 * Real.pi))) θ := by
    convert hasDerivAt_fourier (2 * Real.pi) 1 θ using 1
    push_cast
    have hpi : (2 * (Real.pi : ℝ)) ≠ 0 := by positivity
    field_simp [hpi]
  have hneg : HasDerivAt
      (fun t : ℝ => fourier (-1) (t : AddCircle (2 * Real.pi)))
      (-Complex.I * fourier (-1) (θ : AddCircle (2 * Real.pi))) θ := by
    convert hasDerivAt_fourier (2 * Real.pi) (-1) θ using 1
    push_cast
    have hpi : (2 * (Real.pi : ℝ)) ≠ 0 := by positivity
    field_simp [hpi]
  have hinner : DifferentiableAt ℝ
      (fun t : ℝ => (s : ℂ) * fourier (-1)
        (t : AddCircle (2 * Real.pi))) θ :=
    (hneg.const_mul (s : ℂ)).differentiableAt
  have hcorr : DifferentiableAt ℝ
      (fun t : ℝ => (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
        exteriorForwardCoeff F j *
          ((s : ℂ) * fourier (-1)
            (t : AddCircle (2 * Real.pi))) ^ j) θ := by
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.fun_sum
    intro j hj
    exact (hinner.pow j).const_mul _
  have hsum := deriv_add hpos.differentiableAt hcorr
  have hfun :
      (fun t : ℝ =>
        fourier 1 (t : AddCircle (2 * Real.pi)) +
          (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
            exteriorForwardCoeff F j *
              ((s : ℂ) * fourier (-1)
                (t : AddCircle (2 * Real.pi))) ^ j) =
      ((fun t : ℝ => fourier 1 (t : AddCircle (2 * Real.pi))) +
        (fun t : ℝ => (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
          exteriorForwardCoeff F j *
            ((s : ℂ) * fourier (-1)
              (t : AddCircle (2 * Real.pi))) ^ j)) := by
    funext t
    rfl
  rw [hfun, hsum, hpos.deriv,
    regularizedLaurentPartial_angular_deriv
      (exteriorForwardCoeff F) s M θ]
  ring

/-- Every finite Laurent boundary curve is differentiable as a real-angle
curve. -/
theorem rescaleExterior_boundary_partial_differentiable
    (F : ℂ → ℂ) (s : ℝ) (M : ℕ) :
    Differentiable ℝ (fun t : ℝ =>
      fourier 1 (t : AddCircle (2 * Real.pi)) +
        (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
          exteriorForwardCoeff F j *
            ((s : ℂ) * fourier (-1)
              (t : AddCircle (2 * Real.pi))) ^ j) := by
  intro θ
  have hpos : DifferentiableAt ℝ
      (fun t : ℝ => fourier 1 (t : AddCircle (2 * Real.pi))) θ :=
    (hasDerivAt_fourier (2 * Real.pi) 1 θ).differentiableAt
  have hneg : DifferentiableAt ℝ
      (fun t : ℝ => fourier (-1) (t : AddCircle (2 * Real.pi))) θ :=
    (hasDerivAt_fourier (2 * Real.pi) (-1) θ).differentiableAt
  have hinner : DifferentiableAt ℝ
      (fun t : ℝ => (s : ℂ) * fourier (-1)
        (t : AddCircle (2 * Real.pi))) θ := hneg.const_mul _
  have hsum : DifferentiableAt ℝ
      (fun t : ℝ => ∑ j ∈ Finset.range (M + 1),
        exteriorForwardCoeff F j *
          ((s : ℂ) * fourier (-1)
            (t : AddCircle (2 * Real.pi))) ^ j) θ := by
    apply DifferentiableAt.fun_sum
    intro j hj
    exact (hinner.pow j).const_mul _
  have h := hpos.add (hsum.const_mul (s : ℂ))
  convert h using 1

/-- The derivative of a finite regularized Laurent boundary curve is a
continuous complex-valued function of the real angle. -/
theorem rescaleExterior_boundary_partial_deriv_continuous
    (F : ℂ → ℂ) (s : ℝ) (M : ℕ) :
    Continuous (deriv (fun t : ℝ =>
      fourier 1 (t : AddCircle (2 * Real.pi)) +
        (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
          exteriorForwardCoeff F j *
            ((s : ℂ) * fourier (-1)
              (t : AddCircle (2 * Real.pi))) ^ j)) := by
  have hpos : Continuous
      (fun θ : ℝ => fourier 1 (θ : AddCircle (2 * Real.pi))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hasDerivAt_fourier (2 * Real.pi) 1 θ).continuousAt
  have hneg : Continuous
      (fun θ : ℝ => fourier (-1) (θ : AddCircle (2 * Real.pi))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hasDerivAt_fourier (2 * Real.pi) (-1) θ).continuousAt
  have hsum : Continuous (fun θ : ℝ =>
      ∑ k ∈ Finset.range M,
        (k + 1 : ℂ) * exteriorForwardCoeff F (k + 1) *
          ((s : ℂ) * fourier (-1)
            (θ : AddCircle (2 * Real.pi))) ^ k) := by
    apply continuous_finsetSum
    intro k hk
    exact (continuous_const.mul continuous_const).mul
      ((continuous_const.mul hneg).pow k)
  have hformula :
      (deriv (fun t : ℝ =>
        fourier 1 (t : AddCircle (2 * Real.pi)) +
          (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
            exteriorForwardCoeff F j *
              ((s : ℂ) * fourier (-1)
                (t : AddCircle (2 * Real.pi))) ^ j)) =
      (fun θ : ℝ =>
        Complex.I * fourier 1 (θ : AddCircle (2 * Real.pi)) -
          (s : ℂ) ^ 2 * Complex.I * fourier (-1)
            (θ : AddCircle (2 * Real.pi)) *
            (∑ k ∈ Finset.range M,
              (k + 1 : ℂ) * exteriorForwardCoeff F (k + 1) *
                ((s : ℂ) * fourier (-1)
                  (θ : AddCircle (2 * Real.pi))) ^ k)) := by
    funext θ
    exact rescaleExterior_boundary_partial_angular_deriv F s M θ
  rw [hformula]
  exact (continuous_const.mul hpos).sub
    (((continuous_const.mul continuous_const).mul hneg).mul hsum)

/-- The angular derivatives of the finite Laurent boundary curves converge
uniformly to the angular derivative of the genuine regularized exterior
boundary curve. This includes the exact positive Fourier mode. -/
theorem rescaleExterior_boundary_partial_angular_deriv_uniform
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : ℝ =>
        deriv (fun t : ℝ =>
          fourier 1 (t : AddCircle (2 * Real.pi)) +
            (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
              exteriorForwardCoeff F j *
                ((s : ℂ) * fourier (-1)
                  (t : AddCircle (2 * Real.pi))) ^ j) θ)
      (fun θ : ℝ => deriv (fun t : ℝ => rescaleExterior s F
        (fourier 1 (t : AddCircle (2 * Real.pi)))) θ)
      Filter.atTop Set.univ := by
  have hbase := rescaleExterior_boundary_correction_angular_deriv_uniform
    F hc hs0 hs1
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hbase) ε hε]
    with M hM θ hθ
  have ht := hM θ (Set.mem_univ θ)
  rw [rescaleExterior_boundary_full_angular_deriv F hc hs0 hs1 θ,
    rescaleExterior_boundary_partial_angular_deriv F s M θ]
  rw [rescaleExterior_boundary_correction_angular_deriv F hc hs0 hs1 θ,
    regularizedLaurentPartial_angular_deriv
      (exteriorForwardCoeff F) s M θ] at ht
  convert ht using 1 <;> simp only [dist_eq_norm]
  congr 1
  ring

/-- The signed boundary area integrals of the actual regularized map are
limits of the finite Laurent Fourier area integrals. This connects the
finite signed orthogonality theorem to the genuine exterior boundary curve,
without imposing a boundary analyticity hypothesis on the original map. -/
theorem rescaleExterior_boundary_oriented_integral_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Filter.Tendsto
      (fun M : ℕ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (fourier 1 (θ : AddCircle (2 * Real.pi)) +
          (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
            exteriorForwardCoeff F j *
              ((s : ℂ) * fourier (-1)
                (θ : AddCircle (2 * Real.pi))) ^ j).re *
          deriv (fun t : ℝ =>
            (fourier 1 (t : AddCircle (2 * Real.pi)) +
              (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
                exteriorForwardCoeff F j *
                  ((s : ℂ) * fourier (-1)
                    (t : AddCircle (2 * Real.pi))) ^ j).im) θ)
      Filter.atTop
      (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (rescaleExterior s F
          (fourier 1 (θ : AddCircle (2 * Real.pi)))).re *
          deriv (fun t : ℝ =>
            (rescaleExterior s F
              (fourier 1 (t : AddCircle (2 * Real.pi)))).im) θ)) := by
  let γn : ℕ → ℝ → ℂ := fun M θ =>
    fourier 1 (θ : AddCircle (2 * Real.pi)) +
      (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
        exteriorForwardCoeff F j *
          ((s : ℂ) * fourier (-1)
            (θ : AddCircle (2 * Real.pi))) ^ j
  let γ : ℝ → ℂ := fun θ =>
    rescaleExterior s F (fourier 1 (θ : AddCircle (2 * Real.pi)))
  have hval : TendstoUniformlyOn γn γ Filter.atTop Set.univ :=
    rescaleExterior_boundary_partial_value_uniform F hc hs0 hs1
  have hder : TendstoUniformlyOn
      (fun M θ => deriv (γn M) θ) (deriv γ) Filter.atTop Set.univ :=
    rescaleExterior_boundary_partial_angular_deriv_uniform F hc hs0 hs1
  have hsmooth : ∀ M, Differentiable ℝ (γn M) :=
    fun M => rescaleExterior_boundary_partial_differentiable F s M
  have hdercont : ∀ M, Continuous (deriv (γn M)) :=
    fun M => rescaleExterior_boundary_partial_deriv_continuous F s M
  let I : Set ℝ := Set.uIcc 0 (2 * Real.pi)
  have hγcont : ContinuousOn γ I := by
    have hevent : ∀ᶠ M : ℕ in Filter.atTop, ContinuousOn (γn M) I :=
      Filter.Eventually.of_forall (fun M => (hsmooth M).continuous.continuousOn)
    exact (hval.mono (Set.subset_univ _)).continuousOn hevent.frequently
  have hγdercont : ContinuousOn (deriv γ) I := by
    have hevent : ∀ᶠ M : ℕ in Filter.atTop,
        ContinuousOn (deriv (γn M)) I :=
      Filter.Eventually.of_forall (fun M => (hdercont M).continuousOn)
    exact (hder.mono (Set.subset_univ _)).continuousOn hevent.frequently
  have hlim := oriented_boundary_integral_tendsto_of_uniform_value_deriv
    γn γ (hval.mono (Set.subset_univ _))
    (hder.mono (Set.subset_univ _)) hγcont hγdercont hsmooth hdercont
  have hγdiff : Differentiable ℝ γ :=
    rescaleExterior_boundary_differentiable F hc hs0 hs1
  have hIm (θ : ℝ) : deriv (fun t => (γ t).im) θ =
      (deriv γ θ).im := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ
        (hγdiff θ).hasDerivAt).deriv
  have hIntegral :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γ θ).re * deriv (fun t => (γ t).im) θ) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γ θ).re * (deriv γ θ).im) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    simpa only using congrArg (fun x : ℝ => (γ θ).re * x) (hIm θ)
  change Filter.Tendsto
    (fun M => ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (γn M θ).re * deriv (fun t => (γn M t).im) θ)
    Filter.atTop
    (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (γ θ).re * deriv (fun t => (γ t).im) θ))
  rw [hIntegral]
  exact hlim

end SpringerLean
