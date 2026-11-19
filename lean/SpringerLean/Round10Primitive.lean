import SpringerLean.Round09Reduction
import Mathlib.Analysis.Calculus.FDeriv.Partial

open MeasureTheory Filter
open scoped Topology

namespace SpringerLean

/-- The real primitive of a plane weight in the first coordinate. It is the
coefficient of `dy` in the one-form used for the parameter Green formula. -/
noncomputable def greenPrimitive (φ : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..p.1, φ ((t : ℂ) + Complex.I * (p.2 : ℂ)) ∂volume

theorem greenPrimitive_zero_first (φ : ℂ → ℝ) (y : ℝ) :
    greenPrimitive φ (0, y) = 0 := by
  simp [greenPrimitive]

/-- The only derivative of the primitive that survives the pullback
calculation. -/
theorem greenPrimitive_deriv_first
    (φ : ℂ → ℝ) (hφ : Continuous φ) (x y : ℝ) :
    deriv (fun u : ℝ => greenPrimitive φ (u, y)) x =
      φ ((x : ℂ) + Complex.I * (y : ℂ)) := by
  have hcont : Continuous (fun t : ℝ =>
      φ ((t : ℂ) + Complex.I * (y : ℂ))) := by
    fun_prop
  simpa only [greenPrimitive] using hcont.deriv_integral
    (fun t : ℝ => φ ((t : ℂ) + Complex.I * (y : ℂ))) 0 x

theorem greenPrimitive_hasDerivAt_first
    (φ : ℂ → ℝ) (hφ : Continuous φ) (x y : ℝ) :
    HasDerivAt (fun u : ℝ => greenPrimitive φ (u, y))
      (φ ((x : ℂ) + Complex.I * (y : ℂ))) x := by
  have hcont : Continuous (fun t : ℝ =>
      φ ((t : ℂ) + Complex.I * (y : ℂ))) := by
    fun_prop
  simpa only [greenPrimitive] using
    (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem greenPrimitive_continuous_first
    (φ : ℂ → ℝ) (hφ : Continuous φ) (y : ℝ) :
    Continuous (fun x : ℝ => greenPrimitive φ (x, y)) := by
  have hcont : Continuous (fun t : ℝ =>
      φ ((t : ℂ) + Complex.I * (y : ℂ))) := by
    fun_prop
  simpa only [greenPrimitive] using
    (intervalIntegral.differentiable_integral_of_continuous
      (a := (0 : ℝ)) hcont).continuous

/-- A fixed-interval representation of the Green primitive. -/
theorem greenPrimitive_fixed_interval (φ : ℂ → ℝ) (x y : ℝ) :
    greenPrimitive φ (x, y) =
      x * ∫ t in (0 : ℝ)..1,
        φ (((t * x : ℝ) : ℂ) + Complex.I * (y : ℂ)) ∂volume := by
  have h := intervalIntegral.smul_integral_comp_mul_right
    (f := fun u : ℝ => φ ((u : ℂ) + Complex.I * (y : ℂ)))
    (a := (0 : ℝ)) (b := (1 : ℝ)) (c := x)
  simpa [greenPrimitive, smul_eq_mul, mul_comm] using h.symm

/-- Joint continuity of the actual Green primitive follows from its
fixed-interval representation and continuity of a compact parameter
integral. -/
theorem greenPrimitive_continuous
    (φ : ℂ → ℝ) (hφ : Continuous φ) :
    Continuous (greenPrimitive φ) := by
  let f : (ℝ × ℝ) → ℝ → ℝ := fun p t =>
    φ (((t * p.1 : ℝ) : ℂ) + Complex.I * (p.2 : ℂ))
  have hf : Continuous f.uncurry := by
    dsimp [f, Function.uncurry]
    fun_prop
  have hi : Continuous (fun p : ℝ × ℝ =>
      ∫ t in Set.Icc (0 : ℝ) 1, f p t ∂volume) :=
    continuous_parametric_integral_of_continuous hf isCompact_Icc
  have heq : greenPrimitive φ = fun p : ℝ × ℝ =>
      p.1 * ∫ t in Set.Icc (0 : ℝ) 1, f p t ∂volume := by
    funext p
    rw [greenPrimitive_fixed_interval, intervalIntegral.integral_of_le (by norm_num)]
    simp only [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  rw [heq]
  exact continuous_fst.mul hi

/-- Transverse derivative of a compactly supported C1 Green weight.
The global derivative bound supplied by compact support justifies
differentiation under the interval integral. -/
theorem greenPrimitive_hasDerivAt_second
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) (x y : ℝ) :
    HasDerivAt (fun v : ℝ => greenPrimitive φ (x, v))
      (∫ t in (0 : ℝ)..x,
        fderiv ℝ φ ((t : ℂ) + Complex.I * (y : ℂ)) Complex.I ∂volume) y := by
  let F : ℝ → ℝ → ℝ := fun v t =>
    φ ((t : ℂ) + Complex.I * (v : ℂ))
  let F' : ℝ → ℝ → ℝ := fun v t =>
    fderiv ℝ φ ((t : ℂ) + Complex.I * (v : ℂ)) Complex.I
  have hφcont : Continuous φ := hφ.continuous
  have hfdcont : Continuous (fderiv ℝ φ) :=
    hφ.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ :=
    hfdcont.bounded_above_of_compact_support (hcompact.fderiv ℝ)
  have hmeas : ∀ᶠ (v : ℝ) in 𝓝 y,
      AEStronglyMeasurable (F v) (volume.restrict (Set.uIoc 0 x)) := by
    filter_upwards with v
    have hc : Continuous (F v) := by dsimp [F]; fun_prop
    exact hc.aestronglyMeasurable
  have hFint : IntervalIntegrable (F y) volume 0 x := by
    have hc : Continuous (F y) := by dsimp [F]; fun_prop
    exact hc.intervalIntegrable _ _
  have hF'meas : AEStronglyMeasurable (F' y)
      (volume.restrict (Set.uIoc 0 x)) := by
    have hc : Continuous (F' y) := by
      dsimp [F']
      exact hfdcont.clm_apply continuous_const |>.comp (by fun_prop)
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ (t : ℝ) ∂volume,
      t ∈ Set.uIoc 0 x → ∀ v ∈ (Set.univ : Set ℝ), ‖F' v t‖ ≤ C := by
    filter_upwards with t ht v hv
    dsimp [F']
    have h := (fderiv ℝ φ ((t : ℂ) + Complex.I * (v : ℂ))).unit_le_opNorm
      Complex.I (by simp)
    exact h.trans (hC _)
  have hbint : IntervalIntegrable (fun _ : ℝ => C) volume 0 x :=
    continuous_const.intervalIntegrable _ _
  have hdiff : ∀ᵐ (t : ℝ) ∂volume,
      t ∈ Set.uIoc 0 x → ∀ v ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun q => F q t) (F' v t) v := by
    filter_upwards with t ht v hv
    have harg : HasDerivAt
        (fun q : ℝ => (t : ℂ) + Complex.I * (q : ℂ)) Complex.I v := by
      simpa [Complex.real_smul, mul_comm] using
        ((hasDerivAt_id v).smul_const Complex.I).const_add (t : ℂ)
    have hφ' : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    simpa [F, F', Function.comp_def] using
      (hφ' _).hasFDerivAt.comp_hasDerivAt v harg
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (a := (0 : ℝ)) (b := x) (bound := fun _ => C)
    univ_mem hmeas hFint hF'meas hbound hbint hdiff
  simpa only [greenPrimitive, F, F'] using h.2

theorem greenPrimitive_deriv_second
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) (x y : ℝ) :
    deriv (fun v : ℝ => greenPrimitive φ (x, v)) y =
      ∫ t in (0 : ℝ)..x,
        fderiv ℝ φ ((t : ℂ) + Complex.I * (y : ℂ)) Complex.I ∂volume :=
  (greenPrimitive_hasDerivAt_second φ hφ hcompact x y).deriv

/-- The transverse partial derivative varies continuously in both
coordinates. This is the remaining analytic input for the C1 primitive. -/
theorem greenPrimitive_deriv_second_continuous
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) :
    Continuous (fun p : ℝ × ℝ =>
      deriv (fun v : ℝ => greenPrimitive φ (p.1, v)) p.2) := by
  let ψ : ℂ → ℝ := fun w => fderiv ℝ φ w Complex.I
  have hψ : Continuous ψ := by
    exact (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have heq : (fun p : ℝ × ℝ =>
      deriv (fun v : ℝ => greenPrimitive φ (p.1, v)) p.2) =
      greenPrimitive ψ := by
    funext p
    exact greenPrimitive_deriv_second φ hφ hcompact p.1 p.2
  rw [heq]
  exact greenPrimitive_continuous ψ hψ

/-- The compactly supported C1 weight has a genuine jointly C1 Green
primitive. Both partial derivatives are proved from the integral definition;
mathlib's continuous-partials theorem supplies the joint derivative. -/
theorem greenPrimitive_contDiff
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) :
    ContDiff ℝ 1 (greenPrimitive φ) := by
  let ψ : ℂ → ℝ := fun w => fderiv ℝ φ w Complex.I
  have hψ : Continuous ψ :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  let f₁ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ
      (φ ((x : ℂ) + Complex.I * (y : ℂ)))
  let f₂ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (greenPrimitive ψ (x, y))
  have hc₁ : Continuous (Function.uncurry f₁) := by
    apply Continuous.comp ContinuousLinearMap.toSpanSingletonCLE.continuous
    exact hφ.continuous.comp (by fun_prop)
  have hc₂ : Continuous (Function.uncurry f₂) := by
    exact ContinuousLinearMap.toSpanSingletonCLE.continuous.comp
      (greenPrimitive_continuous ψ hψ)
  have hd₁ : ∀ p : ℝ × ℝ,
      HasFDerivAt (fun x => greenPrimitive φ (x, p.2))
        (f₁ p.1 p.2) p.1 := by
    intro p
    exact (greenPrimitive_hasDerivAt_first φ hφ.continuous p.1 p.2).hasFDerivAt
  have hd₂ : ∀ p : ℝ × ℝ,
      HasFDerivAt (fun y => greenPrimitive φ (p.1, y))
        (f₂ p.1 p.2) p.2 := by
    intro p
    simpa only [f₂, ψ, greenPrimitive] using
      (greenPrimitive_hasDerivAt_second φ hφ hcompact p.1 p.2).hasFDerivAt
  have hder : ∀ p : ℝ × ℝ,
      HasFDerivAt (greenPrimitive φ)
        ((f₁ p.1 p.2).coprod (f₂ p.1 p.2)) p := by
    intro p
    exact (hasStrictFDerivAt_uncurry_coprod
      (u := p) (f := fun x y => greenPrimitive φ (x, y))
      (f₁ := f₁) (f₂ := f₂)
      (Filter.Eventually.of_forall hd₁)
      (Filter.Eventually.of_forall hd₂)
      (show ContinuousAt (Function.uncurry f₁) p from hc₁.continuousAt)
      (show ContinuousAt (Function.uncurry f₂) p from hc₂.continuousAt)).hasFDerivAt
  have hcontder : Continuous (fun p : ℝ × ℝ =>
      (f₁ p.1 p.2).coprod (f₂ p.1 p.2)) := by
    fun_prop
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨_, hcontder, hder⟩

/-- The horizontal component of the genuine two-dimensional Fréchet
derivative is the original weight. -/
theorem greenPrimitive_fderiv_horizontal
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) (p : ℝ × ℝ) :
    fderiv ℝ (greenPrimitive φ) p (1, 0) =
      φ ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) := by
  have hA : DifferentiableAt ℝ (greenPrimitive φ) p :=
    (greenPrimitive_contDiff φ hφ hcompact).differentiable
      (by norm_num) p
  have hline : HasDerivAt (fun x : ℝ => (x, p.2)) (1, 0) p.1 := by
    simpa using (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hchain := hA.hasFDerivAt.comp_hasDerivAt p.1 hline
  have hfirst := greenPrimitive_hasDerivAt_first φ hφ.continuous p.1 p.2
  have heq := hchain.deriv.symm.trans hfirst.deriv
  simpa [Function.comp_def] using heq

/-- The coordinate calculation behind the parameter Green formula. The two
occurrences of the transverse derivative cancel, leaving the oriented
Jacobian with the outer-minus-inner sign. -/
theorem green_flux_coordinate_identity
    (φ Ay Xr Xθ Yr Yθ A Yrθ Yθr : ℝ) (hmixed : Yrθ = Yθr) :
    ((φ * Xr + Ay * Yr) * Yθ + A * Yrθ) -
      ((φ * Xθ + Ay * Yθ) * Yr + A * Yθr) =
      φ * (Xr * Yθ - Xθ * Yr) := by
  rw [hmixed]
  ring


end SpringerLean
