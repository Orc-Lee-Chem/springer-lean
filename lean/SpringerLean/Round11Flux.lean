import SpringerLean.Round10Boundary
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace SpringerLean

/-- Differentiating a fixed directional derivative is evaluation of the
second Fréchet derivative. -/
theorem fderiv_apply_const_fderiv
    (Y : (ℝ × ℝ) → ℝ) (p u v : ℝ × ℝ)
    (hY : ContDiffAt ℝ 2 Y p) :
    (fderiv ℝ (fun q => (fderiv ℝ Y q) v) p) u =
      ((fderiv ℝ (fderiv ℝ Y) p) u) v := by
  have hfirst : DifferentiableAt ℝ (fderiv ℝ Y) p :=
    (hY.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := fderiv_clm_apply hfirst (differentiableAt_const (x := p) v)
  have hu := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L u) h
  simpa using hu

/-- The two mixed directional derivatives of a C² real coordinate function
agree at the radial and angular unit vectors. -/
theorem fderiv_mixed_polar_eq
    (Y : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ)
    (hY : ContDiffAt ℝ 2 Y p) :
    (fderiv ℝ (fun q => (fderiv ℝ Y q) (0, 1)) p) (1, 0) =
      (fderiv ℝ (fun q => (fderiv ℝ Y q) (1, 0)) p) (0, 1) := by
  rw [fderiv_apply_const_fderiv Y p (1, 0) (0, 1) hY,
    fderiv_apply_const_fderiv Y p (0, 1) (1, 0) hY]
  exact hY.isSymmSndFDerivAt (by norm_num) (1, 0) (0, 1)

/-- A real linear functional on the plane is determined by its two
coordinate values. -/
theorem clm_apply_real_pair
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (a b : ℝ) :
    L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have hv : (a, b) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp [smul_eq_mul]

/-- The chain rule through the actual real and imaginary coordinates of a
complex map, with the same vertical coefficient in both directions. -/
theorem fderiv_comp_complex_coordinates
    (A : (ℝ × ℝ) → ℝ) (P : (ℝ × ℝ) → ℂ)
    (p u : ℝ × ℝ)
    (hA : DifferentiableAt ℝ A ((P p).re, (P p).im))
    (hP : DifferentiableAt ℝ P p) :
    (fderiv ℝ (fun q => A ((P q).re, (P q).im)) p) u =
      (fderiv ℝ A ((P p).re, (P p).im)) (1, 0) *
          (fderiv ℝ (fun q => (P q).re) p) u +
      (fderiv ℝ A ((P p).re, (P p).im)) (0, 1) *
          (fderiv ℝ (fun q => (P q).im) p) u := by
  let X : (ℝ × ℝ) → ℝ := fun q => (P q).re
  let Y : (ℝ × ℝ) → ℝ := fun q => (P q).im
  let Q : (ℝ × ℝ) → (ℝ × ℝ) := fun q => (X q, Y q)
  have hX : DifferentiableAt ℝ X p := by
    change DifferentiableAt ℝ (Complex.reCLM ∘ P) p
    exact Complex.reCLM.differentiableAt.comp p hP
  have hY : DifferentiableAt ℝ Y p := by
    change DifferentiableAt ℝ (Complex.imCLM ∘ P) p
    exact Complex.imCLM.differentiableAt.comp p hP
  have hQ : DifferentiableAt ℝ Q p := hX.prodMk hY
  have hcomp := fderiv_comp p hA hQ
  have hpair := hX.fderiv_prodMk hY
  change (fderiv ℝ (A ∘ Q) p) u = _
  rw [hcomp, ContinuousLinearMap.comp_apply, hpair]
  simpa [Q, X, Y, mul_comm] using
    clm_apply_real_pair (fderiv ℝ A (Q p))
      ((fderiv ℝ X p) u) ((fderiv ℝ Y p) u)

/-- The two directional derivatives of the actual Green primitive pullback
share one and the same vertical coefficient. -/
theorem greenPrimitive_comp_complex_fderiv
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (P : (ℝ × ℝ) → ℂ) (p u : ℝ × ℝ)
    (hP : DifferentiableAt ℝ P p) :
    (fderiv ℝ (fun q => greenPrimitive φ ((P q).re, (P q).im)) p) u =
      φ (P p) * (fderiv ℝ (fun q => (P q).re) p) u +
      (fderiv ℝ (greenPrimitive φ) ((P p).re, (P p).im)) (0, 1) *
        (fderiv ℝ (fun q => (P q).im) p) u := by
  have hA : DifferentiableAt ℝ (greenPrimitive φ)
      ((P p).re, (P p).im) :=
    (greenPrimitive_contDiff φ hφ hcompact).differentiable
      (by norm_num) _
  rw [fderiv_comp_complex_coordinates (greenPrimitive φ) P p u hA hP]
  rw [greenPrimitive_fderiv_horizontal φ hφ hcompact]
  have hreim : ((P p).re : ℂ) + Complex.I * ((P p).im : ℂ) = P p := by
    rw [mul_comm]
    exact Complex.re_add_im _
  rw [hreim]

theorem complex_im_contDiffAt_of_contDiffAt
    (P : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ)
    (hP : ContDiffAt ℝ 2 P p) :
    ContDiffAt ℝ 2 (fun q => (P q).im) p := by
  have him : ContDiffAt ℝ 2 (fun z : ℂ => z.im) (P p) := by
    change ContDiffAt ℝ 2 (Complex.imCLM : ℂ → ℝ) (P p)
    exact Complex.imCLM.contDiff.contDiffAt
  exact him.comp p hP

private theorem greenPrimitive_comp_complex_differentiableAt
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (P : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ)
    (hP : DifferentiableAt ℝ P p) :
    DifferentiableAt ℝ
      (fun q => greenPrimitive φ ((P q).re, (P q).im)) p := by
  have hX : DifferentiableAt ℝ (fun q => (P q).re) p := by
    change DifferentiableAt ℝ (Complex.reCLM ∘ P) p
    exact Complex.reCLM.differentiableAt.comp p hP
  have hY : DifferentiableAt ℝ (fun q => (P q).im) p := by
    change DifferentiableAt ℝ (Complex.imCLM ∘ P) p
    exact Complex.imCLM.differentiableAt.comp p hP
  exact ((greenPrimitive_contDiff φ hφ hcompact).differentiable
    (by norm_num) _).comp p (hX.prodMk hY)

/-- The actual radial flux associated with the pullback of `A dY`. -/
noncomputable def greenFluxRadial
    (φ : ℂ → ℝ) (P : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) : ℝ :=
  greenPrimitive φ ((P p).re, (P p).im) *
    (fderiv ℝ (fun q => (P q).im) p) (0, 1)

/-- The negative angular flux, so that the rectangular divergence has
outer-minus-inner boundary orientation. -/
noncomputable def greenFluxAngular
    (φ : ℂ → ℝ) (P : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) : ℝ :=
  -(greenPrimitive φ ((P p).re, (P p).im) *
    (fderiv ℝ (fun q => (P q).im) p) (1, 0))

private theorem greenFluxRadial_fderiv
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (P : (ℝ × ℝ) → ℂ) (p u : ℝ × ℝ)
    (hP : ContDiffAt ℝ 2 P p) :
    (fderiv ℝ (greenFluxRadial φ P) p) u =
      (fderiv ℝ (fun q => greenPrimitive φ ((P q).re, (P q).im)) p) u *
        (fderiv ℝ (fun q => (P q).im) p) (0, 1) +
      greenPrimitive φ ((P p).re, (P p).im) *
        (fderiv ℝ (fun q =>
          (fderiv ℝ (fun v => (P v).im) q) (0, 1)) p) u := by
  let Y : (ℝ × ℝ) → ℝ := fun q => (P q).im
  let A : (ℝ × ℝ) → ℝ :=
    fun q => greenPrimitive φ ((P q).re, (P q).im)
  let Yθ : (ℝ × ℝ) → ℝ :=
    fun q => (fderiv ℝ Y q) (0, 1)
  have hPdiff : DifferentiableAt ℝ P p := hP.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ A p :=
    greenPrimitive_comp_complex_differentiableAt φ hφ hcompact P p hPdiff
  have hY : ContDiffAt ℝ 2 Y p := complex_im_contDiffAt_of_contDiffAt P p hP
  have hYder : DifferentiableAt ℝ (fderiv ℝ Y) p :=
    (hY.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hYθ : DifferentiableAt ℝ Yθ p :=
    hYder.clm_apply (differentiableAt_const (0, 1))
  have hprod := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L u)
    (fderiv_fun_mul hA hYθ)
  change (fderiv ℝ (fun q =>
      greenPrimitive φ ((P q).re, (P q).im) *
        (fderiv ℝ (fun v => (P v).im) q) (0, 1)) p) u = _
  simpa [greenFluxRadial, A, Y, Yθ, add_comm, mul_comm, mul_left_comm,
    mul_assoc] using hprod

private theorem greenFluxAngular_fderiv
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (P : (ℝ × ℝ) → ℂ) (p u : ℝ × ℝ)
    (hP : ContDiffAt ℝ 2 P p) :
    (fderiv ℝ (greenFluxAngular φ P) p) u =
      -((fderiv ℝ (fun q => greenPrimitive φ ((P q).re, (P q).im)) p) u *
          (fderiv ℝ (fun q => (P q).im) p) (1, 0) +
        greenPrimitive φ ((P p).re, (P p).im) *
          (fderiv ℝ (fun q =>
            (fderiv ℝ (fun v => (P v).im) q) (1, 0)) p) u) := by
  let Y : (ℝ × ℝ) → ℝ := fun q => (P q).im
  let A : (ℝ × ℝ) → ℝ :=
    fun q => greenPrimitive φ ((P q).re, (P q).im)
  let Yr : (ℝ × ℝ) → ℝ :=
    fun q => (fderiv ℝ Y q) (1, 0)
  have hPdiff : DifferentiableAt ℝ P p := hP.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ A p :=
    greenPrimitive_comp_complex_differentiableAt φ hφ hcompact P p hPdiff
  have hY : ContDiffAt ℝ 2 Y p := complex_im_contDiffAt_of_contDiffAt P p hP
  have hYder : DifferentiableAt ℝ (fderiv ℝ Y) p :=
    (hY.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hYr : DifferentiableAt ℝ Yr p :=
    hYder.clm_apply (differentiableAt_const (1, 0))
  have hprod := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L u)
    (fderiv_fun_mul hA hYr)
  change (fderiv ℝ (-(fun q =>
      greenPrimitive φ ((P q).re, (P q).im) *
        (fderiv ℝ (fun v => (P v).im) q) (1, 0))) p) u = _
  rw [fderiv_neg]
  simpa [A, Y, Yr, add_comm, mul_comm, mul_left_comm, mul_assoc] using
    congrArg Neg.neg hprod

/-- The actual pulled-back Green flux has divergence equal to the signed
weighted Jacobian. All derivatives on the left are genuine Fréchet
derivatives of the defined flux functions. -/
theorem greenFlux_pointwise
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (P : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ)
    (hP : ContDiffAt ℝ 2 P p) :
    (fderiv ℝ (greenFluxRadial φ P) p) (1, 0) +
      (fderiv ℝ (greenFluxAngular φ P) p) (0, 1) =
      φ (P p) *
        ((fderiv ℝ (fun q => (P q).re) p) (1, 0) *
            (fderiv ℝ (fun q => (P q).im) p) (0, 1) -
          (fderiv ℝ (fun q => (P q).re) p) (0, 1) *
            (fderiv ℝ (fun q => (P q).im) p) (1, 0)) := by
  have hPdiff : DifferentiableAt ℝ P p := hP.differentiableAt (by norm_num)
  have hY : ContDiffAt ℝ 2 (fun q => (P q).im) p :=
    complex_im_contDiffAt_of_contDiffAt P p hP
  have hmixed := fderiv_mixed_polar_eq (fun q => (P q).im) p hY
  rw [greenFluxRadial_fderiv φ hφ hcompact P p (1, 0) hP,
    greenFluxAngular_fderiv φ hφ hcompact P p (0, 1) hP,
    greenPrimitive_comp_complex_fderiv φ hφ hcompact P p (1, 0) hPdiff,
    greenPrimitive_comp_complex_fderiv φ hφ hcompact P p (0, 1) hPdiff]
  simpa only [sub_eq_add_neg] using
    green_flux_coordinate_identity
      (φ (P p))
      ((fderiv ℝ (greenPrimitive φ) ((P p).re, (P p).im)) (0, 1))
      ((fderiv ℝ (fun q => (P q).re) p) (1, 0))
      ((fderiv ℝ (fun q => (P q).re) p) (0, 1))
      ((fderiv ℝ (fun q => (P q).im) p) (1, 0))
      ((fderiv ℝ (fun q => (P q).im) p) (0, 1))
      (greenPrimitive φ ((P p).re, (P p).im))
      ((fderiv ℝ (fun q =>
        (fderiv ℝ (fun v => (P v).im) q) (0, 1)) p) (1, 0))
      ((fderiv ℝ (fun q =>
        (fderiv ℝ (fun v => (P v).im) q) (1, 0)) p) (0, 1))
      hmixed

end SpringerLean
