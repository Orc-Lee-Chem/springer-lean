import SpringerLean.Round11Outer
import SpringerLean.DiskPolar
import Mathlib.LinearAlgebra.Basis.Fin

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean

/-- The Green rectangles use the same positive polar chart as the
change-of-variables theorem in mathlib. -/
theorem greenPolar_eq_polarCoord_symm (r θ : ℝ) :
    greenPolar r θ = Complex.polarCoord.symm (r, θ) := by
  rw [Complex.polarCoord_symm_apply]
  rw [greenPolar, ← Complex.exp_ofReal_mul_I]

theorem greenPolar_periodic (r θ : ℝ) :
    greenPolar r (θ + 2 * Real.pi) = greenPolar r θ := by
  simp [greenPolar, Complex.ofReal_add, add_mul, Complex.exp_add,
    Complex.ofReal_mul]

theorem greenPolar_contDiff :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => greenPolar p.1 p.2) := by
  have hr : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.1 : ℂ)) := by
    change ContDiff ℝ 2 (Complex.ofRealCLM ∘ Prod.fst)
    exact Complex.ofRealCLM.contDiff.comp contDiff_fst
  have hθ : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.2 : ℂ)) := by
    change ContDiff ℝ 2 (Complex.ofRealCLM ∘ Prod.snd)
    exact Complex.ofRealCLM.contDiff.comp contDiff_snd
  change ContDiff ℝ 2 (fun p : ℝ × ℝ =>
    (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))
  exact hr.mul ((hθ.mul contDiff_const).cexp)

/-- The coordinate functions in the complex chart coincide with the two
coordinates of the real polar chart used to prove its Jacobian formula. -/
theorem greenPolar_re_eq_realPolar (p : ℝ × ℝ) :
    (greenPolar p.1 p.2).re = (polarCoord.symm p).1 := by
  rw [greenPolar_eq_polarCoord_symm, Complex.polarCoord_symm_apply]
  simp [polarCoord, Complex.cos_ofReal_re]

theorem greenPolar_im_eq_realPolar (p : ℝ × ℝ) :
    (greenPolar p.1 p.2).im = (polarCoord.symm p).2 := by
  rw [greenPolar_eq_polarCoord_symm, Complex.polarCoord_symm_apply]
  simp [polarCoord, Complex.sin_ofReal_re]

theorem realPair_clm_det_coordinates
    (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    L.det = (L (1, 0)).1 * (L (0, 1)).2 -
      (L (0, 1)).1 * (L (1, 0)).2 := by
  rw [ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ) (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,
    Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one,
    Module.Basis.coe_finTwoProd_repr]

/-- In the `(radius, angle)` order the coordinate Jacobian is `+radius`.
This checks the sign used in all four Green rectangles. -/
theorem greenPolar_coordinateJacobian (p : ℝ × ℝ) :
    (fderiv ℝ (fun q : ℝ × ℝ => (greenPolar q.1 q.2).re) p) (1, 0) *
        (fderiv ℝ (fun q : ℝ × ℝ => (greenPolar q.1 q.2).im) p) (0, 1) -
      (fderiv ℝ (fun q : ℝ × ℝ => (greenPolar q.1 q.2).re) p) (0, 1) *
        (fderiv ℝ (fun q : ℝ × ℝ => (greenPolar q.1 q.2).im) p) (1, 0) = p.1 := by
  have hdiff : DifferentiableAt ℝ polarCoord.symm p :=
    (hasFDerivAt_polarCoord_symm p).differentiableAt
  have hX := fderiv.fst hdiff
  have hY := fderiv.snd hdiff
  have hD := realPair_clm_det_coordinates (fderiv ℝ polarCoord.symm p)
  rw [(hasFDerivAt_polarCoord_symm p).fderiv,
    det_fderivPolarCoordSymm] at hD
  have hXfun : (fun q : ℝ × ℝ => (greenPolar q.1 q.2).re) =
      fun q => (polarCoord.symm q).1 := by
    funext q
    exact greenPolar_re_eq_realPolar q
  have hYfun : (fun q : ℝ × ℝ => (greenPolar q.1 q.2).im) =
      fun q => (polarCoord.symm q).2 := by
    funext q
    exact greenPolar_im_eq_realPolar q
  rw [hXfun, hYfun]
  simp only [hX, hY, ContinuousLinearMap.comp_apply]
  simpa [(hasFDerivAt_polarCoord_symm p).fderiv] using hD.symm

/-- Green's formula for the positive polar parametrization of any locally
smooth plane map. This still records the signed parameter determinant; the
change to planar area is a separate step. -/
theorem green_parameter_polar
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (W : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hW : ∀ p ∈ Set.Icc (a, 0) (b, 2 * Real.pi),
      ContDiffAt ℝ 2 W (greenPolar p.1 p.2)) :
    (∫ p in Set.Icc (a, 0) (b, 2 * Real.pi),
      φ (W (greenPolar p.1 p.2)) *
        ((fderiv ℝ (fun q : ℝ × ℝ => (W (greenPolar q.1 q.2)).re) p) (1, 0) *
            (fderiv ℝ (fun q : ℝ × ℝ => (W (greenPolar q.1 q.2)).im) p) (0, 1) -
          (fderiv ℝ (fun q : ℝ × ℝ => (W (greenPolar q.1 q.2)).re) p) (0, 1) *
            (fderiv ℝ (fun q : ℝ × ℝ => (W (greenPolar q.1 q.2)).im) p) (1, 0))
        ∂volume) =
      greenBoundary φ (fun θ => W (greenPolar b θ)) -
        greenBoundary φ (fun θ => W (greenPolar a θ)) := by
  let P : ℝ × ℝ → ℂ := fun p => W (greenPolar p.1 p.2)
  have hP : ∀ p ∈ Set.Icc (a, 0) (b, 2 * Real.pi),
      ContDiffAt ℝ 2 P p := by
    intro p hp
    exact (hW p hp).comp p greenPolar_contDiff.contDiffAt
  have hperiod : ∀ r : ℝ, P (r, 2 * Real.pi) = P (r, 0) := by
    intro r
    simp [P]
  exact green_parameter_rectangle φ hφ hcompact P a b hab hP hperiod

/-- The standard positive polar disk is an actual instance of the Green
rectangle, with zero circulation at the center. -/
theorem green_parameter_standard_disk
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) (R : ℝ) (hR : 0 ≤ R) :
    (∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (R, 2 * Real.pi),
      φ (greenPolar p.1 p.2) *
        ((fderiv ℝ (fun q : ℝ × ℝ => (greenPolar q.1 q.2).re) p) (1, 0) *
            (fderiv ℝ (fun q : ℝ × ℝ => (greenPolar q.1 q.2).im) p) (0, 1) -
          (fderiv ℝ (fun q : ℝ × ℝ => (greenPolar q.1 q.2).re) p) (0, 1) *
            (fderiv ℝ (fun q : ℝ × ℝ => (greenPolar q.1 q.2).im) p) (1, 0))
        ∂volume) =
      greenBoundary φ (fun θ => greenPolar R θ) := by
  have h := green_parameter_polar φ hφ hcompact (fun z : ℂ => z) 0 R hR
    (fun p hp => contDiffAt_id)
  simpa [greenBoundary_const, greenPolar] using h

/-- The standard disk Green rectangle has the expected positive `r` factor.
The complex disk area conversion is deliberately a separate theorem. -/
theorem green_parameter_standard_disk_radial
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) (R : ℝ) (hR : 0 ≤ R) :
    (∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (R, 2 * Real.pi),
      p.1 * φ (greenPolar p.1 p.2) ∂volume) =
      greenBoundary φ (fun θ => greenPolar R θ) := by
  rw [← green_parameter_standard_disk φ hφ hcompact R hR]
  apply setIntegral_congr_fun isCompact_Icc.measurableSet
  intro p hp
  dsimp only
  rw [greenPolar_coordinateJacobian]
  ring

/-- The actual regularized harmonic filling is C² at every point of the
closed unit disk. This uses the enlarged analytic disk of its forward germ. -/
theorem regularHarmonic_contDiffAt_closedDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ContDiffAt ℝ 2 (regularHarmonic s F) z := by
  have hsinv : 1 < s⁻¹ := by
    exact one_lt_inv_iff₀.mpr ⟨hs0, hs1⟩
  have harg : conj z ∈ Metric.ball (0 : ℂ) s⁻¹ := by
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_conj] using
      (lt_of_le_of_lt hz hsinv)
  have hAnalytic : AnalyticAt ℂ (regularForwardGerm s F) (conj z) :=
    (regularForwardGerm_analyticOnNhd F hc hs0) (conj z) harg
  have hg : ContDiffAt ℝ 2 (regularForwardGerm s F) (conj z) :=
    hAnalytic.restrictScalars.contDiffAt
  have hconj : ContDiffAt ℝ 2 (fun w : ℂ => conj w) z := by
    simpa only [← Complex.conjCLE_apply] using
      (Complex.conjCLE.contDiff.contDiffAt (x := z) (n := 2))
  have hcomp : ContDiffAt ℝ 2
      (fun w : ℂ => regularForwardGerm s F (conj w)) z :=
    hg.comp z hconj
  change ContDiffAt ℝ 2
    (fun w : ℂ => w + regularForwardGerm s F (conj w)) z
  exact contDiffAt_id.add hcomp

theorem regularHarmonic_polar_contDiffAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (p : ℝ × ℝ)
    (hp : p ∈ Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 2 * Real.pi)) :
    ContDiffAt ℝ 2 (regularHarmonic s F) (greenPolar p.1 p.2) := by
  have hr0 : 0 ≤ p.1 := hp.1.1
  have hr1 : p.1 ≤ 1 := hp.2.1
  apply regularHarmonic_contDiffAt_closedDisk F hc hs0 hs1
  simpa [greenPolar_norm_of_nonneg hr0] using hr1

theorem rescaleExterior_polar_contDiffAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {R : ℝ} (hR : 1 < R) (p : ℝ × ℝ)
    (hp : p ∈ Set.Icc ((1 : ℝ), (0 : ℝ)) (R, 2 * Real.pi)) :
    ContDiffAt ℝ 2 (rescaleExterior s F) (greenPolar p.1 p.2) := by
  have hr0 : 0 ≤ p.1 := le_trans (by norm_num) hp.1.1
  have hz : greenPolar p.1 p.2 ∈ exteriorAbove s := by
    change s < ‖greenPolar p.1 p.2‖
    rw [greenPolar_norm_of_nonneg hr0]
    exact lt_of_lt_of_le hs1 hp.1.1
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z := by
    intro z hzE
    exact hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hzE)
  exact (rescaleExterior_analyticAt hs0 hF hz).restrictScalars.contDiffAt

/-- The Green parameter integral of the true regularized filling has the
expected boundary at radius one; the center contribution vanishes. -/
theorem regular_green_parameter_disk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) :
    (∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 2 * Real.pi),
      φ (regularHarmonic s F (greenPolar p.1 p.2)) *
        ((fderiv ℝ (fun q : ℝ × ℝ =>
              (regularHarmonic s F (greenPolar q.1 q.2)).re) p) (1, 0) *
            (fderiv ℝ (fun q : ℝ × ℝ =>
              (regularHarmonic s F (greenPolar q.1 q.2)).im) p) (0, 1) -
          (fderiv ℝ (fun q : ℝ × ℝ =>
              (regularHarmonic s F (greenPolar q.1 q.2)).re) p) (0, 1) *
            (fderiv ℝ (fun q : ℝ × ℝ =>
              (regularHarmonic s F (greenPolar q.1 q.2)).im) p) (1, 0))
        ∂volume) =
      greenBoundary φ (fun θ => regularHarmonic s F (greenPolar 1 θ)) := by
  have h := green_parameter_polar φ hφ hcompact
    (regularHarmonic s F) 0 1 (by norm_num)
    (regularHarmonic_polar_contDiffAt F hc hs0 hs1)
  rw [regular_greenBoundary_disk_center] at h
  simpa using h

/-- The exterior dilate contributes the outer circulation minus the actual
unit-circle circulation, with no boundary regularity assumption on F. -/
theorem regular_green_parameter_annulus
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {R : ℝ} (hR : 1 < R)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) :
    (∫ p in Set.Icc ((1 : ℝ), (0 : ℝ)) (R, 2 * Real.pi),
      φ (rescaleExterior s F (greenPolar p.1 p.2)) *
        ((fderiv ℝ (fun q : ℝ × ℝ =>
              (rescaleExterior s F (greenPolar q.1 q.2)).re) p) (1, 0) *
            (fderiv ℝ (fun q : ℝ × ℝ =>
              (rescaleExterior s F (greenPolar q.1 q.2)).im) p) (0, 1) -
          (fderiv ℝ (fun q : ℝ × ℝ =>
              (rescaleExterior s F (greenPolar q.1 q.2)).re) p) (0, 1) *
            (fderiv ℝ (fun q : ℝ × ℝ =>
              (rescaleExterior s F (greenPolar q.1 q.2)).im) p) (1, 0))
        ∂volume) =
      greenBoundary φ (fun θ => rescaleExterior s F (greenPolar R θ)) -
        greenBoundary φ (fun θ => rescaleExterior s F (greenPolar 1 θ)) := by
  exact green_parameter_polar φ hφ hcompact
    (rescaleExterior s F) 1 R hR.le
    (rescaleExterior_polar_contDiffAt F hc hs0 hs1 hR)

end SpringerLean
