import SpringerLean.Round11Polar

namespace SpringerLean

/-- The real differential of the complex polar chart, expressed through
mathlib's real polar derivative and the standard complex plane equivalence. -/
theorem greenPolar_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => greenPolar q.1 q.2)
      ((Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ).comp
        (fderivPolarCoordSymm p)) p := by
  have h := (Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ).hasFDerivAt.comp p
    (hasFDerivAt_polarCoord_symm p)
  convert h using 1
  funext q
  rw [greenPolar_eq_polarCoord_symm]
  rfl

/-- Coordinate form of the Jacobian of a map composed with the positive
polar chart. The sign is retained, including for a noninjective filling. -/
theorem greenPolar_composed_coordinateJacobian
    (W : ℂ → ℂ) (p : ℝ × ℝ)
    (hW : DifferentiableAt ℝ W (greenPolar p.1 p.2)) :
    (fderiv ℝ (fun q : ℝ × ℝ => (W (greenPolar q.1 q.2)).re) p) (1, 0) *
        (fderiv ℝ (fun q : ℝ × ℝ => (W (greenPolar q.1 q.2)).im) p) (0, 1) -
      (fderiv ℝ (fun q : ℝ × ℝ => (W (greenPolar q.1 q.2)).re) p) (0, 1) *
        (fderiv ℝ (fun q : ℝ × ℝ => (W (greenPolar q.1 q.2)).im) p) (1, 0) =
      p.1 * (fderiv ℝ W (greenPolar p.1 p.2)).det := by
  let Q : ℝ × ℝ → ℝ × ℝ := fun q =>
    ((W (greenPolar q.1 q.2)).re, (W (greenPolar q.1 q.2)).im)
  let E : ℂ ≃L[ℝ] (ℝ × ℝ) := Complex.equivRealProdCLM
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    E.toContinuousLinearMap.comp
      ((fderiv ℝ W (greenPolar p.1 p.2)).comp E.symm.toContinuousLinearMap)
  have hQ : HasFDerivAt Q (L.comp (fderivPolarCoordSymm p)) p := by
    have hcomp := E.hasFDerivAt.comp p
      (hW.hasFDerivAt.comp p (greenPolar_hasFDerivAt p))
    convert hcomp using 1
    · funext q
      simp [Q, E]
    · ext
      all_goals rfl
  have hD := realPair_clm_det_coordinates (fderiv ℝ Q p)
  rw [hQ.fderiv] at hD
  have hL : L.det = (fderiv ℝ W (greenPolar p.1 p.2)).det := by
    change LinearMap.det ((E.toLinearEquiv : ℂ ≃ₗ[ℝ] (ℝ × ℝ)).toLinearMap ∘ₗ
      (fderiv ℝ W (greenPolar p.1 p.2)).toLinearMap ∘ₗ
      E.symm.toLinearEquiv.toLinearMap) = _
    exact LinearMap.det_conj _ E.toLinearEquiv
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp] at hD
  -- The remaining equality identifies the four coordinate derivatives with
  -- the columns of the real derivative of `Q`.
  rw [show (fun q : ℝ × ℝ => (W (greenPolar q.1 q.2)).re) =
      (fun q => (Q q).1) from rfl,
    show (fun q : ℝ × ℝ => (W (greenPolar q.1 q.2)).im) =
      (fun q => (Q q).2) from rfl]
  have hQdiff : DifferentiableAt ℝ Q p := hQ.differentiableAt
  rw [fderiv.fst hQdiff, fderiv.snd hQdiff]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hQ.fderiv]
  simpa [hL, det_fderivPolarCoordSymm, mul_comm] using hD.symm

/-- Signed Green formula in positive polar coordinates, before invoking
the measure-theoretic polar change of variables. -/
theorem green_parameter_polar_signed
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (W : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hW : ∀ p ∈ Set.Icc (a, 0) (b, 2 * Real.pi),
      ContDiffAt ℝ 2 W (greenPolar p.1 p.2)) :
    (∫ p in Set.Icc (a, 0) (b, 2 * Real.pi),
      p.1 * φ (W (greenPolar p.1 p.2)) *
        (fderiv ℝ W (greenPolar p.1 p.2)).det ∂MeasureTheory.volume) =
      greenBoundary φ (fun θ => W (greenPolar b θ)) -
        greenBoundary φ (fun θ => W (greenPolar a θ)) := by
  rw [← green_parameter_polar φ hφ hcompact W a b hab hW]
  apply MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet
  intro p hp
  dsimp only
  rw [greenPolar_composed_coordinateJacobian W p
    ((hW p hp).differentiableAt (by norm_num))]
  ring

/-- The actual harmonic filling has a signed polar parameter integral equal
to its unit-circle Green circulation. -/
theorem regular_green_parameter_disk_signed
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) :
    (∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 2 * Real.pi),
      p.1 * φ (regularHarmonic s F (greenPolar p.1 p.2)) *
        (fderiv ℝ (regularHarmonic s F) (greenPolar p.1 p.2)).det
        ∂MeasureTheory.volume) =
      greenBoundary φ (fun θ => regularHarmonic s F (greenPolar 1 θ)) := by
  have h := green_parameter_polar_signed φ hφ hcompact
    (regularHarmonic s F) 0 1 (by norm_num)
    (regularHarmonic_polar_contDiffAt F hc hs0 hs1)
  rw [regular_greenBoundary_disk_center] at h
  simpa using h

/-- The actual exterior dilate has a signed polar parameter integral equal
to outer circulation minus unit-circle circulation. -/
theorem regular_green_parameter_annulus_signed
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {R : ℝ} (hR : 1 < R)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) :
    (∫ p in Set.Icc ((1 : ℝ), (0 : ℝ)) (R, 2 * Real.pi),
      p.1 * φ (rescaleExterior s F (greenPolar p.1 p.2)) *
        (fderiv ℝ (rescaleExterior s F) (greenPolar p.1 p.2)).det
        ∂MeasureTheory.volume) =
      greenBoundary φ (fun θ => rescaleExterior s F (greenPolar R θ)) -
        greenBoundary φ (fun θ => rescaleExterior s F (greenPolar 1 θ)) := by
  exact green_parameter_polar_signed φ hφ hcompact
    (rescaleExterior s F) 1 R hR.le
    (rescaleExterior_polar_contDiffAt F hc hs0 hs1 hR)

end SpringerLean
