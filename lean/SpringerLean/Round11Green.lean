import SpringerLean.Round11Rectangle

open MeasureTheory

namespace SpringerLean

/-- Both actual pulled-back flux components are C¹ wherever the parameter
map is C². This supplies continuity, fderivatives, and rectangle
integrability locally. -/
theorem greenFlux_contDiffAt
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (P : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ)
    (hP : ContDiffAt ℝ 2 P p) :
    ContDiffAt ℝ 1 (greenFluxRadial φ P) p ∧
      ContDiffAt ℝ 1 (greenFluxAngular φ P) p := by
  let X : (ℝ × ℝ) → ℝ := fun q => (P q).re
  let Y : (ℝ × ℝ) → ℝ := fun q => (P q).im
  let Q : (ℝ × ℝ) → (ℝ × ℝ) := fun q => (X q, Y q)
  have hX : ContDiffAt ℝ 2 X p := by
    change ContDiffAt ℝ 2 (Complex.reCLM ∘ P) p
    exact Complex.reCLM.contDiff.contDiffAt.comp p hP
  have hY : ContDiffAt ℝ 2 Y p :=
    complex_im_contDiffAt_of_contDiffAt P p hP
  have hQ : ContDiffAt ℝ 2 Q p := hX.prodMk hY
  have hA : ContDiffAt ℝ 1 (fun q => greenPrimitive φ (Q q)) p :=
    (greenPrimitive_contDiff φ hφ hcompact).contDiffAt.comp p
      (hQ.of_le (by norm_num))
  have hYder : ContDiffAt ℝ 1 (fderiv ℝ Y) p :=
    hY.fderiv_right (m := 1) (by norm_num)
  have hYθ : ContDiffAt ℝ 1
      (fun q => (fderiv ℝ Y q) (0, 1)) p :=
    hYder.clm_apply contDiffAt_const
  have hYr : ContDiffAt ℝ 1
      (fun q => (fderiv ℝ Y q) (1, 0)) p :=
    hYder.clm_apply contDiffAt_const
  constructor
  · change ContDiffAt ℝ 1
      (fun q => greenPrimitive φ (Q q) * (fderiv ℝ Y q) (0, 1)) p
    exact hA.mul hYθ
  · change ContDiffAt ℝ 1
      (fun q => -(greenPrimitive φ (Q q) * (fderiv ℝ Y q) (1, 0))) p
    exact (hA.mul hYr).neg

/-- Read the angular Fréchet derivative of the imaginary coordinate as
the actual one-variable tangent of the parametrized curve. -/
theorem fderiv_im_angular_eq_deriv
    (P : (ℝ × ℝ) → ℂ) (r θ : ℝ)
    (hP : DifferentiableAt ℝ P (r, θ)) :
    (fderiv ℝ (fun q => (P q).im) (r, θ)) (0, 1) =
      deriv (fun t : ℝ => (P (r, t)).im) θ := by
  have hY : DifferentiableAt ℝ (fun q => (P q).im) (r, θ) := by
    change DifferentiableAt ℝ (Complex.imCLM ∘ P) (r, θ)
    exact Complex.imCLM.differentiableAt.comp (r, θ) hP
  have hline : HasDerivAt (fun t : ℝ => (r, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ r).prodMk (hasDerivAt_id θ)
  have hchain := hY.hasFDerivAt.comp_hasDerivAt θ hline
  simpa [Function.comp_def] using hchain.deriv.symm

theorem fderiv_im_radial_eq_deriv
    (P : (ℝ × ℝ) → ℂ) (r θ : ℝ)
    (hP : DifferentiableAt ℝ P (r, θ)) :
    (fderiv ℝ (fun q => (P q).im) (r, θ)) (1, 0) =
      deriv (fun t : ℝ => (P (t, θ)).im) r := by
  have hY : DifferentiableAt ℝ (fun q => (P q).im) (r, θ) := by
    change DifferentiableAt ℝ (Complex.imCLM ∘ P) (r, θ)
    exact Complex.imCLM.differentiableAt.comp (r, θ) hP
  have hline : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) r := by
    simpa using (hasDerivAt_id r).prodMk (hasDerivAt_const r θ)
  have hchain := hY.hasFDerivAt.comp_hasDerivAt r hline
  simpa [Function.comp_def] using hchain.deriv.symm

/-- Global equality of the two angular endpoint curves gives exactly the
local radial-flux periodicity used by the rectangle theorem. -/
theorem greenFluxAngular_periodic
    (φ : ℂ → ℝ) (P : (ℝ × ℝ) → ℂ) (r : ℝ)
    (hP0 : DifferentiableAt ℝ P (r, 0))
    (hP2 : DifferentiableAt ℝ P (r, 2 * Real.pi))
    (hperiod : ∀ t : ℝ, P (t, 2 * Real.pi) = P (t, 0)) :
    greenFluxAngular φ P (r, 2 * Real.pi) =
      greenFluxAngular φ P (r, 0) := by
  have hcurves :
      (fun t : ℝ => (P (t, 2 * Real.pi)).im) =
        (fun t : ℝ => (P (t, 0)).im) := by
    funext t
    rw [hperiod t]
  simp only [greenFluxAngular,
    fderiv_im_radial_eq_deriv P r (2 * Real.pi) hP2,
    fderiv_im_radial_eq_deriv P r 0 hP0,
    hperiod r, hcurves]

/-- Parameter Green formula for the actual primitive and a map that is C²
on the closed parameter rectangle. The angular traces agree as functions
of the radial coordinate; no smoothness is imposed away from the rectangle. -/
theorem green_parameter_rectangle
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (P : (ℝ × ℝ) → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hP : ∀ p ∈ Set.Icc (a, 0) (b, 2 * Real.pi),
      ContDiffAt ℝ 2 P p)
    (hperiod : ∀ r : ℝ, P (r, 2 * Real.pi) = P (r, 0)) :
    (∫ p in Set.Icc (a, 0) (b, 2 * Real.pi),
      φ (P p) *
        ((fderiv ℝ (fun q => (P q).re) p) (1, 0) *
            (fderiv ℝ (fun q => (P q).im) p) (0, 1) -
          (fderiv ℝ (fun q => (P q).re) p) (0, 1) *
            (fderiv ℝ (fun q => (P q).im) p) (1, 0)) ∂volume) =
      greenBoundary φ (fun θ => P (b, θ)) -
        greenBoundary φ (fun θ => P (a, θ)) := by
  let S : Set (ℝ × ℝ) := Set.Icc (a, 0) (b, 2 * Real.pi)
  let f := greenFluxRadial φ P
  let g := greenFluxAngular φ P
  have hθ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hmem (p : ℝ × ℝ)
      (hp : p ∈ Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) : p ∈ S := by
    change (a, 0) ≤ p ∧ p ≤ (b, 2 * Real.pi)
    exact ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩
  have hfcont : ContinuousOn f S :=
    continuousOn_of_forall_continuousAt fun p hp =>
      ((greenFlux_contDiffAt φ hφ hcompact P p (hP p hp)).1).continuousAt
  have hgcont : ContinuousOn g S :=
    continuousOn_of_forall_continuousAt fun p hp =>
      ((greenFlux_contDiffAt φ hφ hcompact P p (hP p hp)).2).continuousAt
  have hfder : ∀ p ∈ Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
      HasFDerivAt f (fderiv ℝ f p) p := by
    intro p hp
    exact ((greenFlux_contDiffAt φ hφ hcompact P p
      (hP p (hmem p hp))).1.differentiableAt (by norm_num)).hasFDerivAt
  have hgder : ∀ p ∈ Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
      HasFDerivAt g (fderiv ℝ g p) p := by
    intro p hp
    exact ((greenFlux_contDiffAt φ hφ hcompact P p
      (hP p (hmem p hp))).2.differentiableAt (by norm_num)).hasFDerivAt
  have hint : IntegrableOn
      (fun p => (fderiv ℝ f p) (1, 0) + (fderiv ℝ g p) (0, 1)) S := by
    have hc : ContinuousOn
        (fun p => (fderiv ℝ f p) (1, 0) + (fderiv ℝ g p) (0, 1)) S := by
      apply continuousOn_of_forall_continuousAt
      intro p hp
      obtain ⟨hfp, hgp⟩ := greenFlux_contDiffAt φ hφ hcompact P p (hP p hp)
      have hfc : ContinuousAt (fderiv ℝ f) p :=
        (hfp.fderiv_right (m := 0) (by norm_num)).continuousAt
      have hgc : ContinuousAt (fderiv ℝ g) p :=
        (hgp.fderiv_right (m := 0) (by norm_num)).continuousAt
      exact (hfc.clm_apply continuousAt_const).add
        (hgc.clm_apply continuousAt_const)
    exact hc.integrableOn_compact (show IsCompact S from isCompact_Icc)
  have hgperiod : ∀ r ∈ Set.Icc a b,
      g (r, 2 * Real.pi) = g (r, 0) := by
    intro r hr
    have hp0 : (r, 0) ∈ S := by
      change (a, 0) ≤ (r, 0) ∧ (r, 0) ≤ (b, 2 * Real.pi)
      exact ⟨⟨hr.1, le_refl _⟩, ⟨hr.2, hθ⟩⟩
    have hp2 : (r, 2 * Real.pi) ∈ S := by
      change (a, 0) ≤ (r, 2 * Real.pi) ∧
        (r, 2 * Real.pi) ≤ (b, 2 * Real.pi)
      exact ⟨⟨hr.1, hθ⟩, ⟨hr.2, le_refl _⟩⟩
    exact greenFluxAngular_periodic φ P r
      ((hP _ hp0).differentiableAt (by norm_num))
      ((hP _ hp2).differentiableAt (by norm_num)) hperiod
  have hrect := periodic_rectangle_flux_local f g
    (fderiv ℝ f) (fderiv ℝ g) a b 0 (2 * Real.pi)
    hab hθ hfcont hgcont hfder hgder hint hgperiod
  have hpoint :
      (∫ p in S, φ (P p) *
        ((fderiv ℝ (fun q => (P q).re) p) (1, 0) *
            (fderiv ℝ (fun q => (P q).im) p) (0, 1) -
          (fderiv ℝ (fun q => (P q).re) p) (0, 1) *
            (fderiv ℝ (fun q => (P q).im) p) (1, 0)) ∂volume) =
      ∫ p in S, (fderiv ℝ f p) (1, 0) +
        (fderiv ℝ g p) (0, 1) ∂volume := by
    apply setIntegral_congr_fun isCompact_Icc.measurableSet
    intro p hp
    exact (greenFlux_pointwise φ hφ hcompact P p (hP p hp)).symm
  have hedge (r : ℝ) (hr : r ∈ Set.Icc a b) :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), f (r, θ) ∂volume) =
        greenBoundary φ (fun θ => P (r, θ)) := by
    unfold greenBoundary
    apply intervalIntegral.integral_congr
    intro θ hθmem
    have hθ' : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
      simpa [Set.uIcc_of_le hθ] using hθmem
    have hp : (r, θ) ∈ S := by
      change (a, 0) ≤ (r, θ) ∧ (r, θ) ≤ (b, 2 * Real.pi)
      exact ⟨⟨hr.1, hθ'.1⟩, ⟨hr.2, hθ'.2⟩⟩
    have hPd : DifferentiableAt ℝ P (r, θ) :=
      (hP _ hp).differentiableAt (by norm_num)
    simp [f, greenFluxRadial, fderiv_im_angular_eq_deriv P r θ hPd]
  change (∫ p in S, _ ∂volume) = _
  rw [hpoint, hrect, hedge b ⟨hab, le_refl _⟩,
    hedge a ⟨le_refl _, hab⟩]

end SpringerLean
