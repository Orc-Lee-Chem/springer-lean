import SpringerLean.Round1758LipschitzPartialIntegral
import SpringerLean.Round1692ActualHorizontalSliceDerivative
import SpringerLean.Round1733CartesianDivergenceLinear
import Mathlib.Analysis.Calculus.Rademacher

open MeasureTheory Filter

namespace SpringerLean

/-- Coordinatewise absolute continuity proves zero total divergence
for a Lipschitz plane field supported in the unit disk. No C1
assumption, or nullity of any prescribed level set, is used. -/
theorem integral_actualCartesianDiv_zero_of_lipschitz_unit_support
    (J : ℂ → ℂ) (K : NNReal) (hJ : LipschitzWith K J)
    (hzero : ∀ z : ℂ, 1 ≤ ‖z‖ → J z = 0) :
    Integrable (actualCartesianDiv J) ∧
      (∫ z : ℂ, actualCartesianDiv J z) = 0 := by
  let e : ℝ × ℝ → ℂ := fun p => Complex.mk p.1 p.2
  let fr : ℝ × ℝ → ℝ := fun p => (J (e p)).re
  let fi : ℝ × ℝ → ℝ := fun p => (J (e p)).im
  let fis : ℝ × ℝ → ℝ := fun p => fi p.swap
  have he : (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) = e := by
    ext p
    apply Complex.ext <;> simp [e, Complex.equivRealProdCLM_symm_apply]
  have hrlip : ∃ C : NNReal, LipschitzWith C fr := by
    have h := Complex.reCLM.lipschitzWith.comp
      (hJ.comp Complex.equivRealProdCLM.symm.lipschitzWith)
    refine ⟨‖Complex.reCLM‖₊ *
      (K * ‖(Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ)‖₊), ?_⟩
    convert h using 1
    rw [he]
    rfl
  have hilip : ∃ C : NNReal, LipschitzWith C fi := by
    have h := Complex.imCLM.lipschitzWith.comp
      (hJ.comp Complex.equivRealProdCLM.symm.lipschitzWith)
    refine ⟨‖Complex.imCLM‖₊ *
      (K * ‖(Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ)‖₊), ?_⟩
    convert h using 1
    rw [he]
    rfl
  have hnorm (p : ℝ × ℝ) (hp : 1 ≤ |p.1| ∨ 1 ≤ |p.2|) :
      1 ≤ ‖e p‖ := by
    rcases hp with hp | hp
    · exact hp.trans (by simpa [e] using Complex.abs_re_le_norm (e p))
    · exact hp.trans (by simpa [e] using Complex.abs_im_le_norm (e p))
  have hrzero (p : ℝ × ℝ) (hp : 1 ≤ |p.1| ∨ 1 ≤ |p.2|) : fr p = 0 := by
    dsimp [fr]
    rw [hzero (e p) (hnorm p hp)]
    rfl
  have hizero (p : ℝ × ℝ) (hp : 1 ≤ |p.1| ∨ 1 ≤ |p.2|) : fi p = 0 := by
    dsimp [fi]
    rw [hzero (e p) (hnorm p hp)]
    rfl
  have hswaplip : LipschitzWith 1 (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp [Prod.dist_eq, max_comm]
  obtain ⟨Kr, hrlip⟩ := hrlip
  obtain ⟨Ki, hilip⟩ := hilip
  have hfislip : LipschitzWith (Ki*1) fis := hilip.comp hswaplip
  have hfiszero (p : ℝ × ℝ) (hp : 1 ≤ |p.1| ∨ 1 ≤ |p.2|) : fis p = 0 :=
    hizero p.swap hp.symm
  obtain ⟨hrInt, hrZero⟩ := integral_horizontalSliceDeriv_zero fr Kr hrlip hrzero
  obtain ⟨hsInt, hsZero⟩ := integral_horizontalSliceDeriv_zero fis (Ki*1) hfislip hfiszero
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      (volume : Measure (ℝ × ℝ)) volume := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ)))
  let dy : ℝ × ℝ → ℝ := fun p => horizontalSliceDeriv fis p.swap
  have hyInt : Integrable dy := hswap.integrable_comp_of_integrable hsInt
  have hyZero : (∫ p : ℝ × ℝ, dy p) = 0 := by
    rw [hswap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding]
    exact hsZero
  let d : ℝ × ℝ → ℝ := fun p => horizontalSliceDeriv fr p + dy p
  have hdInt : Integrable d := hrInt.add hyInt
  have hdZero : (∫ p : ℝ × ℝ, d p) = 0 := by
    rw [integral_add hrInt hyInt, hrZero, hyZero]
    norm_num
  let g : ℂ → ℝ := fun z => d (Complex.measurableEquivRealProd z)
  have hgInt : Integrable g :=
    Complex.volume_preserving_equiv_real_prod.integrable_comp_of_integrable hdInt
  have hgZero : (∫ z : ℂ, g z) = 0 := by
    rw [Complex.volume_preserving_equiv_real_prod.integral_comp' d]
    exact hdZero
  have heq : actualCartesianDiv J =ᵐ[volume] g := by
    filter_upwards [hJ.ae_differentiableAt (μ := (volume : Measure ℂ))] with z hz
    have hre : DifferentiableAt ℝ (fun w => (J w).re) z :=
      Complex.reCLM.differentiableAt.comp z hz
    have him : DifferentiableAt ℝ (fun w => (J w).im) z :=
      Complex.imCLM.differentiableAt.comp z hz
    have hx := deriv_comp_complexMk_first (fun w => (J w).re) z.re z.im
      (by simpa using hre)
    have hy := deriv_comp_complexMk_second (fun w => (J w).im) z.re z.im
      (by simpa using him)
    change actualCartesianDiv J z =
      horizontalSliceDeriv fr (z.re, z.im) +
        horizontalSliceDeriv fis (z.im, z.re)
    dsimp [horizontalSliceDeriv, fr, fis, fi, e]
    rw [hx, hy]
    simp [actualCartesianDiv]
  exact ⟨hgInt.congr heq.symm, (integral_congr_ae heq).trans hgZero⟩

end SpringerLean

#print axioms SpringerLean.integral_actualCartesianDiv_zero_of_lipschitz_unit_support
