import SpringerLean.Round11Green
import Mathlib.Analysis.Analytic.Constructions

open MeasureTheory

namespace SpringerLean

/-- The outer homotopy uses the same radius and actual regularized exterior
map as the cutoff theorem. -/
noncomputable def greenOuterHomotopy
    (F : ℂ → ℂ) (s R : ℝ) (p : ℝ × ℝ) : ℂ :=
  greenPolar R p.2 + (p.1 : ℂ) *
    (rescaleExterior s F (greenPolar R p.2) - greenPolar R p.2)

@[simp] theorem greenOuterHomotopy_zero
    (F : ℂ → ℂ) (s R θ : ℝ) :
    greenOuterHomotopy F s R (0, θ) = greenPolar R θ := by
  simp [greenOuterHomotopy]

@[simp] theorem greenOuterHomotopy_one
    (F : ℂ → ℂ) (s R θ : ℝ) :
    greenOuterHomotopy F s R (1, θ) =
      rescaleExterior s F (greenPolar R θ) := by
  simp [greenOuterHomotopy]

theorem greenOuterHomotopy_periodic
    (F : ℂ → ℂ) (s R t : ℝ) :
    greenOuterHomotopy F s R (t, 2 * Real.pi) =
      greenOuterHomotopy F s R (t, 0) := by
  simp [greenOuterHomotopy]

/-- The outer homotopy is genuinely C² in its two real parameters. -/
theorem greenOuterHomotopy_contDiff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {R : ℝ} (hR : 1 < R) :
    ContDiff ℝ 2 (greenOuterHomotopy F s R) := by
  have hpolar : ContDiff ℝ 2 (fun θ : ℝ => greenPolar R θ) := by
    have hcast : ContDiff ℝ 2 (fun θ : ℝ => (θ : ℂ)) := by
      change ContDiff ℝ 2 (Complex.ofRealCLM : ℝ → ℂ)
      exact Complex.ofRealCLM.contDiff
    change ContDiff ℝ 2 (fun θ : ℝ =>
      (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    exact contDiff_const.mul ((hcast.mul contDiff_const).cexp)
  have hGcurve : ContDiff ℝ 2
      (fun θ : ℝ => rescaleExterior s F (greenPolar R θ)) := by
    rw [contDiff_iff_contDiffAt]
    intro θ
    have hz : greenPolar R θ ∈ exteriorAbove s := by
      change s < ‖greenPolar R θ‖
      rw [greenPolar_norm_of_nonneg (le_trans (by norm_num) hR.le)]
      exact lt_trans hs1 hR
    have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z := by
      intro z hzE
      exact hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hzE)
    have hGcomplex : AnalyticAt ℂ (rescaleExterior s F) (greenPolar R θ) :=
      rescaleExterior_analyticAt hs0 hF hz
    have hGreal : ContDiffAt ℝ 2 (rescaleExterior s F) (greenPolar R θ) :=
      hGcomplex.restrictScalars.contDiffAt
    exact hGreal.comp θ hpolar.contDiffAt
  have hpolar2 : ContDiff ℝ 2
      (fun p : ℝ × ℝ => greenPolar R p.2) :=
    hpolar.comp contDiff_snd
  have hG2 : ContDiff ℝ 2
      (fun p : ℝ × ℝ => rescaleExterior s F (greenPolar R p.2)) :=
    hGcurve.comp contDiff_snd
  have ht : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.1 : ℂ)) := by
    change ContDiff ℝ 2 (Complex.ofRealCLM ∘ Prod.fst)
    exact Complex.ofRealCLM.contDiff.comp contDiff_fst
  change ContDiff ℝ 2 (fun p : ℝ × ℝ =>
    greenPolar R p.2 + (p.1 : ℂ) *
      (rescaleExterior s F (greenPolar R p.2) - greenPolar R p.2))
  exact hpolar2.add (ht.mul (hG2.sub hpolar2))

/-- The outer homotopy contributes zero signed Green area, so its two
oriented boundary circulations agree. The returned radius is the same one
that controls the entire exterior tail of the actual cutoff. -/
theorem regular_greenBoundary_outer_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    ∃ R : ℝ, 1 < R ∧
      (∀ z : ℂ, R ≤ ‖z‖ →
        evenWeightCutoff T hT k z = 0) ∧
      (∀ z : ℂ, R ≤ ‖z‖ →
        evenWeightCutoff T hT k (rescaleExterior s F z) = 0) ∧
      greenBoundary (evenWeightCutoff T hT k)
          (fun θ => rescaleExterior s F (greenPolar R θ)) =
        greenBoundary (evenWeightCutoff T hT k)
          (fun θ => greenPolar R θ) := by
  obtain ⟨R, hR, hfar⟩ :=
    regular_evenWeightCutoff_far_outer F hc hs0 hs1 T hT k
  let φ : ℂ → ℝ := evenWeightCutoff T hT k
  let P : (ℝ × ℝ) → ℂ := greenOuterHomotopy F s R
  have hP : ContDiff ℝ 2 P :=
    greenOuterHomotopy_contDiff F hc hs0 hs1 hR
  have hgreen := green_parameter_rectangle φ
    (evenWeightCutoff_contDiff T hT k)
    (evenWeightCutoff_hasCompactSupport T hT k)
    P 0 1 (by norm_num)
    (fun p hp => hP.contDiffAt)
    (greenOuterHomotopy_periodic F s R)
  have hzero :
      (∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 2 * Real.pi),
        φ (P p) *
          ((fderiv ℝ (fun q => (P q).re) p) (1, 0) *
              (fderiv ℝ (fun q => (P q).im) p) (0, 1) -
            (fderiv ℝ (fun q => (P q).re) p) (0, 1) *
              (fderiv ℝ (fun q => (P q).im) p) (1, 0)) ∂volume) = 0 := by
    have heq :
        (∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 2 * Real.pi),
          φ (P p) *
            ((fderiv ℝ (fun q => (P q).re) p) (1, 0) *
                (fderiv ℝ (fun q => (P q).im) p) (0, 1) -
              (fderiv ℝ (fun q => (P q).re) p) (0, 1) *
                (fderiv ℝ (fun q => (P q).im) p) (1, 0)) ∂volume) =
        ∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 2 * Real.pi),
          (0 : ℝ) ∂volume := by
      apply setIntegral_congr_fun isCompact_Icc.measurableSet
      intro p hp
      have hp0 : 0 ≤ p.1 := hp.1.1
      have hp1 : p.1 ≤ 1 := hp.2.1
      have hR0 : 0 ≤ R := le_trans (by norm_num) hR.le
      have hnorm : R ≤ ‖greenPolar R p.2‖ :=
        (greenPolar_norm_of_nonneg hR0 p.2).ge
      have hφzero := (hfar (greenPolar R p.2) hnorm).2 p.1 hp0 hp1
      simp [φ, P, greenOuterHomotopy, hφzero]
    simpa using heq
  rw [hzero] at hgreen
  have hC : greenBoundary φ (fun θ => P (1, θ)) =
      greenBoundary φ (fun θ => P (0, θ)) := by
    exact sub_eq_zero.mp hgreen.symm
  refine ⟨R, hR, ?_, (fun z hz => (hfar z hz).1), ?_⟩
  · intro z hz
    simpa using (hfar z hz).2 0 (le_refl _) (by norm_num)
  simpa [φ, P] using hC

end SpringerLean
