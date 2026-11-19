import SpringerLean.Round79FaberArea
import SpringerLean.Round09Cutoff
import SpringerLean.Round11Outer
import SpringerLean.Round11FinalGreen
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace SpringerLean

open MeasureTheory

/-- A compactly supported real polynomial-derivative area weight. -/
noncomputable def faberPolynomialCutoff
    (T : ℝ) (hT : 0 ≤ T) (P : Polynomial ℂ) (w : ℂ) : ℝ :=
  areaBump T hT w * Complex.normSq (P.derivative.eval w)

theorem faberPolynomialCutoff_eq_weight
    (T : ℝ) (hT : 0 ≤ T) (P : Polynomial ℂ)
    {w : ℂ} (hw : ‖w‖ ≤ T) :
    faberPolynomialCutoff T hT P w = ‖P.derivative.eval w‖ ^ 2 := by
  have hb : areaBump T hT w = 1 := by
    apply (areaBump T hT).one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_zero_right, areaBump] using
      (show ‖w‖ ≤ T + 1 by linarith)
  simp [faberPolynomialCutoff, hb, Complex.normSq_eq_norm_sq]

theorem faberPolynomialCutoff_zero_of_far
    (T : ℝ) (hT : 0 ≤ T) (P : Polynomial ℂ)
    {w : ℂ} (hw : T + 2 ≤ ‖w‖) :
    faberPolynomialCutoff T hT P w = 0 := by
  have hb : areaBump T hT w = 0 := by
    apply (areaBump T hT).zero_of_le_dist
    simpa only [areaBump, dist_zero_right] using hw
  simp [faberPolynomialCutoff, hb]

theorem faberPolynomialCutoff_hasCompactSupport
    (T : ℝ) (hT : 0 ≤ T) (P : Polynomial ℂ) :
    HasCompactSupport (faberPolynomialCutoff T hT P) :=
  (areaBump T hT).hasCompactSupport.mul_right

theorem faberPolynomialCutoff_contDiff
    (T : ℝ) (hT : 0 ≤ T) (P : Polynomial ℂ) :
    ContDiff ℝ 1 (faberPolynomialCutoff T hT P) := by
  have hEval : ∀ Q : Polynomial ℂ,
      ContDiff ℝ 1 (fun w : ℂ => Q.eval w) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q hp hq => simpa using hp.add hq
    | monomial n a =>
        simpa [Polynomial.eval_monomial] using
          (contDiff_const : ContDiff ℝ 1 (fun _ : ℂ => a)).mul
            ((contDiff_id : ContDiff ℝ 1 (fun w : ℂ => w)).pow n)
  have hnormsq : ContDiff ℝ 1
      (fun w : ℂ => Complex.normSq (P.derivative.eval w)) := by
    have hreal : ContDiff ℝ 1
        (fun w : ℂ => (P.derivative.eval w).re) :=
      Complex.reCLM.contDiff.comp (hEval P.derivative)
    have himag : ContDiff ℝ 1
        (fun w : ℂ => (P.derivative.eval w).im) :=
      Complex.imCLM.contDiff.comp (hEval P.derivative)
    simpa only [Complex.normSq_apply] using
      (hreal.mul hreal).add (himag.mul himag)
  exact (areaBump T hT).contDiff.mul hnormsq

/-- One outer radius works simultaneously for the actual regularized
exterior image and the entire straight-line homotopy to the standard
circle. This is the compact-support input for the Faber Green formula. -/
theorem faberPolynomialCutoff_far_outer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (T : ℝ) (hT : 0 ≤ T) (P : Polynomial ℂ) :
    ∃ R : ℝ, 1 < R ∧
      ∀ z : ℂ, R ≤ ‖z‖ →
        faberPolynomialCutoff T hT P (rescaleExterior s F z) = 0 ∧
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          faberPolynomialCutoff T hT P
            (z + (t : ℂ) * (rescaleExterior s F z - z)) = 0 := by
  obtain ⟨C, hC0, hC⟩ := rescaleExterior_sub_id_bounded F hc hs0 hs1
  let R : ℝ := max (T + 2 + C) 1 + 1
  have hR1 : 1 < R := by dsimp [R]; linarith [le_max_right (T + 2 + C) 1]
  have hRTC : T + 2 + C ≤ R := by
    dsimp [R]
    linarith [le_max_left (T + 2 + C) 1]
  refine ⟨R, hR1, ?_⟩
  intro z hz
  constructor
  · exact rescaleExterior_compact_weight_vanish_far F hC hRTC
      (faberPolynomialCutoff T hT P)
      (fun w hw => faberPolynomialCutoff_zero_of_far T hT P hw) hz hR1
  · intro t ht0 ht1
    exact rescaleExterior_outer_homotopy_weight_vanish F hC0 hC hRTC
      (faberPolynomialCutoff T hT P)
      (fun w hw => faberPolynomialCutoff_zero_of_far T hT P hw)
      hz hR1 ht0 ht1

/-- The Faber polynomial cutoff has the same oriented circulation on the
large actual exterior circle and on the corresponding standard circle. -/
theorem faberPolynomial_greenBoundary_outer_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (T : ℝ) (hT : 0 ≤ T) (Q : Polynomial ℂ) :
    ∃ R : ℝ, 1 < R ∧
      (∀ z : ℂ, R ≤ ‖z‖ →
        faberPolynomialCutoff T hT Q z = 0) ∧
      (∀ z : ℂ, R ≤ ‖z‖ →
        faberPolynomialCutoff T hT Q (rescaleExterior s F z) = 0) ∧
      greenBoundary (faberPolynomialCutoff T hT Q)
          (fun θ => rescaleExterior s F (greenPolar R θ)) =
        greenBoundary (faberPolynomialCutoff T hT Q)
          (fun θ => greenPolar R θ) := by
  obtain ⟨R, hR, hfar⟩ :=
    faberPolynomialCutoff_far_outer F hc hs0 hs1 T hT Q
  let φ : ℂ → ℝ := faberPolynomialCutoff T hT Q
  let H : (ℝ × ℝ) → ℂ := greenOuterHomotopy F s R
  have hH : ContDiff ℝ 2 H :=
    greenOuterHomotopy_contDiff F hc hs0 hs1 hR
  have hgreen := green_parameter_rectangle φ
    (faberPolynomialCutoff_contDiff T hT Q)
    (faberPolynomialCutoff_hasCompactSupport T hT Q)
    H 0 1 (by norm_num)
    (fun p hp => hH.contDiffAt)
    (greenOuterHomotopy_periodic F s R)
  have hzero :
      (∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 2 * Real.pi),
        φ (H p) *
          ((fderiv ℝ (fun q => (H q).re) p) (1, 0) *
              (fderiv ℝ (fun q => (H q).im) p) (0, 1) -
            (fderiv ℝ (fun q => (H q).re) p) (0, 1) *
              (fderiv ℝ (fun q => (H q).im) p) (1, 0)) ∂volume) = 0 := by
    have heq :
        (∫ p in Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 2 * Real.pi),
          φ (H p) *
            ((fderiv ℝ (fun q => (H q).re) p) (1, 0) *
                (fderiv ℝ (fun q => (H q).im) p) (0, 1) -
              (fderiv ℝ (fun q => (H q).re) p) (0, 1) *
                (fderiv ℝ (fun q => (H q).im) p) (1, 0)) ∂volume) =
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
      simp [φ, H, greenOuterHomotopy, hφzero]
    simpa using heq
  rw [hzero] at hgreen
  have hC : greenBoundary φ (fun θ => H (1, θ)) =
      greenBoundary φ (fun θ => H (0, θ)) := by
    exact sub_eq_zero.mp hgreen.symm
  refine ⟨R, hR, ?_, (fun z hz => (hfar z hz).1), ?_⟩
  · intro z hz
    simpa using (hfar z hz).2 0 (le_refl _) (by norm_num)
  · simpa [φ, H] using hC

/-- Signed Green partition with a polynomial derivative square weight.
The exterior term uses the actual univalent map; the harmonic filling
retains its signed real Jacobian. -/
theorem faberPolynomial_signedPartition
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (T : ℝ) (hT : 0 ≤ T) (P : Polynomial ℂ) :
    (∫ z in Metric.ball (0 : ℂ) 1,
        faberPolynomialCutoff T hT P (regularHarmonic s F z) *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) +
      (∫ z in exteriorDisk,
        ‖deriv (rescaleExterior s F) z‖ ^ 2 *
          faberPolynomialCutoff T hT P (rescaleExterior s F z) ∂volume) =
      ∫ w : ℂ, faberPolynomialCutoff T hT P w ∂volume := by
  obtain ⟨R, hR, hφfar, hGfar, houter⟩ :=
    faberPolynomial_greenBoundary_outer_eq F hc hs0 hs1 T hT P
  let φ : ℂ → ℝ := faberPolynomialCutoff T hT P
  have hφ : ContDiff ℝ 1 φ := faberPolynomialCutoff_contDiff T hT P
  have hcompact : HasCompactSupport φ :=
    faberPolynomialCutoff_hasCompactSupport T hT P
  have hD := regular_green_disk_area F hc hs0 hs1 φ hφ hcompact
  have hA := regular_green_annulus_area F hc hs0 hs1 hR φ hφ hcompact
  have hE := regular_exterior_signed_cutoff_integral_eq
    F hc hs0 hs1 hR φ hGfar
  have hS := green_standard_disk_area φ hφ hcompact R
    (lt_trans (by norm_num : (0 : ℝ) < 1) hR)
  have hfull :
      (∫ w in Metric.ball (0 : ℂ) R, φ w ∂volume) =
        ∫ w : ℂ, φ w ∂volume := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    apply hφfar w
    exact le_of_not_gt (by
      intro hlt
      apply hw
      simpa only [Metric.mem_ball, dist_zero_right] using hlt)
  have hunit := regular_greenBoundary_unit_eq F hs0 φ
  change (∫ z in Metric.ball (0 : ℂ) 1,
        φ (regularHarmonic s F z) *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) +
      (∫ z in exteriorDisk,
        ‖deriv (rescaleExterior s F) z‖ ^ 2 *
          φ (rescaleExterior s F z) ∂volume) =
      ∫ w : ℂ, φ w ∂volume
  linarith

/-- The signed filling integral equals the polynomial-derivative weight
of the *actual* omitted set. Positivity of the right side is available
even though the harmonic filling's Jacobian may change sign. -/
theorem faberPolynomial_signedDisk_eq_omitted_cutoff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (T : ℝ) (hT : 0 ≤ T) (P : Polynomial ℂ) :
    (∫ z in Metric.ball (0 : ℂ) 1,
        faberPolynomialCutoff T hT P (regularHarmonic s F z) *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) =
      ∫ w in exteriorOmitted (rescaleExterior s F),
        faberPolynomialCutoff T hT P w ∂volume := by
  let G : ℂ → ℂ := rescaleExterior s F
  let φ : ℂ → ℝ := faberPolynomialCutoff T hT P
  have hcG : CenteredExteriorUnivalent G :=
    rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have himage : MeasurableSet (G '' exteriorDisk) := by
    simpa only [exteriorOmitted, compl_compl] using
      (exteriorOmitted_measurableSet G hcG).compl
  have hφint : Integrable φ volume :=
    (faberPolynomialCutoff_contDiff T hT P).continuous.integrable_of_hasCompactSupport
      (faberPolynomialCutoff_hasCompactSupport T hT P)
  have hdecomp := integral_add_compl himage hφint
  have hchange := (exteriorImage_compact_weight_change G hcG φ
    (faberPolynomialCutoff_contDiff T hT P).continuous
    (faberPolynomialCutoff_hasCompactSupport T hT P)).2
  have hpart := faberPolynomial_signedPartition F hc hs0 hs1 T hT P
  dsimp only [G, φ] at hpart hchange
  rw [← hchange] at hpart
  have hdecomp' :
      (∫ w in G '' exteriorDisk, φ w ∂volume) +
        (∫ w in exteriorOmitted G, φ w ∂volume) =
          ∫ w : ℂ, φ w ∂volume := by
    simpa only [exteriorOmitted] using hdecomp
  dsimp only [G, φ] at hdecomp' ⊢
  linarith

/-- Exact weighted omitted-area identity for each polynomial derivative
square weight and each regularized *actual* exterior map. No cutoff or
boundary assumptions remain in this statement. -/
theorem faberPolynomial_regular_omitted_area
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : Polynomial ℂ) :
    (∫ z in Metric.ball (0 : ℂ) 1,
        ‖P.derivative.eval (regularHarmonic s F z)‖ ^ 2 *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) =
      ∫ w in exteriorOmitted (rescaleExterior s F),
        ‖P.derivative.eval w‖ ^ 2 ∂volume := by
  obtain ⟨C, hC0, hC⟩ := regularHarmonic_uniform_bound_closedDisk F hc
  let G : ℂ → ℂ := rescaleExterior s F
  have hcG : CenteredExteriorUnivalent G :=
    rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  obtain ⟨M, hM0, hM⟩ := exteriorOmitted_bounded G hcG
  let T : ℝ := max C M + 1
  have hT : 0 ≤ T := by dsimp [T]; linarith [le_max_left C M]
  have hH : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      faberPolynomialCutoff T hT P (regularHarmonic s F z) =
        ‖P.derivative.eval (regularHarmonic s F z)‖ ^ 2 := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    apply faberPolynomialCutoff_eq_weight T hT P
    exact (hC s hs0 hs1 z hz').trans
      (by dsimp [T]; linarith [le_max_left C M])
  have hK : ∀ w ∈ exteriorOmitted G,
      faberPolynomialCutoff T hT P w = ‖P.derivative.eval w‖ ^ 2 := by
    intro w hw
    apply faberPolynomialCutoff_eq_weight T hT P
    exact (hM w hw).trans
      (by dsimp [T]; linarith [le_max_right C M])
  have hraw := faberPolynomial_signedDisk_eq_omitted_cutoff
    F hc hs0 hs1 T hT P
  have hD :
      (∫ z in Metric.ball (0 : ℂ) 1,
          faberPolynomialCutoff T hT P (regularHarmonic s F z) *
            (fderiv ℝ (regularHarmonic s F) z).det ∂volume) =
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖P.derivative.eval (regularHarmonic s F z)‖ ^ 2 *
            (fderiv ℝ (regularHarmonic s F) z).det ∂volume) := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro z hz
    change faberPolynomialCutoff T hT P (regularHarmonic s F z) * _ = _ * _
    rw [hH z (Metric.ball_subset_closedBall hz)]
  have hO :
      (∫ w in exteriorOmitted G,
          faberPolynomialCutoff T hT P w ∂volume) =
        (∫ w in exteriorOmitted G,
          ‖P.derivative.eval w‖ ^ 2 ∂volume) := by
    apply setIntegral_congr_fun (exteriorOmitted_measurableSet G hcG)
    intro w hw
    exact hK w hw
  change _ = (∫ w in exteriorOmitted G,
    ‖P.derivative.eval w‖ ^ 2 ∂volume)
  exact hD.symm.trans (hraw.trans hO)

/-- The signed regularized filling area with a polynomial derivative
weight is nonnegative because it is the genuine omitted-set integral. -/
theorem faberPolynomial_regular_signedDisk_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : Polynomial ℂ) :
    0 ≤ ∫ z in Metric.ball (0 : ℂ) 1,
      ‖P.derivative.eval (regularHarmonic s F z)‖ ^ 2 *
        (fderiv ℝ (regularHarmonic s F) z).det ∂volume := by
  rw [faberPolynomial_regular_omitted_area F hc hs0 hs1 P]
  exact integral_nonneg (fun w => sq_nonneg _)

/-- Chain rule for the signed real Jacobian of a polynomial applied to
the regular harmonic filling. This is the local bridge to its boundary
Fourier calculation; no injectivity of the polynomial is used. -/
theorem faberPolynomial_regular_comp_jacobian
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : Polynomial ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (fderiv ℝ (fun z => P.eval (regularHarmonic s F z)) z).det =
      ‖P.derivative.eval (regularHarmonic s F z)‖ ^ 2 *
        (fderiv ℝ (regularHarmonic s F) z).det := by
  have hP := (P.hasDerivAt (regularHarmonic s F z)).complexToReal_fderiv
  have hH := regularHarmonic_hasFDerivAt_real F hc hs0 hs1 hz
  have hcomp := hP.comp z hH
  change (fderiv ℝ ((fun w : ℂ => P.eval w) ∘ regularHarmonic s F) z).det = _
  rw [hcomp.fderiv]
  rw [← hH.fderiv]
  change (((P.derivative.eval (regularHarmonic s F z)) •
    (1 : ℂ →L[ℝ] ℂ)).comp (fderiv ℝ (regularHarmonic s F) z)).det = _
  change (((P.derivative.eval (regularHarmonic s F z)) •
    (1 : ℂ →L[ℝ] ℂ)).toLinearMap.comp
      (fderiv ℝ (regularHarmonic s F) z).toLinearMap).det = _
  rw [LinearMap.det_comp]
  change (((P.derivative.eval (regularHarmonic s F z)) •
      (1 : ℂ →L[ℝ] ℂ)).det) *
      (fderiv ℝ (regularHarmonic s F) z).det = _
  rw [complex_mul_real_det, Complex.normSq_eq_norm_sq]

/-- The polynomial-composed actual filling has nonnegative signed area.
This is the geometric input for the finite Faber Fourier inequality. -/
theorem faberPolynomial_comp_signedDisk_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : Polynomial ℂ) :
    0 ≤ ∫ z in Metric.ball (0 : ℂ) 1,
      (fderiv ℝ (fun z => P.eval (regularHarmonic s F z)) z).det ∂volume := by
  have hEq :
      (∫ z in Metric.ball (0 : ℂ) 1,
        (fderiv ℝ (fun z => P.eval (regularHarmonic s F z)) z).det ∂volume) =
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖P.derivative.eval (regularHarmonic s F z)‖ ^ 2 *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro z hz
    exact faberPolynomial_regular_comp_jacobian F hc hs0 hs1 P
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  rw [hEq]
  exact faberPolynomial_regular_signedDisk_nonneg F hc hs0 hs1 P

end SpringerLean
