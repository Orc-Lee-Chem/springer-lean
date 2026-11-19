import SpringerLean.Round80PolynomialCutoff

namespace SpringerLean

open MeasureTheory

/-- On a horizontal segment where the Green weight is identically one,
its real primitive is the first coordinate. This is the exact local
conversion needed to read a boundary circulation by Fourier modes. -/
theorem greenPrimitive_eq_first_of_one_on_horizontal
    (φ : ℂ → ℝ) (x y : ℝ)
    (hφ : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      φ ((t : ℂ) + Complex.I * (y : ℂ)) = 1) :
    greenPrimitive φ (x, y) = x := by
  unfold greenPrimitive
  rw [intervalIntegral.integral_congr (fun t ht => hφ t ht)]
  simp

/-- If the Green weight equals one along every horizontal segment from
the imaginary axis to a closed curve, its boundary integral is the
standard oriented integral `∫ X dY`. -/
theorem greenBoundary_eq_real_deriv_im_of_one_on_horizontal
    (φ : ℂ → ℝ) (c : ℝ → ℂ)
    (hφ : ∀ θ : ℝ, ∀ t ∈ Set.uIcc (0 : ℝ) (c θ).re,
      φ ((t : ℂ) + Complex.I * ((c θ).im : ℂ)) = 1) :
    greenBoundary φ c =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (c θ).re * deriv (fun t : ℝ => (c t).im) θ := by
  unfold greenBoundary
  apply intervalIntegral.integral_congr
  intro θ _
  change greenPrimitive φ ((c θ).re, (c θ).im) * _ = _ * _
  rw [greenPrimitive_eq_first_of_one_on_horizontal φ (c θ).re (c θ).im
    (hφ θ)]

/-- A radial bump that is one on a sufficiently large ball remains one
along the entire horizontal segment used by the Green primitive. -/
theorem areaBump_one_on_horizontal
    (T : ℝ) (hT : 0 ≤ T) (x y : ℝ)
    (hxy : |x| + |y| ≤ T) :
    ∀ t ∈ Set.uIcc (0 : ℝ) x,
      areaBump T hT ((t : ℂ) + Complex.I * (y : ℂ)) = 1 := by
  intro t ht
  have htx : |t| ≤ |x| := by
    rcases (Set.mem_uIcc.mp ht) with ⟨ht0, htx⟩ | ⟨hxt, ht0⟩
    · rw [abs_of_nonneg ht0, abs_of_nonneg (le_trans ht0 htx)]
      exact htx
    · rw [abs_of_nonpos ht0, abs_of_nonpos (le_trans hxt ht0)]
      linarith
  have hnorm : ‖(t : ℂ) + Complex.I * (y : ℂ)‖ ≤ T := by
    calc
      ‖(t : ℂ) + Complex.I * (y : ℂ)‖ ≤
          ‖(t : ℂ)‖ + ‖Complex.I * (y : ℂ)‖ := norm_add_le _ _
      _ = |t| + |y| := by simp
      _ ≤ |x| + |y| := by linarith
      _ ≤ T := hxy
  apply (areaBump T hT).one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right, areaBump] using
    (show ‖(t : ℂ) + Complex.I * (y : ℂ)‖ ≤ T + 1 by linarith)

/-- On a curve bounded in coordinate ℓ¹ norm, the radial bump Green
boundary form is exactly the usual oriented `X dY` integral. -/
theorem areaBump_greenBoundary_eq_real_deriv_im
    (T : ℝ) (hT : 0 ≤ T) (c : ℝ → ℂ)
    (hc : ∀ θ : ℝ, |(c θ).re| + |(c θ).im| ≤ T) :
    greenBoundary (areaBump T hT) c =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (c θ).re * deriv (fun t : ℝ => (c t).im) θ := by
  exact greenBoundary_eq_real_deriv_im_of_one_on_horizontal
    (areaBump T hT) c
    (fun θ => areaBump_one_on_horizontal T hT (c θ).re (c θ).im (hc θ))

/-- A generic signed disk area formula in the exact form needed for the
Faber Fourier calculation. The compact cutoff is eliminated from the
interior by `hφdisk`, and from the boundary primitive by `hφhorizontal`. -/
theorem green_disk_signed_area_eq_oriented_boundary
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ) (W : ℂ → ℂ)
    (hW : ∀ z : ℂ, ‖z‖ ≤ 1 → ContDiffAt ℝ 2 W z)
    (hφdisk : ∀ z : ℂ, ‖z‖ < 1 → φ (W z) = 1)
    (hφhorizontal : ∀ θ : ℝ,
      ∀ t ∈ Set.uIcc (0 : ℝ) (W (greenPolar 1 θ)).re,
        φ ((t : ℂ) + Complex.I *
          ((W (greenPolar 1 θ)).im : ℂ)) = 1) :
    (∫ z in Metric.ball (0 : ℂ) 1,
        (fderiv ℝ W z).det ∂volume) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (W (greenPolar 1 θ)).re *
          deriv (fun t : ℝ => (W (greenPolar 1 t)).im) θ := by
  have hpolar := green_signed_polar_integral_eq_region φ hφ W 0 1
    (by norm_num) (fun z hz0 hz1 => hW z hz1)
  have hparam := green_parameter_polar_signed φ hφ hcompact W 0 1
    (by norm_num) (by
      intro p hp
      have hp0 : 0 ≤ p.1 := hp.1.1
      have hp1 : p.1 ≤ 1 := hp.2.1
      apply hW
      rw [greenPolar_norm_of_nonneg hp0]
      exact hp1)
  have hregion : greenPolarRegion 0 1 =
      Metric.ball (0 : ℂ) 1 \ {0} := by
    ext z
    simp [greenPolarRegion, Metric.mem_ball, dist_zero_right,
      norm_pos_iff, and_comm]
  have hae : greenPolarRegion 0 1 =ᵐ[volume]
      Metric.ball (0 : ℂ) 1 := by
    rw [hregion]
    exact sdiff_null_ae_eq_self (measure_singleton (0 : ℂ))
  have hset :
      (∫ z in greenPolarRegion 0 1,
        φ (W z) * (fderiv ℝ W z).det ∂volume) =
      (∫ z in Metric.ball (0 : ℂ) 1,
        (fderiv ℝ W z).det ∂volume) := by
    rw [setIntegral_congr_set hae]
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro z hz
    change φ (W z) * (fderiv ℝ W z).det = (fderiv ℝ W z).det
    rw [hφdisk z (by simpa only [Metric.mem_ball, dist_zero_right] using hz)]
    ring
  have hcenter : greenBoundary φ (fun θ => W (greenPolar 0 θ)) = 0 := by
    simpa [greenPolar] using greenBoundary_const φ (W 0)
  rw [hcenter, sub_zero] at hparam
  have hboundary := greenBoundary_eq_real_deriv_im_of_one_on_horizontal
    φ (fun θ => W (greenPolar 1 θ)) hφhorizontal
  exact hset.symm.trans (hpolar.symm.trans (hparam.trans hboundary))

/-- Actual polynomial-composed regular fillings have a genuine signed
area equal to their oriented boundary integral. The auxiliary bump and
its radius are constructed inside the proof. -/
theorem faberPolynomial_regular_comp_area_eq_boundary
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : Polynomial ℂ) :
    (∫ z in Metric.ball (0 : ℂ) 1,
        (fderiv ℝ (fun z => P.eval (regularHarmonic s F z)) z).det ∂volume) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (P.eval (regularHarmonic s F (greenPolar 1 θ))).re *
          deriv (fun t : ℝ =>
            (P.eval (regularHarmonic s F (greenPolar 1 t))).im) θ := by
  have hEval : ∀ Q : Polynomial ℂ,
      ContDiff ℝ 2 (fun w : ℂ => Q.eval w) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q hp hq => simpa using hp.add hq
    | monomial n a =>
        simpa [Polynomial.eval_monomial] using
          (contDiff_const : ContDiff ℝ 2 (fun _ : ℂ => a)).mul
            ((contDiff_id : ContDiff ℝ 2 (fun w : ℂ => w)).pow n)
  obtain ⟨C, hC0, hC⟩ := regularHarmonic_uniform_bound_closedDisk F hc
  let K : Set ℂ := Metric.closedBall 0 C
  have hKcompact : IsCompact K := isCompact_closedBall 0 C
  have himage : Bornology.IsBounded ((fun w : ℂ => P.eval w) '' K) :=
    (hKcompact.image_of_continuousOn (hEval P).continuous.continuousOn).isBounded
  obtain ⟨M, hM⟩ := himage.exists_norm_le
  let T : ℝ := 2 * max M 0 + 1
  have hT : 0 ≤ T := by dsimp [T]; linarith [le_max_right M 0]
  have hbound : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖P.eval (regularHarmonic s F z)‖ ≤ M := by
    intro z hz
    apply hM
    exact ⟨regularHarmonic s F z,
      by simpa only [K, Metric.mem_closedBall, dist_zero_right] using
        hC s hs0 hs1 z hz, rfl⟩
  let W : ℂ → ℂ := fun z => P.eval (regularHarmonic s F z)
  let φ : ℂ → ℝ := areaBump T hT
  have hW : ∀ z : ℂ, ‖z‖ ≤ 1 → ContDiffAt ℝ 2 W z := by
    intro z hz
    exact (hEval P).contDiffAt.comp z
      (regularHarmonic_contDiffAt_closedDisk F hc hs0 hs1 hz)
  have hφdisk : ∀ z : ℂ, ‖z‖ < 1 → φ (W z) = 1 := by
    intro z hz
    apply (areaBump T hT).one_of_mem_closedBall
    have hb := hbound z hz.le
    have hMT : M ≤ T := by dsimp [T]; linarith [le_max_left M 0]
    simpa only [Metric.mem_closedBall, dist_zero_right, φ, areaBump] using
      (show ‖W z‖ ≤ T + 1 by dsimp [W]; linarith)
  have hφhorizontal : ∀ θ : ℝ,
      ∀ t ∈ Set.uIcc (0 : ℝ) (W (greenPolar 1 θ)).re,
        φ ((t : ℂ) + Complex.I *
          ((W (greenPolar 1 θ)).im : ℂ)) = 1 := by
    intro θ
    have hcircle : ‖greenPolar 1 θ‖ ≤ 1 := by
      simpa using (greenPolar_norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) θ).le
    have hb := hbound (greenPolar 1 θ) hcircle
    have hre : |(W (greenPolar 1 θ)).re| ≤ ‖W (greenPolar 1 θ)‖ :=
      Complex.abs_re_le_norm _
    have him : |(W (greenPolar 1 θ)).im| ≤ ‖W (greenPolar 1 θ)‖ :=
      Complex.abs_im_le_norm _
    have hxy : |(W (greenPolar 1 θ)).re| +
        |(W (greenPolar 1 θ)).im| ≤ T := by
      dsimp [T]
      linarith [le_max_left M 0]
    exact areaBump_one_on_horizontal T hT _ _ hxy
  simpa only [W, φ] using
    (green_disk_signed_area_eq_oriented_boundary φ
      (areaBump T hT).contDiff (areaBump T hT).hasCompactSupport
      W hW hφdisk hφhorizontal)

/-- The boundary in the preceding area identity is the actual
regularized exterior image curve, with its tangential derivative. -/
theorem faberPolynomial_regular_comp_area_eq_actual_exterior_boundary
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : Polynomial ℂ) :
    (∫ z in Metric.ball (0 : ℂ) 1,
        (fderiv ℝ (fun z => P.eval (regularHarmonic s F z)) z).det ∂volume) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (P.eval (rescaleExterior s F (greenPolar 1 θ))).re *
          deriv (fun t : ℝ =>
            (P.eval (rescaleExterior s F (greenPolar 1 t))).im) θ := by
  have hcurve :
      (fun θ : ℝ => P.eval (regularHarmonic s F (greenPolar 1 θ))) =
      (fun θ : ℝ => P.eval (rescaleExterior s F (greenPolar 1 θ))) := by
    funext θ
    simpa [greenPolar] using congrArg (fun w : ℂ => P.eval w)
      (congrFun (regularHarmonic_boundary_curve_eq F hs0) θ)
  have h := faberPolynomial_regular_comp_area_eq_boundary F hc hs0 hs1 P
  have hbound := congrArg (fun c : ℝ → ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (c θ).re * deriv (fun t : ℝ => (c t).im) θ) hcurve
  exact h.trans hbound

/-- The actual regularized exterior boundary curve has nonnegative
oriented area after every polynomial map, even though the polynomial
need not be injective. Its omitted-set meaning is provided by Round80. -/
theorem faberPolynomial_actual_exterior_boundary_area_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : Polynomial ℂ) :
    0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (P.eval (rescaleExterior s F (greenPolar 1 θ))).re *
        deriv (fun t : ℝ =>
          (P.eval (rescaleExterior s F (greenPolar 1 t))).im) θ := by
  rw [← faberPolynomial_regular_comp_area_eq_actual_exterior_boundary
    F hc hs0 hs1 P]
  exact faberPolynomial_comp_signedDisk_nonneg F hc hs0 hs1 P

/-- Exact oriented boundary area of `P ∘ F_s` equals the integral of
`‖P′‖²` over the actual omitted set. This is the geometric identity
underlying the finite Faber coefficient inequality. -/
theorem faberPolynomial_actual_exterior_boundary_eq_omitted
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : Polynomial ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (P.eval (rescaleExterior s F (greenPolar 1 θ))).re *
        deriv (fun t : ℝ =>
          (P.eval (rescaleExterior s F (greenPolar 1 t))).im) θ) =
      ∫ w in exteriorOmitted (rescaleExterior s F),
        ‖P.derivative.eval w‖ ^ 2 ∂volume := by
  have hboundary :=
    (faberPolynomial_regular_comp_area_eq_actual_exterior_boundary
      F hc hs0 hs1 P).symm
  have hJac :
      (∫ z in Metric.ball (0 : ℂ) 1,
        (fderiv ℝ (fun z => P.eval (regularHarmonic s F z)) z).det ∂volume) =
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖P.derivative.eval (regularHarmonic s F z)‖ ^ 2 *
          (fderiv ℝ (regularHarmonic s F) z).det ∂volume) := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro z hz
    exact faberPolynomial_regular_comp_jacobian F hc hs0 hs1 P
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  exact hboundary.trans (hJac.trans
    (faberPolynomial_regular_omitted_area F hc hs0 hs1 P))

end SpringerLean
