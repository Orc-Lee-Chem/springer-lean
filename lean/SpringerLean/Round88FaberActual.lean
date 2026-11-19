import SpringerLean.Round87LaurentFourier

open scoped NNReal ENNReal

namespace SpringerLean

/-- Actual derivative-read Taylor series preserve addition of analytic
functions. This is needed to identify Faber reciprocal factors with the
already verified formal coefficient formulas. -/
theorem actualTaylorSeries_add
    (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    actualTaylorSeries (fun u => f u + g u) =
      actualTaylorSeries f + actualTaylorSeries g := by
  ext n
  simp only [actualTaylorSeries_coeff, map_add, actualTaylorCoeff]
  rw [iteratedDeriv_fun_add
    (hf.contDiffAt.of_le le_top) (hg.contDiffAt.of_le le_top)]
  ring

/-- The corresponding subtraction identity. -/
theorem actualTaylorSeries_sub
    (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    actualTaylorSeries (fun u => f u - g u) =
      actualTaylorSeries f - actualTaylorSeries g := by
  ext n
  simp only [actualTaylorSeries_coeff, map_sub, actualTaylorCoeff]
  rw [iteratedDeriv_fun_sub
    (hf.contDiffAt.of_le le_top) (hg.contDiffAt.of_le le_top)]
  ring

/-- A scalar factor commutes with the independently derivative-read Taylor
series. -/
theorem actualTaylorSeries_const_mul (c : ℂ) (f : ℂ → ℂ) :
    actualTaylorSeries (fun u => c * f u) =
      PowerSeries.C c * actualTaylorSeries f := by
  ext n
  simp only [actualTaylorSeries_coeff, PowerSeries.coeff_C_mul,
    actualTaylorCoeff]
  have hder : iteratedDeriv n (fun u => c * f u) 0 =
      c * iteratedDeriv n f 0 := by
    simpa only [Pi.mul_apply] using
      (iteratedDeriv_const_mul_field (n := n) (x := (0 : ℂ)) c f)
  rw [hder]
  ring

/-- The actual Taylor series of a complex monomial is the formal monomial. -/
theorem actualTaylorSeries_monomial (m : ℕ) :
    actualTaylorSeries (fun u : ℂ => u ^ m) = PowerSeries.X ^ m := by
  ext n
  simp only [actualTaylorSeries_coeff, actualTaylorCoeff]
  rw [iteratedDeriv_fun_pow_zero]
  by_cases h : n = m
  · subst n
    have hf : (m.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero m
    simp [hf]
  · simp [h]

/-- Actual derivative-read Taylor polynomials converge uniformly on the
closed unit disk whenever the function is analytic on a larger disk. This
value counterpart of `analytic_deriv_uniform_closedUnitDisk` applies to all
three regularized Faber reciprocal factors. -/
theorem analytic_actualTaylor_uniform_closedUnitDisk
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) :
    TendstoUniformlyOn
      (fun M u => ∑ j ∈ Finset.range M,
        actualTaylorCoeff h j * u ^ j)
      h Filter.atTop (Metric.closedBall (0 : ℂ) 1) := by
  let r : ℝ≥0 := ⟨(R + 1) / 2, by linarith⟩
  have hr1 : (1 : ℝ≥0) < r := by
    apply NNReal.coe_lt_coe.mp
    change (1 : ℝ) < (R + 1) / 2
    linarith
  have hrR : (r : ℝ) < R := by
    change (R + 1) / 2 < R
    linarith
  have hr0 : (0 : ℝ≥0) < r := lt_trans (by norm_num) hr1
  have hd : DifferentiableOn ℂ h (Metric.closedBall 0 r) :=
    hh.differentiableOn.mono (Metric.closedBall_subset_ball hrR)
  have hp := hd.hasFPowerSeriesOnBall hr0
  have hzero : (0 : ℂ) ∈ Metric.ball 0 R := by
    simp only [Metric.mem_ball, dist_self]
    linarith
  have hcanon := (hh 0 hzero).hasFPowerSeriesAt
  have heq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hcanon
  rw [heq] at hp
  let t : ℝ≥0 := ⟨((r : ℝ) + 1) / 2, by positivity⟩
  have h1t : (1 : ℝ) < t := by
    change (1 : ℝ) < ((r : ℝ) + 1) / 2
    have h : (1 : ℝ) < r := by exact_mod_cast hr1
    linarith
  have htr : (t : ℝ) < r := by
    change ((r : ℝ) + 1) / 2 < r
    have h : (1 : ℝ) < r := by exact_mod_cast hr1
    linarith
  have hrad : (t : ℝ≥0∞) < (r : ℝ≥0∞) := by
    exact_mod_cast htr
  have huniform := (hp.tendstoUniformlyOn hrad).mono
    (Metric.closedBall_subset_ball h1t)
  simpa [FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.coeff_ofScalars, actualTaylorCoeff,
    smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using huniform

/-- Uniform Taylor convergence of any analytic reciprocal factor around the
regularized exterior boundary, with the actual circle variable. -/
theorem analytic_actualTaylor_uniform_unitCircle
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) :
    TendstoUniformlyOn
      (fun M (θ : AddCircle (2 * Real.pi)) =>
        ∑ j ∈ Finset.range M,
          actualTaylorCoeff h j * (fourier (-1) θ) ^ j)
      (fun θ => h (fourier (-1) θ)) Filter.atTop Set.univ := by
  let point : AddCircle (2 * Real.pi) → ℂ := fun θ => fourier (-1) θ
  have hsubset : Set.univ ⊆ point ⁻¹' Metric.closedBall (0 : ℂ) 1 := by
    intro θ _
    change dist (point θ) 0 ≤ 1
    rw [dist_zero_right]
    change ‖fourier (-1) θ‖ ≤ 1
    rw [fourier_apply, Circle.norm_coe]
  simpa only [point, Function.comp_def] using
    ((analytic_actualTaylor_uniform_closedUnitDisk h hR hh).comp point).mono hsubset

/-- The matching angular derivative series is uniformly convergent after
taking the complex derivative of the analytic reciprocal factor. -/
theorem analytic_actualTaylor_deriv_uniform_unitCircle
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) :
    TendstoUniformlyOn
      (fun M (θ : AddCircle (2 * Real.pi)) =>
        ∑ j ∈ Finset.range M,
          (j + 1 : ℂ) * actualTaylorCoeff h (j + 1) *
            (fourier (-1) θ) ^ j)
      (fun θ => deriv h (fourier (-1) θ)) Filter.atTop Set.univ := by
  let point : AddCircle (2 * Real.pi) → ℂ := fun θ => fourier (-1) θ
  have hsubset : Set.univ ⊆ point ⁻¹' Metric.closedBall (0 : ℂ) 1 := by
    intro θ _
    change dist (point θ) 0 ≤ 1
    rw [dist_zero_right]
    change ‖fourier (-1) θ‖ ≤ 1
    rw [fourier_apply, Circle.norm_coe]
  simpa only [point, Function.comp_def] using
    ((analytic_deriv_uniform_closedUnitDisk h hR hh).comp point).mono hsubset

theorem fourier_one_pow (j : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    (fourier 1 θ) ^ j = fourier (j : ℤ) θ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih]
    have hi : (((j + 1 : ℕ) : ℤ)) = (j : ℤ) + 1 := by omega
    rw [hi, fourier_add]

theorem fourier_neg_one_inv (θ : AddCircle (2 * Real.pi)) :
    (fourier (-1) θ)⁻¹ = fourier 1 θ := by
  have hnorm : ‖fourier 1 θ‖ = 1 := by
    rw [fourier_apply, Circle.norm_coe]
  have hneg : fourier (-1) θ = (fourier 1 θ)⁻¹ := by
    rw [fourier_neg]
    exact (Complex.inv_eq_conj hnorm).symm
  rw [hneg, inv_inv]

theorem fourier_neg_one_pow_inv (j : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    ((fourier (-1) θ) ^ j)⁻¹ = fourier (j : ℤ) θ := by
  rw [← inv_pow, fourier_neg_one_inv, fourier_one_pow]

/-- First Faber polynomial in the paper's centered exterior normalization. -/
noncomputable def firstFaberPolynomial (F : ℂ → ℂ) : Polynomial ℂ :=
  Polynomial.X

/-- Second Faber polynomial. Its constant correction removes the constant
term of `F(z)^2` at infinity. -/
noncomputable def secondFaberPolynomial (F : ℂ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 2 - Polynomial.C (2 * exteriorForwardCoeff F 1)

/-- Third Faber polynomial. Its linear and constant corrections remove the
nonnegative modes below the leading `z^3` mode. -/
noncomputable def thirdFaberPolynomial (F : ℂ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 3 -
    Polynomial.C (3 * exteriorForwardCoeff F 1) * Polynomial.X -
    Polynomial.C (3 * exteriorForwardCoeff F 2)

/-- Exact reciprocal-coordinate identity for the actual first Faber
polynomial, valid at every nonzero reciprocal coordinate. -/
theorem firstFaberPolynomial_reciprocal_factor
    (F : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    u * (firstFaberPolynomial F).eval (F u⁻¹) = exteriorPhi F u := by
  simp only [firstFaberPolynomial, Polynomial.eval_X]
  rw [exteriorF_reciprocal_phi F hu]
  field_simp [hu]

/-- Actual second Faber polynomial after reciprocal multiplication. The
right side is analytic wherever the regularized forward germ is analytic. -/
theorem secondFaberPolynomial_reciprocal_factor
    (F : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    u ^ 2 * (secondFaberPolynomial F).eval (F u⁻¹) =
      (exteriorPhi F u) ^ 2 -
        2 * exteriorForwardCoeff F 1 * u ^ 2 := by
  simp only [secondFaberPolynomial, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [exteriorF_reciprocal_phi F hu]
  field_simp [hu]

/-- Actual third Faber polynomial after reciprocal multiplication, with the
same sign and coefficient convention used in the formal kernel calculations. -/
theorem thirdFaberPolynomial_reciprocal_factor
    (F : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    u ^ 3 * (thirdFaberPolynomial F).eval (F u⁻¹) =
      (exteriorPhi F u) ^ 3 -
        3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
        3 * exteriorForwardCoeff F 2 * u ^ 3 := by
  simp only [thirdFaberPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [exteriorF_reciprocal_phi F hu]
  field_simp [hu]

/-- The regularized forward factor is analytic on the enlarged reciprocal
disk `|u|<1/s`, which contains the closed unit circle when `s<1`. -/
theorem rescaleExterior_phi_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) :
    AnalyticOnNhd ℂ (exteriorPhi (rescaleExterior s F))
      (Metric.ball 0 s⁻¹) := by
  have hident : exteriorPhi (rescaleExterior s F) =
      (fun u : ℂ => 1 + u * regularForwardGerm s F u) := by
    funext u
    rw [exteriorPhi, regularForwardGerm,
      rescaleExterior_forwardGerm s hs0 F u]
  rw [hident]
  intro u hu
  have hg := regularForwardGerm_analyticOnNhd F hc hs0 u hu
  fun_prop

/-- The reciprocal factor of the second actual Faber polynomial is
analytic throughout that enlarged disk. -/
theorem rescaleExterior_secondFaberFactor_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) :
    AnalyticOnNhd ℂ
      (fun u : ℂ =>
        (exteriorPhi (rescaleExterior s F) u) ^ 2 -
          2 * exteriorForwardCoeff (rescaleExterior s F) 1 * u ^ 2)
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hphi := rescaleExterior_phi_analyticOnNhd F hc hs0 u hu
  fun_prop

/-- The reciprocal factor of the third actual Faber polynomial is
analytic throughout the same enlarged disk. -/
theorem rescaleExterior_thirdFaberFactor_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) :
    AnalyticOnNhd ℂ
      (fun u : ℂ =>
        (exteriorPhi (rescaleExterior s F) u) ^ 3 -
          3 * exteriorForwardCoeff (rescaleExterior s F) 1 * u ^ 2 *
            exteriorPhi (rescaleExterior s F) u -
          3 * exteriorForwardCoeff (rescaleExterior s F) 2 * u ^ 3)
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hphi := rescaleExterior_phi_analyticOnNhd F hc hs0 u hu
  fun_prop

/-- The actual second Faber factor of the regularized map has a uniformly
convergent derivative-read Taylor expansion on the unit circle, together
with the uniformly convergent derivative expansion. -/
theorem rescaleExterior_secondFaberFactor_uniform_boundary
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi (rescaleExterior s F) u) ^ 2 -
        2 * exteriorForwardCoeff (rescaleExterior s F) 1 * u ^ 2
    TendstoUniformlyOn
      (fun M (θ : AddCircle (2 * Real.pi)) =>
        ∑ j ∈ Finset.range M,
          actualTaylorCoeff A j * (fourier (-1) θ) ^ j)
      (fun θ => A (fourier (-1) θ)) Filter.atTop Set.univ ∧
    TendstoUniformlyOn
      (fun M (θ : AddCircle (2 * Real.pi)) =>
        ∑ j ∈ Finset.range M,
          (j + 1 : ℂ) * actualTaylorCoeff A (j + 1) *
            (fourier (-1) θ) ^ j)
      (fun θ => deriv A (fourier (-1) θ)) Filter.atTop Set.univ := by
  dsimp
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hA := rescaleExterior_secondFaberFactor_analyticOnNhd F hc hs0
  exact ⟨analytic_actualTaylor_uniform_unitCircle _ hR hA,
    analytic_actualTaylor_deriv_uniform_unitCircle _ hR hA⟩

/-- The third actual Faber factor has the same uniform boundary value and
derivative control, now with the cubic polynomial corrections. -/
theorem rescaleExterior_thirdFaberFactor_uniform_boundary
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi (rescaleExterior s F) u) ^ 3 -
        3 * exteriorForwardCoeff (rescaleExterior s F) 1 * u ^ 2 *
          exteriorPhi (rescaleExterior s F) u -
        3 * exteriorForwardCoeff (rescaleExterior s F) 2 * u ^ 3
    TendstoUniformlyOn
      (fun M (θ : AddCircle (2 * Real.pi)) =>
        ∑ j ∈ Finset.range M,
          actualTaylorCoeff A j * (fourier (-1) θ) ^ j)
      (fun θ => A (fourier (-1) θ)) Filter.atTop Set.univ ∧
    TendstoUniformlyOn
      (fun M (θ : AddCircle (2 * Real.pi)) =>
        ∑ j ∈ Finset.range M,
          (j + 1 : ℂ) * actualTaylorCoeff A (j + 1) *
            (fourier (-1) θ) ^ j)
      (fun θ => deriv A (fourier (-1) θ)) Filter.atTop Set.univ := by
  dsimp
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hA := rescaleExterior_thirdFaberFactor_analyticOnNhd F hc hs0
  exact ⟨analytic_actualTaylor_uniform_unitCircle _ hR hA,
    analytic_actualTaylor_deriv_uniform_unitCircle _ hR hA⟩

/-- Convert a reciprocal-coordinate factorization into an exact boundary
Fourier factorization. This lemma retains the polynomial's positive leading
frequency and the analytic reciprocal factor separately. -/
theorem reciprocal_factor_to_fourier_boundary
    (F : ℂ → ℂ) (P : Polynomial ℂ) (j : ℕ) (A : ℂ → ℂ)
    (hfactor : ∀ {u : ℂ}, u ≠ 0 →
      u ^ j * P.eval (F u⁻¹) = A u)
    (θ : AddCircle (2 * Real.pi)) :
    P.eval (F (fourier 1 θ)) =
      fourier (j : ℤ) θ * A (fourier (-1) θ) := by
  have hu : fourier (-1) θ ≠ 0 := by
    intro h
    have hn : ‖fourier (-1) θ‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    simp [h] at hn
  have hh := hfactor (u := fourier (-1) θ) hu
  rw [fourier_neg_one_inv] at hh
  calc
    P.eval (F (fourier 1 θ)) =
        ((fourier (-1) θ) ^ j)⁻¹ *
          ((fourier (-1) θ) ^ j * P.eval (F (fourier 1 θ))) := by
            field_simp [hu]
    _ = fourier (j : ℤ) θ * A (fourier (-1) θ) := by
      rw [fourier_neg_one_pow_inv, hh]

theorem firstFaberPolynomial_boundary_factor
    (F : ℂ → ℂ) (θ : AddCircle (2 * Real.pi)) :
    (firstFaberPolynomial F).eval (F (fourier 1 θ)) =
      fourier 1 θ * exteriorPhi F (fourier (-1) θ) := by
  simpa only [Nat.cast_one] using
    reciprocal_factor_to_fourier_boundary F (firstFaberPolynomial F) 1
      (exteriorPhi F)
      (fun {u : ℂ} hu => by simpa only [pow_one] using
        firstFaberPolynomial_reciprocal_factor F hu) θ

theorem secondFaberPolynomial_boundary_factor
    (F : ℂ → ℂ) (θ : AddCircle (2 * Real.pi)) :
    (secondFaberPolynomial F).eval (F (fourier 1 θ)) =
      fourier 2 θ *
        ((exteriorPhi F (fourier (-1) θ)) ^ 2 -
          2 * exteriorForwardCoeff F 1 * (fourier (-1) θ) ^ 2) := by
  simpa only [Nat.cast_ofNat] using
    reciprocal_factor_to_fourier_boundary F (secondFaberPolynomial F) 2
      (fun u => (exteriorPhi F u) ^ 2 -
        2 * exteriorForwardCoeff F 1 * u ^ 2)
      (fun {u : ℂ} hu => secondFaberPolynomial_reciprocal_factor F hu) θ

theorem thirdFaberPolynomial_boundary_factor
    (F : ℂ → ℂ) (θ : AddCircle (2 * Real.pi)) :
    (thirdFaberPolynomial F).eval (F (fourier 1 θ)) =
      fourier 3 θ *
        ((exteriorPhi F (fourier (-1) θ)) ^ 3 -
          3 * exteriorForwardCoeff F 1 * (fourier (-1) θ) ^ 2 *
            exteriorPhi F (fourier (-1) θ) -
          3 * exteriorForwardCoeff F 2 * (fourier (-1) θ) ^ 3) := by
  simpa only [Nat.cast_ofNat] using
    reciprocal_factor_to_fourier_boundary F (thirdFaberPolynomial F) 3
      (fun u => (exteriorPhi F u) ^ 3 -
        3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
        3 * exteriorForwardCoeff F 2 * u ^ 3)
      (fun {u : ℂ} hu => thirdFaberPolynomial_reciprocal_factor F hu) θ

/-- The actual reciprocal factor of the second Faber polynomial has exactly
the formal coefficients used in the logarithmic kernel calculation. -/
theorem secondFaberFactor_actualTaylorSeries
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorSeries
      (fun u : ℂ => (exteriorPhi F u) ^ 2 -
        2 * exteriorForwardCoeff F 1 * u ^ 2) =
      (formalExteriorPhi (exteriorFormalForward F)) ^ 2 -
        PowerSeries.C (2 * exteriorForwardCoeff F 1) * PowerSeries.X ^ 2 := by
  have hphi := exteriorPhi_analyticAt F hc.2.2
  have hpow : AnalyticAt ℂ (fun u : ℂ => (exteriorPhi F u) ^ 2) 0 :=
    hphi.pow 2
  have hmon : AnalyticAt ℂ
      (fun u : ℂ => 2 * exteriorForwardCoeff F 1 * u ^ 2) 0 := by
    fun_prop
  rw [actualTaylorSeries_sub _ _ hpow hmon,
    actualTaylorSeries_pow _ hphi,
    actualTaylorSeries_const_mul,
    actualTaylorSeries_monomial,
    exteriorPhi_actualTaylorSeries F hc]

/-- The corresponding actual third Faber factor matches its finite formal
expression coefficient by coefficient. -/
theorem thirdFaberFactor_actualTaylorSeries
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorSeries
      (fun u : ℂ => (exteriorPhi F u) ^ 3 -
        3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
        3 * exteriorForwardCoeff F 2 * u ^ 3) =
      (formalExteriorPhi (exteriorFormalForward F)) ^ 3 -
        PowerSeries.C (3 * exteriorForwardCoeff F 1) *
          PowerSeries.X ^ 2 * formalExteriorPhi (exteriorFormalForward F) -
        PowerSeries.C (3 * exteriorForwardCoeff F 2) * PowerSeries.X ^ 3 := by
  have hphi := exteriorPhi_analyticAt F hc.2.2
  have hpow : AnalyticAt ℂ (fun u : ℂ => (exteriorPhi F u) ^ 3) 0 :=
    hphi.pow 3
  have hmiddle : AnalyticAt ℂ
      (fun u : ℂ => 3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u) 0 := by
    fun_prop
  have hlast : AnalyticAt ℂ
      (fun u : ℂ => 3 * exteriorForwardCoeff F 2 * u ^ 3) 0 := by
    fun_prop
  have hfirst : actualTaylorSeries
      (fun u : ℂ => (exteriorPhi F u) ^ 3 -
        3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u) =
      actualTaylorSeries (fun u : ℂ => (exteriorPhi F u) ^ 3) -
        actualTaylorSeries
          (fun u : ℂ => 3 * exteriorForwardCoeff F 1 * u ^ 2 *
            exteriorPhi F u) :=
    actualTaylorSeries_sub _ _ hpow hmiddle
  have hwhole : actualTaylorSeries
      (fun u : ℂ => (exteriorPhi F u) ^ 3 -
        3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
        3 * exteriorForwardCoeff F 2 * u ^ 3) =
      actualTaylorSeries
        (fun u : ℂ => (exteriorPhi F u) ^ 3 -
          3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u) -
      actualTaylorSeries
        (fun u : ℂ => 3 * exteriorForwardCoeff F 2 * u ^ 3) :=
    actualTaylorSeries_sub _ _ (by fun_prop) hlast
  have hm : actualTaylorSeries
      (fun u : ℂ => 3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u) =
      PowerSeries.C (3 * exteriorForwardCoeff F 1) *
        PowerSeries.X ^ 2 * formalExteriorPhi (exteriorFormalForward F) := by
    have heq : (fun u : ℂ => 3 * exteriorForwardCoeff F 1 * u ^ 2 *
        exteriorPhi F u) =
        (fun u : ℂ => (3 * exteriorForwardCoeff F 1) *
          ((u ^ 2) * exteriorPhi F u)) := by
      funext u; ring
    rw [heq, actualTaylorSeries_const_mul,
      actualTaylorSeries_mul _ _ (by fun_prop : AnalyticAt ℂ (fun u : ℂ => u ^ 2) 0) hphi,
      actualTaylorSeries_monomial, exteriorPhi_actualTaylorSeries F hc]
    simp only [mul_assoc]
  rw [hwhole, hfirst, actualTaylorSeries_pow _ hphi,
    exteriorPhi_actualTaylorSeries F hc,
    hm, actualTaylorSeries_const_mul, actualTaylorSeries_monomial]

/-- The first three actual negative boundary modes of the second Faber
polynomial, read from derivatives of its analytic reciprocal factor. -/
theorem secondFaberFactor_actual_first_three_negative_modes
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff
      (fun u : ℂ => (exteriorPhi F u) ^ 2 -
        2 * exteriorForwardCoeff F 1 * u ^ 2) 3 =
        2 * exteriorForwardCoeff F 2 ∧
    actualTaylorCoeff
      (fun u : ℂ => (exteriorPhi F u) ^ 2 -
        2 * exteriorForwardCoeff F 1 * u ^ 2) 4 =
        2 * exteriorForwardCoeff F 3 + (exteriorForwardCoeff F 1) ^ 2 ∧
    actualTaylorCoeff
      (fun u : ℂ => (exteriorPhi F u) ^ 2 -
        2 * exteriorForwardCoeff F 1 * u ^ 2) 5 =
        2 * exteriorForwardCoeff F 4 +
          2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 := by
  let φ := formalExteriorPhi (exteriorFormalForward F)
  have hs := secondFaberFactor_actualTaylorSeries F hc
  rcases formalFaberTwo_first_three_negative_modes F with ⟨h3, h4, h5⟩
  have heq (m : ℕ) (hm : 3 ≤ m) :
      actualTaylorCoeff
        (fun u : ℂ => (exteriorPhi F u) ^ 2 -
          2 * exteriorForwardCoeff F 1 * u ^ 2) m =
        PowerSeries.coeff m (φ ^ 2) := by
    rw [← actualTaylorSeries_coeff, hs]
    simp only [map_sub, PowerSeries.coeff_C_mul]
    have hzero : PowerSeries.coeff m (PowerSeries.X ^ 2 : PowerSeries ℂ) = 0 := by
      rw [PowerSeries.coeff_X_pow]
      simp [Nat.ne_of_gt (lt_of_lt_of_le (by omega : 2 < 3) hm)]
    simp [hzero, φ]
  constructor
  · simpa only [heq 3 (by omega)] using h3
  constructor
  · simpa only [heq 4 (by omega)] using h4
  · simpa only [heq 5 (by omega)] using h5

/-- The three actual negative modes of the third Faber polynomial are the
three verified formal modes, with the leading polynomial corrections
removed. -/
theorem thirdFaberFactor_actual_first_three_negative_modes
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi F u) ^ 3 -
        3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
        3 * exteriorForwardCoeff F 2 * u ^ 3
    actualTaylorCoeff A 4 = 3 * exteriorForwardCoeff F 3 ∧
    actualTaylorCoeff A 5 =
      3 * (exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2) ∧
    actualTaylorCoeff A 6 =
      3 * (exteriorForwardCoeff F 5 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
        (exteriorForwardCoeff F 2) ^ 2) +
        (exteriorForwardCoeff F 1) ^ 3 := by
  let φ := formalExteriorPhi (exteriorFormalForward F)
  let A : ℂ → ℂ := fun u =>
    (exteriorPhi F u) ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3
  have hs := thirdFaberFactor_actualTaylorSeries F hc
  rcases formalFaberThree_first_three_negative_modes F with ⟨h4, h5, h6⟩
  have heq (k : ℕ) (hk : 2 ≤ k) :
      actualTaylorCoeff A (k + 2) =
        PowerSeries.coeff (k + 2) (φ ^ 3) -
          3 * exteriorForwardCoeff F 1 * PowerSeries.coeff k φ := by
    change actualTaylorCoeff
      (fun u : ℂ => (exteriorPhi F u) ^ 3 -
        3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
        3 * exteriorForwardCoeff F 2 * u ^ 3) (k + 2) = _
    rw [← actualTaylorSeries_coeff, hs]
    simp only [map_sub]
    have hmiddle : PowerSeries.coeff (k + 2)
        (PowerSeries.C (3 * exteriorForwardCoeff F 1) *
          PowerSeries.X ^ 2 * φ) =
        3 * exteriorForwardCoeff F 1 * PowerSeries.coeff k φ := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      rw [PowerSeries.coeff_X_pow_mul φ 2 k]
    have hlast : PowerSeries.coeff (k + 2)
        (PowerSeries.C (3 * exteriorForwardCoeff F 2) *
          PowerSeries.X ^ 3) = 0 := by
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      simp [show k + 2 ≠ 3 by omega]
    rw [hmiddle, hlast]
    ring
  dsimp [A] at heq ⊢
  constructor
  · simpa only [heq 2 (by omega)] using h4
  constructor
  · simpa only [heq 3 (by omega)] using h5
  · simpa only [heq 4 (by omega)] using h6

/-- All actual second-Faber boundary coefficients used by the finite
Grunsky matrix are exactly its verified logarithmic-kernel row. -/
theorem secondFaberFactor_actual_modes_eq_logKernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi F u) ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2
    let Q := schoberKernelQ3
      (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
      (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
      (exteriorForwardCoeff F 5)
    actualTaylorCoeff A 3 = 2 * schoberBiCoeff 2 1 Q ∧
    actualTaylorCoeff A 4 = 2 * schoberBiCoeff 2 2 Q ∧
    actualTaylorCoeff A 5 = 2 * schoberBiCoeff 2 3 Q := by
  rcases secondFaberFactor_actual_first_three_negative_modes F hc with
    ⟨h3, h4, h5⟩
  dsimp
  constructor
  · rw [h3, schoberKernelQ3_coeff_two_one]
  constructor
  · rw [h4, schoberKernelQ3_coeff_two_two]
    simp [schoberQ22]
    ring
  · rw [h5, schoberKernelQ3_coeff_two_three]
    ring

/-- The third actual Faber boundary factor supplies the third logarithmic
kernel row, without a formal-to-actual coefficient assumption. -/
theorem thirdFaberFactor_actual_modes_eq_logKernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi F u) ^ 3 -
        3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
        3 * exteriorForwardCoeff F 2 * u ^ 3
    let Q := schoberKernelQ3
      (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
      (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
      (exteriorForwardCoeff F 5)
    actualTaylorCoeff A 4 = 3 * schoberBiCoeff 3 1 Q ∧
    actualTaylorCoeff A 5 = 3 * schoberBiCoeff 3 2 Q ∧
    actualTaylorCoeff A 6 = 3 * schoberBiCoeff 3 3 Q := by
  rcases thirdFaberFactor_actual_first_three_negative_modes F hc with
    ⟨h4, h5, h6⟩
  dsimp
  constructor
  · rw [h4, schoberKernelQ3_coeff_three_one]
  constructor
  · rw [h5, schoberKernelQ3_coeff_three_two]
  · rw [h6, schoberKernelQ3_coeff_three_three]
    simp [schoberQ33]
    ring

/-- Centering removes the linear reciprocal term from the actual forward
factor. The next two coefficients are the actual `b₁,b₂`. -/
theorem exteriorPhi_actual_low_coefficients
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (exteriorPhi F) 0 = 1 ∧
    actualTaylorCoeff (exteriorPhi F) 1 = 0 ∧
    actualTaylorCoeff (exteriorPhi F) 2 = exteriorForwardCoeff F 1 ∧
    actualTaylorCoeff (exteriorPhi F) 3 = exteriorForwardCoeff F 2 := by
  constructor
  · exact actualTaylorCoeff_exteriorPhi_zero F
  constructor
  · simpa only [exteriorForwardCoeff_zero] using
      actualTaylorCoeff_exteriorPhi_succ F hc 0
  constructor
  · simpa only [Nat.reduceAdd] using
      actualTaylorCoeff_exteriorPhi_succ F hc 1
  · simpa only [Nat.reduceAdd] using
      actualTaylorCoeff_exteriorPhi_succ F hc 2

/-- The second Faber polynomial has only its leading positive Fourier mode;
its two intervening Taylor coefficients cancel exactly. -/
theorem secondFaberFactor_actual_low_coefficients
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi F u) ^ 2 -
        2 * exteriorForwardCoeff F 1 * u ^ 2
    actualTaylorCoeff A 0 = 1 ∧
    actualTaylorCoeff A 1 = 0 ∧
    actualTaylorCoeff A 2 = 0 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let φ := formalExteriorPhi f
  let A : ℂ → ℂ := fun u =>
    (exteriorPhi F u) ^ 2 -
      2 * exteriorForwardCoeff F 1 * u ^ 2
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hphi : φ = 1 + PowerSeries.X ^ 2 * g := by
    change formalExteriorPhi f = _
    rw [formalExteriorPhi, hf]
    ring
  have hg0 : PowerSeries.coeff 0 g = exteriorForwardCoeff F 1 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 1
  have hg0' : PowerSeries.constantCoeff g = exteriorForwardCoeff F 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hg0
  have htwo : PowerSeries.constantCoeff (2 : PowerSeries ℂ) = 2 := by
    calc
      PowerSeries.constantCoeff (2 : PowerSeries ℂ) =
          PowerSeries.constantCoeff ((1 : PowerSeries ℂ) + 1) := by norm_num
      _ = 2 := by rw [map_add, map_one]; norm_num
  have hA : φ ^ 2 -
      PowerSeries.C (2 * exteriorForwardCoeff F 1) * PowerSeries.X ^ 2 =
        1 + PowerSeries.X ^ 2 *
          (2 * g - PowerSeries.C (2 * exteriorForwardCoeff F 1)) +
          PowerSeries.X ^ 4 * g ^ 2 := by
    rw [hphi]
    ring
  have hseries := secondFaberFactor_actualTaylorSeries F hc
  dsimp [A]
  constructor
  · rw [← actualTaylorSeries_coeff, hseries]
    change PowerSeries.coeff 0 (φ ^ 2 -
      PowerSeries.C (2 * exteriorForwardCoeff F 1) * PowerSeries.X ^ 2) = 1
    rw [hA]
    simp [PowerSeries.coeff_X_pow_mul']
  constructor
  · rw [← actualTaylorSeries_coeff, hseries]
    change PowerSeries.coeff 1 (φ ^ 2 -
      PowerSeries.C (2 * exteriorForwardCoeff F 1) * PowerSeries.X ^ 2) = 0
    rw [hA]
    simp [PowerSeries.coeff_X_pow_mul']
  · rw [← actualTaylorSeries_coeff, hseries]
    change PowerSeries.coeff 2 (φ ^ 2 -
      PowerSeries.C (2 * exteriorForwardCoeff F 1) * PowerSeries.X ^ 2) = 0
    rw [hA]
    have hshift := PowerSeries.coeff_X_pow_mul
      (2 * g - PowerSeries.C (2 * exteriorForwardCoeff F 1)) 2 0
    have hhigh := PowerSeries.coeff_X_pow_mul' (g ^ 2) 4 2
    simp only [map_add, hshift, hhigh]
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hg0', htwo]

/-- All three intermediate nonnegative Fourier modes cancel from the
third actual Faber polynomial. -/
theorem thirdFaberFactor_actual_low_coefficients
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi F u) ^ 3 -
        3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
        3 * exteriorForwardCoeff F 2 * u ^ 3
    actualTaylorCoeff A 0 = 1 ∧
    actualTaylorCoeff A 1 = 0 ∧
    actualTaylorCoeff A 2 = 0 ∧
    actualTaylorCoeff A 3 = 0 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let φ := formalExteriorPhi f
  let b1 := exteriorForwardCoeff F 1
  let b2 := exteriorForwardCoeff F 2
  let A : ℂ → ℂ := fun u =>
    (exteriorPhi F u) ^ 3 - 3 * b1 * u ^ 2 * exteriorPhi F u - 3 * b2 * u ^ 3
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hphi : φ = 1 + PowerSeries.X ^ 2 * g := by
    change formalExteriorPhi f = _
    rw [formalExteriorPhi, hf]
    ring
  have hg0 : PowerSeries.coeff 0 g = b1 := by
    simpa [g, f, b1, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 1
  have hg1 : PowerSeries.coeff 1 g = b2 := by
    simpa [g, f, b2, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 2
  have hg0' : PowerSeries.constantCoeff g = b1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hg0
  have hA : φ ^ 3 - PowerSeries.C (3 * b1) * PowerSeries.X ^ 2 * φ -
      PowerSeries.C (3 * b2) * PowerSeries.X ^ 3 =
      1 + PowerSeries.X ^ 2 * (g + g + g - PowerSeries.C (3 * b1)) -
      PowerSeries.C (3 * b2) * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 4 *
        (g ^ 2 + g ^ 2 + g ^ 2 - PowerSeries.C (3 * b1) * g) +
      PowerSeries.X ^ 6 * g ^ 3 := by
    rw [hphi]
    ring
  have hseries := thirdFaberFactor_actualTaylorSeries F hc
  have hreplace (m : ℕ) : actualTaylorCoeff A m =
      PowerSeries.coeff m
        (φ ^ 3 - PowerSeries.C (3 * b1) * PowerSeries.X ^ 2 * φ -
          PowerSeries.C (3 * b2) * PowerSeries.X ^ 3) := by
    change actualTaylorCoeff
      (fun u : ℂ => (exteriorPhi F u) ^ 3 -
        3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
        3 * exteriorForwardCoeff F 2 * u ^ 3) m = _
    rw [← actualTaylorSeries_coeff, hseries]
  dsimp [A]
  constructor
  · rw [hreplace 0, hA]
    simp [PowerSeries.coeff_X_pow_mul']
  constructor
  · rw [hreplace 1, hA]
    have hlast : PowerSeries.coeff 1
        (PowerSeries.C (3 * b2) * PowerSeries.X ^ 3) = 0 := by
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      simp
    simp only [map_add, map_sub]
    rw [hlast]
    simp [PowerSeries.coeff_X_pow_mul']
  constructor
  · rw [hreplace 2, hA]
    have hlast : PowerSeries.coeff 2
        (PowerSeries.C (3 * b2) * PowerSeries.X ^ 3) = 0 := by
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      simp
    simp only [map_add, map_sub]
    rw [hlast]
    simp [PowerSeries.coeff_X_pow_mul', hg0', b1]
    ring
  · rw [hreplace 3, hA]
    have hlast : PowerSeries.coeff 3
        (PowerSeries.C (3 * b2) * PowerSeries.X ^ 3) = 3 * b2 := by
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      simp
    simp only [map_add, map_sub]
    rw [hlast]
    simp [PowerSeries.coeff_X_pow_mul', hg1, b2]
    ring

end SpringerLean
