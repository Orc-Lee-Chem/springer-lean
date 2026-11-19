import SpringerLean.Round1687ActualMultiplierRegularSet

namespace SpringerLean

/-- The vertical coordinate line in the complex plane has derivative `I`. -/
theorem complexMk_second_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.mk x v) Complex.I y := by
  have hEq : (fun v : ℝ => Complex.mk x v) =
      (fun v : ℝ => (x : ℂ) + v • Complex.I) := by
    funext v
    apply Complex.ext <;> simp
  rw [hEq]
  simpa using ((hasDerivAt_id y).smul_const Complex.I).const_add (x : ℂ)

/-- A vertical real slice differentiates by applying the real fderiv
to the imaginary unit direction. -/
theorem deriv_comp_complexMk_second
    (f : ℂ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ f (Complex.mk x y)) :
    deriv (fun v : ℝ => f (Complex.mk x v)) y =
      (fderiv ℝ f (Complex.mk x y)) Complex.I := by
  have hpath := complexMk_second_hasDerivAt x y
  have h := (hf.hasFDerivAt.comp y hpath.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using h

/-- The actual physical multiplier time has the expected vertical
slice derivative throughout the regular source region. -/
theorem actualHarmonicMultiplierTime_vertical_deriv
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (x y : ℝ)
    (hz : Complex.mk x y ∈ actualMultiplierRegularSet F) :
    deriv (fun v : ℝ => actualHarmonicMultiplierTime F k (Complex.mk x v)) y =
      (fderiv ℝ (actualHarmonicMultiplierTime F k) (Complex.mk x y)) Complex.I := by
  obtain ⟨hball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F (Complex.mk x y)).mp hz
  exact deriv_comp_complexMk_second
    (actualHarmonicMultiplierTime F k) x y
    (actualHarmonicMultiplierTime_differentiableAt F hc k hball hz0 hH)

theorem actualHarmonicMultiplierTime_vertical_differentiableAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (x y : ℝ)
    (hz : Complex.mk x y ∈ actualMultiplierRegularSet F) :
    DifferentiableAt ℝ
      (fun v : ℝ => actualHarmonicMultiplierTime F k (Complex.mk x v)) y := by
  obtain ⟨hball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F (Complex.mk x y)).mp hz
  exact (actualHarmonicMultiplierTime_differentiableAt F hc k hball hz0 hH).comp
    y (complexMk_second_hasDerivAt x y).differentiableAt

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplierTime_vertical_deriv
#print axioms SpringerLean.actualHarmonicMultiplierTime_vertical_differentiableAt
