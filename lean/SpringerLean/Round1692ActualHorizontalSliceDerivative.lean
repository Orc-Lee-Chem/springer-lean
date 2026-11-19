import SpringerLean.Round1690ComplexCoordinateSliceDerivative

namespace SpringerLean

/-- The horizontal coordinate line in the complex plane has derivative one. -/
theorem complexMk_first_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.mk v y) (1 : ℂ) x := by
  have hEq : (fun v : ℝ => Complex.mk v y) =
      (fun v : ℝ => y • Complex.I + (v : ℂ)) := by
    funext v
    apply Complex.ext <;> simp
  rw [hEq]
  have hReal : HasDerivAt (fun v : ℝ => (v : ℂ)) (1 : ℂ) x := by
    have hcoe : (fun v : ℝ => (v : ℂ)) =
        (Complex.ofRealCLM : ℝ → ℂ) := by
      funext v
      exact (Complex.ofRealCLM_apply v).symm
    rw [hcoe]
    exact Complex.ofRealCLM.hasDerivAt
  simpa using hReal.const_add (y • Complex.I)

theorem deriv_comp_complexMk_first
    (f : ℂ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ f (Complex.mk x y)) :
    deriv (fun v : ℝ => f (Complex.mk v y)) x =
      (fderiv ℝ f (Complex.mk x y)) (1 : ℂ) := by
  have hpath := complexMk_first_hasDerivAt x y
  have h := (hf.hasFDerivAt.comp x hpath.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using h

theorem actualHarmonicMultiplierTime_horizontal_deriv
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (x y : ℝ)
    (hz : Complex.mk x y ∈ actualMultiplierRegularSet F) :
    deriv (fun v : ℝ => actualHarmonicMultiplierTime F k (Complex.mk v y)) x =
      (fderiv ℝ (actualHarmonicMultiplierTime F k) (Complex.mk x y)) (1 : ℂ) := by
  obtain ⟨hball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F (Complex.mk x y)).mp hz
  exact deriv_comp_complexMk_first
    (actualHarmonicMultiplierTime F k) x y
    (actualHarmonicMultiplierTime_differentiableAt F hc k hball hz0 hH)

theorem actualHarmonicMultiplierTime_horizontal_differentiableAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (x y : ℝ)
    (hz : Complex.mk x y ∈ actualMultiplierRegularSet F) :
    DifferentiableAt ℝ
      (fun v : ℝ => actualHarmonicMultiplierTime F k (Complex.mk v y)) x := by
  obtain ⟨hball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F (Complex.mk x y)).mp hz
  exact (actualHarmonicMultiplierTime_differentiableAt F hc k hball hz0 hH).comp
    x (complexMk_first_hasDerivAt x y).differentiableAt

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplierTime_horizontal_deriv
#print axioms SpringerLean.actualHarmonicMultiplierTime_horizontal_differentiableAt
