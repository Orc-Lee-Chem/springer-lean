import SpringerLean.Coefficients


open scoped Topology

namespace SpringerLean

/-- Correction of an actual exterior map in the coordinate t=1/z. -/
noncomputable def exteriorForwardGerm (F : ℂ → ℂ) (t : ℂ) : ℂ :=
  if t = 0 then 0 else F t⁻¹ - t⁻¹

/-- The inverse is selected from the actual exterior map. -/
noncomputable def exteriorInverse (F : ℂ → ℂ) : ℂ → ℂ :=
  Function.invFunOn F exteriorDisk

/-- Correction of the actual inverse in the coordinate t=1/w. -/
noncomputable def exteriorInverseGerm (F : ℂ → ℂ) (t : ℂ) : ℂ :=
  if t = 0 then 0 else t⁻¹ - exteriorInverse F t⁻¹

/-- Independently read a Laurent coefficient from the actual forward germ. -/
noncomputable def exteriorForwardCoeff (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (exteriorForwardGerm F) 0 / (n.factorial : ℂ)

/-- Independently read a Laurent coefficient from the actual inverse germ. -/
noncomputable def exteriorInverseCoeff (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (exteriorInverseGerm F) 0 / (n.factorial : ℂ)

private theorem first_deriv_of_correction_identity (f g : ℂ → ℂ)
    (hg0 : g 0 = 0) (hf : DifferentiableAt ℂ f 0)
    (hg : DifferentiableAt ℂ g 0)
    (hid : g =ᶠ[𝓝 0] (fun t => f (t / (1 - t * g t)))) :
    deriv g 0 = deriv f 0 := by
  have hmul : HasDerivAt (fun t : ℂ => t * g t) 0 0 := by
    convert (hasDerivAt_id (0 : ℂ)).mul hg.hasDerivAt using 1
    · funext t; rfl
    · simp [hg0]
  have hden : HasDerivAt (fun t : ℂ => 1 - t * g t) 0 0 := by
    convert (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub hmul using 1
    simp
  have hp : HasDerivAt (fun t : ℂ => t / (1 - t * g t)) 1 0 := by
    convert (hasDerivAt_id (0 : ℂ)).div hden (by simp) using 1
    · funext t; rfl
    · simp
  have hcomp : HasDerivAt (fun t : ℂ => f (t / (1 - t * g t))) (deriv f 0) 0 := by
    have hf' : HasDerivAt f (deriv f 0) (0 / (1 - 0 * g 0)) := by simpa using hf.hasDerivAt
    simpa only [Function.comp_def, mul_one] using hf'.comp (0 : ℂ) hp
  exact (hcomp.congr_of_eventuallyEq hid).deriv

/-- Conditional first-coefficient identity for the same actual exterior map and its inverse.
The forward/inverse differentiability and image-coverage inputs are explicit in the type. -/
theorem exteriorInverseCoeff_one_eq_forwardCoeff_one_of_local
    (F : ℂ → ℂ)
    (hf : DifferentiableAt ℂ (exteriorForwardGerm F) 0)
    (hg : DifferentiableAt ℂ (exteriorInverseGerm F) 0)
    (hcover : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → t⁻¹ ∈ F '' exteriorDisk) :
    exteriorInverseCoeff F 1 = exteriorForwardCoeff F 1 := by
  let f := exteriorForwardGerm F
  let g := exteriorInverseGerm F
  have hg0 : g 0 = 0 := by simp [g, exteriorInverseGerm]
  have hdencont : ContinuousAt (fun t : ℂ => 1 - t * g t) 0 := by
    exact continuousAt_const.sub (continuousAt_id.mul hg.continuousAt)
  have hden : ∀ᶠ t in 𝓝 (0 : ℂ), 1 - t * g t ≠ 0 :=
    hdencont.eventually_ne (by simp)
  have hloc : g =ᶠ[𝓝 (0 : ℂ)] (fun t => f (t / (1 - t * g t))) := by
    filter_upwards [hden, hcover] with t hd hi
    by_cases ht : t = 0
    · subst t
      simp [f, g, exteriorForwardGerm, exteriorInverseGerm]
    · have hgt : g t = t⁻¹ - exteriorInverse F t⁻¹ := by
        simp [g, exteriorInverseGerm, ht]
      have hpne : t / (1 - t * g t) ≠ 0 := div_ne_zero ht hd
      have hpinv : (t / (1 - t * g t))⁻¹ = exteriorInverse F t⁻¹ := by
        calc
          (t / (1 - t * g t))⁻¹ = t⁻¹ - g t := by
            field_simp [ht, hd]
          _ = exteriorInverse F t⁻¹ := by rw [hgt]; ring
      have hF : F (exteriorInverse F t⁻¹) = t⁻¹ := by
        simpa only [exteriorInverse] using (Function.invFunOn_eq (hi ht))
      have hft : f (t / (1 - t * g t)) =
          F ((t / (1 - t * g t))⁻¹) - (t / (1 - t * g t))⁻¹ := by
        simp [f, exteriorForwardGerm, hpne]
      rw [hft, hpinv, hF]
      exact hgt
  have hder := first_deriv_of_correction_identity f g hg0 hf hg hloc
  simpa only [exteriorInverseCoeff, exteriorForwardCoeff, iteratedDeriv_one,
    Nat.factorial_one, Nat.cast_one, div_one] using hder
end SpringerLean