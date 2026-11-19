import SpringerLean.CircleFinite

open MeasureTheory AddCircle

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

private def exteriorCircleFrequency : Option ℕ → ℤ
  | none => 0
  | some j => -((j : ℤ) + 1)

private theorem exteriorCircleFrequency_injective :
    Function.Injective exteriorCircleFrequency := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some j => simp [exteriorCircleFrequency] at h; omega
  | some i =>
      cases y with
      | none => simp [exteriorCircleFrequency] at h; omega
      | some j =>
          have hij : i = j := by
            simp only [exteriorCircleFrequency] at h
            omega
          exact congrArg some hij

private noncomputable def exteriorCircleModeCoeff
    (F : ℂ → ℂ) (ρ : ℝ) : Option ℕ → ℂ
  | none => 1
  | some j => -((j : ℂ) * exteriorForwardCoeff F j *
      ((ρ : ℂ)⁻¹) ^ (j + 1))

private def exteriorCircleModeSet (M : ℕ) : Finset (Option ℕ) :=
  insert none ((Finset.Icc 1 M).image some)

/-- The actual finite derivative Fourier polynomial on a circle of radius ρ. -/
noncomputable def exteriorDerivativePartialCircle
    (F : ℂ → ℂ) (ρ : ℝ) (M : ℕ) (θ : AddCircle (2 * Real.pi)) : ℂ :=
  finiteFourierFamily (2 * Real.pi) (exteriorCircleModeSet M)
    exteriorCircleFrequency (exteriorCircleModeCoeff F ρ) θ

theorem exteriorDerivativePartialCircle_eq
    (F : ℂ → ℂ) (ρ : ℝ) (M : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    exteriorDerivativePartialCircle F ρ M θ =
      1 - ∑ j ∈ Finset.Icc 1 M,
        (j : ℂ) * exteriorForwardCoeff F j *
          ((ρ : ℂ)⁻¹) ^ (j + 1) *
            fourier (-((j : ℤ) + 1)) θ := by
  classical
  have hnone : none ∉ (Finset.Icc 1 M).image some := by simp
  simp [exteriorDerivativePartialCircle, finiteFourierFamily,
    exteriorCircleModeSet, Finset.sum_insert hnone,
    Finset.sum_image, exteriorCircleModeCoeff,
    exteriorCircleFrequency, Finset.sum_neg_distrib,
    sub_eq_add_neg]

/-- The Fourier basis notation is the exponential notation of the paper. -/
theorem exteriorDerivativePartialCircle_coe_eq_exp
    (F : ℂ → ℂ) (ρ : ℝ) (M : ℕ) (θ : ℝ) :
    exteriorDerivativePartialCircle F ρ M
        (θ : AddCircle (2 * Real.pi)) =
      1 - ∑ j ∈ Finset.Icc 1 M,
        (j : ℂ) * exteriorForwardCoeff F j *
          ((ρ : ℂ)⁻¹) ^ (j + 1) *
            Complex.exp (-(j + 1 : ℂ) * Complex.I * (θ : ℂ)) := by
  rw [exteriorDerivativePartialCircle_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [fourier_coe_apply]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  congr 1
  field_simp
  push_cast
  ring

/-- Exact finite square-integral identity on normalized Haar measure. -/
theorem exteriorDerivativePartialCircle_energy
    (F : ℂ → ℂ) (ρ : ℝ) (M : ℕ) :
    (∫ θ : AddCircle (2 * Real.pi),
      ‖exteriorDerivativePartialCircle F ρ M θ‖ ^ 2
      ∂(@haarAddCircle (2 * Real.pi) _)) =
      1 + ∑ j ∈ Finset.Icc 1 M,
        ‖(j : ℂ) * exteriorForwardCoeff F j *
          ((ρ : ℂ)⁻¹) ^ (j + 1)‖ ^ 2 := by
  classical
  have h := finiteFourierFamily_energy (2 * Real.pi)
    (exteriorCircleModeSet M) exteriorCircleFrequency
    (exteriorCircleModeCoeff F ρ) exteriorCircleFrequency_injective
  have hnone : none ∉ (Finset.Icc 1 M).image some := by simp
  simpa [exteriorDerivativePartialCircle, exteriorCircleModeSet,
    Finset.sum_insert hnone, Finset.sum_image,
    exteriorCircleModeCoeff] using h

/-- The explicit finite circle square sum with the paper's coefficient and
frequency indexing. The first negative frequency is `-2` when `j=1`. -/
theorem exteriorDerivativePartialCircle_energy_formula
    (F : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (M : ℕ) :
    (∫ θ : AddCircle (2 * Real.pi),
      ‖exteriorDerivativePartialCircle F ρ M θ‖ ^ 2
      ∂(@haarAddCircle (2 * Real.pi) _)) =
      1 + ∑ j ∈ Finset.Icc 1 M,
        (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
          (ρ⁻¹) ^ (2 * j + 2) := by
  rw [exteriorDerivativePartialCircle_energy]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [norm_mul, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  simp only [Complex.norm_natCast]
  rw [show 2 * j + 2 = (j + 1) * 2 by omega, pow_mul]
  ring

/-- The same exact identity in the paper's angular interval notation. -/
theorem exteriorDerivativePartialCircle_interval_energy
    (F : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (M : ℕ) :
    (1 / (2 * Real.pi)) *
      (∫ θ in -Real.pi..Real.pi,
        ‖exteriorDerivativePartialCircle F ρ M
          (θ : AddCircle (2 * Real.pi))‖ ^ 2) =
      1 + ∑ j ∈ Finset.Icc 1 M,
        (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
          (ρ⁻¹) ^ (2 * j + 2) := by
  let g : AddCircle (2 * Real.pi) → ℝ :=
    fun θ => ‖exteriorDerivativePartialCircle F ρ M θ‖ ^ 2
  have hinterval :
      (∫ θ in -Real.pi..Real.pi,
        g (θ : AddCircle (2 * Real.pi))) =
      ∫ θ : AddCircle (2 * Real.pi), g θ := by
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using
      (AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi) g)
  have hhaar :
      (∫ θ : AddCircle (2 * Real.pi),
        g θ ∂(@haarAddCircle (2 * Real.pi) _)) =
      (2 * Real.pi)⁻¹ *
        (∫ θ : AddCircle (2 * Real.pi), g θ) := by
    simpa only [smul_eq_mul] using
      (AddCircle.integral_haarAddCircle (T := 2 * Real.pi) (f := g))
  calc
    (1 / (2 * Real.pi)) *
      (∫ θ in -Real.pi..Real.pi,
        ‖exteriorDerivativePartialCircle F ρ M
          (θ : AddCircle (2 * Real.pi))‖ ^ 2) =
      (∫ θ : AddCircle (2 * Real.pi),
        ‖exteriorDerivativePartialCircle F ρ M θ‖ ^ 2
        ∂(@haarAddCircle (2 * Real.pi) _)) := by
          change (1 / (2 * Real.pi)) *
            (∫ θ in -Real.pi..Real.pi,
              g (θ : AddCircle (2 * Real.pi))) = _
          rw [hinterval, hhaar]
          ring
    _ = _ := exteriorDerivativePartialCircle_energy_formula F hρ M

end SpringerLean
