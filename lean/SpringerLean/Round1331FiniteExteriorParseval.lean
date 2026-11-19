import SpringerLean.Round14CircleParseval

open MeasureTheory AddCircle

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- A finite exterior Laurent truncation, with its leading positive
frequency and all inverse modes placed in a single Fourier family. -/
noncomputable def finiteExteriorFourierPartial
    (b : ℕ → ℂ) (r : ℝ) (M : ℕ)
    (θ : AddCircle (2 * Real.pi)) : ℂ :=
  finiteFourierFamily (2 * Real.pi)
    (insert (none : Option ℕ) ((Finset.range M).image some))
    (fun i => match i with
      | none => (1 : ℤ)
      | some j => -(j : ℤ))
    (fun i => match i with
      | none => (r⁻¹ : ℂ)
      | some j => b j * (r : ℂ) ^ j) θ

theorem finiteExteriorFourierPartial_eq
    (b : ℕ → ℂ) (r : ℝ) (M : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    finiteExteriorFourierPartial b r M θ =
      (r⁻¹ : ℂ) * fourier 1 θ +
        ∑ j ∈ Finset.range M,
          (b j * (r : ℂ) ^ j) * fourier (-(j : ℤ)) θ := by
  have hnone : (none : Option ℕ) ∉ ((Finset.range M).image some) := by simp
  unfold finiteExteriorFourierPartial finiteFourierFamily
  rw [Finset.sum_insert hnone]
  rw [Finset.sum_image (by intro i hi j hj hij; simpa using hij)]

/-- Exact finite Parseval for an exterior Laurent truncation.  The
positive mode has energy `r⁻²`; every inverse mode contributes its
coefficient square times `r^(2j)`. -/
theorem finiteExteriorFourierPartial_energy
    (b : ℕ → ℂ) (r : ℝ) (hr : 0 < r) (M : ℕ) :
    (∫ θ : AddCircle (2 * Real.pi),
      ‖finiteExteriorFourierPartial b r M θ‖ ^ 2 ∂haarAddCircle) =
      (r⁻¹) ^ 2 +
        ∑ j ∈ Finset.range M, ‖b j‖ ^ 2 * r ^ (2 * j) := by
  let freq : Option ℕ → ℤ := fun i => match i with
    | none => 1
    | some j => -(j : ℤ)
  have hinj : Function.Injective freq := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some j =>
            dsimp [freq] at hij
            omega
    | some i =>
        cases j with
        | none =>
            dsimp [freq] at hij
            omega
        | some j =>
            dsimp [freq] at hij
            have : i = j := by omega
            simp [this]
  have hnone : (none : Option ℕ) ∉ ((Finset.range M).image some) := by simp
  change (∫ θ : AddCircle (2 * Real.pi),
      ‖finiteFourierFamily (2 * Real.pi)
        (insert (none : Option ℕ) ((Finset.range M).image some))
        freq (fun i => match i with
          | none => (r⁻¹ : ℂ)
          | some j => b j * (r : ℂ) ^ j) θ‖ ^ 2 ∂haarAddCircle) = _
  have hparseval := finiteFourierFamily_energy (2 * Real.pi)
    (insert (none : Option ℕ) ((Finset.range M).image some)) freq
    (fun i => match i with
      | none => (r⁻¹ : ℂ)
      | some j => b j * (r : ℂ) ^ j) hinj
  rw [hparseval, Finset.sum_insert hnone]
  rw [Finset.sum_image (by intro i hi j hj hij; simpa using hij)]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, norm_mul,
    norm_pow]
  congr 1
  · simp [abs_of_pos hr]
  · apply Finset.sum_congr rfl
    intro j hj
    ring

end SpringerLean

#print axioms SpringerLean.finiteExteriorFourierPartial_energy
