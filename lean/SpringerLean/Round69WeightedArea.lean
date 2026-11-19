import SpringerLean.Round68TensorTerms

namespace SpringerLean

/-- Finite weighted Cauchy–Schwarz for complex coefficients. -/
theorem finiteComplexWeightedSum_sq_le
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2 / w i) *
        (∑ i ∈ s, w i * ‖b i‖ ^ 2) := by
  let x : ι → ℝ := fun i => ‖a i‖ / Real.sqrt (w i)
  let y : ι → ℝ := fun i => Real.sqrt (w i) * ‖b i‖
  have hxy (i : ι) (hi : i ∈ s) :
      x i * y i = ‖a i‖ * ‖b i‖ := by
    have hs : Real.sqrt (w i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hw i hi))
    dsimp [x, y]
    field_simp
  have hx (i : ι) (hi : i ∈ s) :
      x i ^ 2 = ‖a i‖ ^ 2 / w i := by
    have hs := Real.sq_sqrt (le_of_lt (hw i hi))
    dsimp [x]
    rw [div_pow, hs]
  have hy (i : ι) (hi : i ∈ s) :
      y i ^ 2 = w i * ‖b i‖ ^ 2 := by
    have hs := Real.sq_sqrt (le_of_lt (hw i hi))
    dsimp [y]
    rw [mul_pow, hs]
  have hsum : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, x i * y i := by
    calc
      _ ≤ ∑ i ∈ s, ‖a i * b i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, x i * y i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_mul, hxy i hi]
  have hsum0 : 0 ≤ ∑ i ∈ s, x i * y i := by
    apply Finset.sum_nonneg
    intro i hi
    dsimp [x, y]
    positivity
  have hsquared : ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, x i * y i) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsum0).2 hsum
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s x y
  calc
    _ ≤ (∑ i ∈ s, x i * y i) ^ 2 := hsquared
    _ ≤ (∑ i ∈ s, x i ^ 2) * (∑ i ∈ s, y i ^ 2) := hcs
    _ = _ := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
      · exact hx i hi
      · exact hy i hi


/-- The finite exterior area theorem with the first mode removed. -/
theorem exteriorForwardCoeff_finite_area_tail
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.Icc 2 N,
      (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) ≤
      1 - ‖exteriorForwardCoeff F 1‖ ^ 2 := by
  have hs : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1not : 1 ∉ Finset.Icc 2 N := by simp
  have h := exteriorForwardCoeff_finite_area F hc N
  rw [hs, Finset.sum_insert h1not] at h
  norm_num at h
  linarith

/-- Schober's finite weighted estimate (7) for the actual forward
coefficients of one centered exterior univalent map. The weights may depend
on the map; this theorem quantifies them after fixing `F`. -/
theorem exteriorForwardCoeff_weighted_linear_combination_sq_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (hN : 1 ≤ N) (lambda : ℕ → ℂ) :
    ‖∑ j ∈ Finset.Icc 2 N, lambda j * exteriorForwardCoeff F j‖ ^ 2 ≤
      (∑ j ∈ Finset.Icc 2 N, ‖lambda j‖ ^ 2 / (j : ℝ)) *
        (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  let S := Finset.Icc 2 N
  have hw : ∀ j ∈ S, (0 : ℝ) < j := by
    intro j hj
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    exact_mod_cast (by omega : 0 < j)
  have hcs := finiteComplexWeightedSum_sq_le S (fun j : ℕ => (j : ℝ))
    hw lambda (exteriorForwardCoeff F)
  have hA : 0 ≤ (∑ j ∈ S, ‖lambda j‖ ^ 2 / (j : ℝ)) := by
    apply Finset.sum_nonneg
    intro j hj
    exact div_nonneg (sq_nonneg _) (le_of_lt (hw j hj))
  have htail := exteriorForwardCoeff_finite_area_tail F hc N hN
  exact hcs.trans (mul_le_mul_of_nonneg_left htail hA)
end SpringerLean