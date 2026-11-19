import SpringerLean.Round248LinearFormalLog

namespace SpringerLean
open PowerSeries

theorem formal_logOf_subst
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (f T : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1)
    (hT : PowerSeries.constantCoeff T = 0) :
    (PowerSeries.logOf f).subst T = PowerSeries.logOf (f.subst T) := by
  have hsF : PowerSeries.HasSubst (f - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hf])
  have hsT : PowerSeries.HasSubst T :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hT
  simp only [PowerSeries.logOf_eq]
  rw [PowerSeries.subst_comp_subst_apply hsF hsT]
  congr 1
  rw [PowerSeries.subst_sub hsT]
  simp only [← PowerSeries.coe_substAlgHom hsT, map_one]

noncomputable def formalNegativeLogSeries
    (A : Type*) [CommRing A] [Algebra ℚ A] : PowerSeries A :=
  -PowerSeries.logOf (1 - PowerSeries.X)

@[simp] theorem formalNegativeLogSeries_constantCoeff
    {A : Type*} [CommRing A] [Algebra ℚ A] :
    PowerSeries.constantCoeff (formalNegativeLogSeries A) = 0 := by
  simp [formalNegativeLogSeries, PowerSeries.constantCoeff_logOf]

theorem formalNegativeLogSeries_coeff_succ
    {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℕ) :
    PowerSeries.coeff (n + 1) (formalNegativeLogSeries A) =
      algebraMap ℚ A (((n + 1 : ℕ) : ℚ)⁻¹) := by
  let r := algebraMap ℚ A (((n + 1 : ℕ) : ℚ)⁻¹)
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hcancel : r * ((n + 1 : ℕ) : A) = 1 := by
    change algebraMap ℚ A (((n + 1 : ℕ) : ℚ)⁻¹) * ((n + 1 : ℕ) : A) = 1
    rw [show ((n + 1 : ℕ) : A) = algebraMap ℚ A ((n + 1 : ℕ) : ℚ) by simp,
      ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hcoeff := formal_linear_log_coeff_succ (1 : A) n
  simp only [map_one, one_pow, one_mul] at hcoeff
  change PowerSeries.coeff (n + 1) (formalNegativeLogSeries A) = r
  calc
    _ = (r * ((n + 1 : ℕ) : A)) *
        PowerSeries.coeff (n + 1) (formalNegativeLogSeries A) := by rw [hcancel]; simp
    _ = r * (((n + 1 : ℕ) : A) *
        PowerSeries.coeff (n + 1) (formalNegativeLogSeries A)) := by ring
    _ = r := by rw [show ((n + 1 : ℕ) : A) *
        PowerSeries.coeff (n + 1) (formalNegativeLogSeries A) = 1 from hcoeff]; simp

theorem formalNegativeLogSeries_map
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (h : A →+* B) :
    PowerSeries.map h (formalNegativeLogSeries A) = formalNegativeLogSeries B := by
  unfold formalNegativeLogSeries
  rw [map_neg, formal_logOf_map h _ (by simp), map_sub, map_one, PowerSeries.map_X]

theorem formalNegativeLogSeries_subst
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (T : PowerSeries A) (hT : PowerSeries.constantCoeff T = 0) :
    (formalNegativeLogSeries A).subst T = -PowerSeries.logOf (1 - T) := by
  have hsT : PowerSeries.HasSubst T :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hT
  unfold formalNegativeLogSeries
  rw [← PowerSeries.coe_substAlgHom hsT, map_neg]
  rw [PowerSeries.coe_substAlgHom]
  rw [formal_logOf_subst _ T (by simp) hT]
  congr 1
  rw [PowerSeries.subst_sub hsT]
  simp only [← PowerSeries.coe_substAlgHom hsT, map_one,
    PowerSeries.substAlgHom_X]

theorem formal_coeff_pow_zero_of_lt
    {A : Type*} [CommRing A] (T : PowerSeries A)
    (hT : PowerSeries.constantCoeff T = 0) (m k : ℕ) (hmk : m < k) :
    PowerSeries.coeff m (T ^ k) = 0 := by
  have hform : T = PowerSeries.X *
      PowerSeries.mk (fun n => PowerSeries.coeff (n + 1) T) := by
    simpa [hT] using PowerSeries.eq_X_mul_shift_add_const T
  rw [hform, mul_pow, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hmk]

theorem formal_coeff_subst_finite
    {A : Type*} [CommRing A]
    (f T : PowerSeries A) (hT : PowerSeries.constantCoeff T = 0) (m : ℕ) :
    PowerSeries.coeff m (f.subst T) =
      ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k f * PowerSeries.coeff m (T ^ k) := by
  have hsT : PowerSeries.HasSubst T :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hT
  rw [PowerSeries.coeff_subst' hsT]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  by_contra hnot
  simp only [Finset.mem_coe, Finset.mem_range] at hnot
  have hmk : m < k := by omega
  have hz := formal_coeff_pow_zero_of_lt T hT m k hmk
  exact hk (by simp [hz])

/-- A finite negative-log coefficient formula valid in any requested
truncation N, with every discarded power proved to have zero coefficient. -/
theorem formal_negative_log_coeff_finite
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (T : PowerSeries A) (hT : PowerSeries.constantCoeff T = 0)
    (m N : ℕ) (hmN : m ≤ N) :
    PowerSeries.coeff m (-PowerSeries.logOf (1 - T)) =
      ∑ k ∈ Finset.range (N + 1),
        PowerSeries.coeff k (formalNegativeLogSeries A) * PowerSeries.coeff m (T ^ k) := by
  have hsT : PowerSeries.HasSubst T :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hT
  rw [← formalNegativeLogSeries_subst T hT,
    PowerSeries.coeff_subst' hsT]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  by_contra hnot
  simp only [Finset.mem_coe, Finset.mem_range] at hnot
  have hmk : m < k := by omega
  have hz := formal_coeff_pow_zero_of_lt T hT m k hmk
  exact hk (by simp [hz])

end SpringerLean
