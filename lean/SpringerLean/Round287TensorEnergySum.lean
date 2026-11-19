import SpringerLean.Round286FiniteLogEnergy

namespace SpringerLean
open PowerSeries

theorem finite_exp_coeff_trunc
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (Q : PowerSeries A) (hQ : PowerSeries.constantCoeff Q = 0)
    (m n : ℕ) (hm : m ≤ n) :
    PowerSeries.coeff m ((PowerSeries.exp A).subst Q) =
      ∑ d ∈ Finset.range (n + 1),
        algebraMap ℚ A (1 / (d.factorial : ℚ)) * PowerSeries.coeff m (Q ^ d) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hQ
  rw [PowerSeries.coeff_subst' hs]
  simp only [PowerSeries.coeff_exp, smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  by_contra hnot
  simp only [Finset.mem_coe, Finset.mem_range] at hnot
  have hmd : m < d := by omega
  exact hd (by simp [formal_coeff_pow_zero_of_lt Q hQ m d hmd])

theorem finiteTensorProduct_log_monomial (N d : ℕ)
    (p : finiteKernelTensorIndex N d) :
    finiteTensorProduct N
      (fun i => PowerSeries.C ((((i.val + 1 : ℕ) : ℝ))⁻¹) *
        PowerSeries.X ^ (i.val + 1)) d p =
      PowerSeries.C ((finiteKernelTensorRootWeight N d p ^ 2)⁻¹) *
        PowerSeries.X ^ finiteKernelTensorDegree N d p := by
  induction d with
  | zero => simp [finiteTensorProduct, finiteKernelTensorRootWeight, finiteKernelTensorDegree]
  | succ d ih =>
      rcases p with ⟨p, i⟩
      change finiteTensorProduct N
          (fun i => PowerSeries.C ((((i.val + 1 : ℕ) : ℝ))⁻¹) *
            PowerSeries.X ^ (i.val + 1)) d p *
          (PowerSeries.C ((((i.val + 1 : ℕ) : ℝ))⁻¹) * PowerSeries.X ^ (i.val + 1)) =
        PowerSeries.C (((finiteKernelTensorRootWeight N d p *
          Real.sqrt ((i.val + 1 : ℕ) : ℝ)) ^ 2)⁻¹) *
            PowerSeries.X ^ (finiteKernelTensorDegree N d p + (i.val + 1))
      rw [ih p]
      simp only [mul_pow,
        Real.sq_sqrt (show (0 : ℝ) ≤ (i.val + 1 : ℕ) by positivity),
        mul_inv_rev, map_mul, pow_add]
      ring

theorem finiteLogTruncation_pow_tensor (N d : ℕ) :
    finiteLogTruncation N ^ d =
      ∑ p : finiteKernelTensorIndex N d,
        PowerSeries.C ((finiteKernelTensorRootWeight N d p ^ 2)⁻¹) *
          PowerSeries.X ^ finiteKernelTensorDegree N d p := by
  rw [finiteLogTruncation, finite_sum_pow_eq_tensor_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact finiteTensorProduct_log_monomial N d p

theorem finiteTensor_energy_as_coefficient_sum
    (N n d : ℕ) (L : ℕ → ℂ) (hL : ∀ m, n < m → L m = 0) :
    (∑ p : finiteKernelTensorIndex N d,
      ‖L (finiteKernelTensorDegree N d p)‖ ^ 2 /
        finiteKernelTensorRootWeight N d p ^ 2) =
      ∑ m ∈ Finset.range (n + 1),
        ‖L m‖ ^ 2 * PowerSeries.coeff m (finiteLogTruncation N ^ d) := by
  classical
  rw [finiteLogTruncation_pow_tensor]
  simp only [map_sum, Finset.mul_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hdeg : finiteKernelTensorDegree N d p ≤ n
  · symm
    rw [Finset.sum_eq_single (finiteKernelTensorDegree N d p)]
    · simp [div_eq_mul_inv]
    · intro m hm hne
      simp [hne]
    · simp [Finset.mem_range, hdeg]
  · rw [hL _ (by omega), norm_zero, zero_pow (by omega), zero_div]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    have hne : m ≠ finiteKernelTensorDegree N d p := by
      have := Finset.mem_range.mp hm
      omega
    simp [hne]

/-- The complete factorial-weighted tensor energy equals the comparison
diagonal. The identity is a finite consequence of exp(-log(1-X))=1/(1-X),
with powers above each requested coefficient proved to vanish. -/
theorem finiteTensor_energy_total
    (N n : ℕ) (hnN : n ≤ N) (L : ℕ → ℂ)
    (hL : ∀ m, n < m → L m = 0) :
    (∑ d ∈ Finset.range (n + 1), (1 / (d.factorial : ℝ)) *
      (∑ p : finiteKernelTensorIndex N d,
        ‖L (finiteKernelTensorDegree N d p)‖ ^ 2 /
          finiteKernelTensorRootWeight N d p ^ 2)) =
      ∑ m ∈ Finset.range (n + 1), ‖L m‖ ^ 2 := by
  classical
  simp_rw [finiteTensor_energy_as_coefficient_sum N n _ L hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by have := Finset.mem_range.mp hm; omega
  have he := finite_exp_coeff_trunc (finiteLogTruncation N)
    (finiteLogTruncation_zero N) m n hmn
  have hcoef := finiteLogTruncation_exp_coeff_low N m (hmn.trans hnN)
  rw [he] at hcoef
  simp only [map_div₀, map_one, map_natCast] at hcoef
  calc
    (∑ d ∈ Finset.range (n + 1),
      1 / (d.factorial : ℝ) * (‖L m‖ ^ 2 * PowerSeries.coeff m (finiteLogTruncation N ^ d))) =
        ‖L m‖ ^ 2 * (∑ d ∈ Finset.range (n + 1),
          1 / (d.factorial : ℝ) * PowerSeries.coeff m (finiteLogTruncation N ^ d)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = ‖L m‖ ^ 2 := by rw [hcoef, mul_one]

end SpringerLean
