import SpringerLean.Round282TensorFunctional

namespace SpringerLean

def finiteTensorProduct {R : Type*} [CommMonoid R] (N : ℕ) (t : Fin N → R) :
    (d : ℕ) → finiteKernelTensorIndex N d → R
  | 0 => fun _ => 1
  | d + 1 => fun p => finiteTensorProduct N t d p.1 * t p.2

theorem finite_sum_pow_eq_tensor_sum
    {R : Type*} [CommSemiring R] (N : ℕ) (t : Fin N → R) (d : ℕ) :
    (∑ i : Fin N, t i) ^ d =
      ∑ p : finiteKernelTensorIndex N d, finiteTensorProduct N t d p := by
  classical
  induction d with
  | zero =>
      letI : Unique (finiteKernelTensorIndex N 0) := inferInstanceAs (Unique PUnit)
      simp [finiteTensorProduct]
  | succ d ih =>
      rw [pow_succ, ih, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      change (∑ p : finiteKernelTensorIndex N d, ∑ i : Fin N,
        finiteTensorProduct N t d p * t i) =
          ∑ p : finiteKernelTensorIndex N d × Fin N,
            finiteTensorProduct N t d p.1 * t p.2
      symm
      exact Fintype.sum_prod_type _

theorem finiteKernelTensorDegree_lower_bound (N d : ℕ)
    (p : finiteKernelTensorIndex N d) : d ≤ finiteKernelTensorDegree N d p := by
  induction d with
  | zero => exact Nat.zero_le _
  | succ d ih =>
      change d + 1 ≤ finiteKernelTensorDegree N d p.1 + (p.2.val + 1)
      have h := ih p.1
      omega

theorem finiteKernelTensorRootWeight_sq (N d : ℕ)
    (p : finiteKernelTensorIndex N d) :
    finiteKernelTensorRootWeight N d p ^ 2 =
      finiteTensorProduct N (fun i => ((i.val + 1 : ℕ) : ℝ)) d p := by
  induction d with
  | zero => simp [finiteKernelTensorRootWeight, finiteTensorProduct]
  | succ d ih =>
      simp only [finiteKernelTensorRootWeight, finiteTensorProduct, mul_pow,
        ih, Real.sq_sqrt (show (0 : ℝ) ≤ (p.2.val + 1 : ℕ) by positivity)]

end SpringerLean
