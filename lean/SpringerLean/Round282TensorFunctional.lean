import SpringerLean.Round271GenericTensorPowers

namespace SpringerLean

def finiteKernelTensorDegree (N : ℕ) :
    (d : ℕ) → finiteKernelTensorIndex N d → ℕ
  | 0 => fun _ => 0
  | d + 1 => fun p => finiteKernelTensorDegree N d p.1 + (p.2.val + 1)

noncomputable def finiteKernelTensorRootWeight (N : ℕ) :
    (d : ℕ) → finiteKernelTensorIndex N d → ℝ
  | 0 => fun _ => 1
  | d + 1 => fun p => finiteKernelTensorRootWeight N d p.1 *
      Real.sqrt ((p.2.val + 1 : ℕ) : ℝ)

theorem finiteKernelTensorRootWeight_pos (N d : ℕ)
    (p : finiteKernelTensorIndex N d) : 0 < finiteKernelTensorRootWeight N d p := by
  induction d with
  | zero => exact zero_lt_one
  | succ d ih =>
      exact mul_pos (ih p.1) (Real.sqrt_pos.2 (by positivity))

noncomputable def exteriorGeneralUnweightedKernel
    (F : ℂ → ℂ) (N : ℕ) (j i : Fin N) : ℂ :=
  PowerSeries.coeff (j.val + 1)
    (PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F))

theorem exteriorGeneralGrunskyTensor_normalization
    (F : ℂ → ℂ) (N d : ℕ) (p q : finiteKernelTensorIndex N d) :
    finiteKernelTensorPower N (exteriorGeneralGrunskyMatrix F N) d p q =
      (finiteKernelTensorRootWeight N d p : ℂ) *
        (finiteKernelTensorRootWeight N d q : ℂ) *
          finiteKernelTensorPower N (exteriorGeneralUnweightedKernel F N) d p q := by
  induction d with
  | zero => simp [finiteKernelTensorPower, finiteKernelTensorRootWeight]
  | succ d ih =>
      simp only [finiteKernelTensorPower, finiteKernelTensorRootWeight, ih,
        exteriorGeneralGrunskyMatrix, exteriorGeneralUnweightedKernel,
        Complex.ofReal_mul]
      ring

/-- The actual finite Grunsky contractions control every tensor degree
of a coefficient functional. All normalizing square roots cancel with
proved nonzero denominators, including the complex bilinear convention. -/
theorem exteriorGeneralGrunskyTensor_functional_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N d : ℕ) (L : ℕ → ℂ) :
    ‖∑ p : finiteKernelTensorIndex N d, L (finiteKernelTensorDegree N d p) *
      (∑ q : finiteKernelTensorIndex N d,
        finiteKernelTensorPower N (exteriorGeneralUnweightedKernel F N) d p q *
          L (finiteKernelTensorDegree N d q))‖ ≤
      ∑ p : finiteKernelTensorIndex N d,
        ‖L (finiteKernelTensorDegree N d p)‖ ^ 2 /
          finiteKernelTensorRootWeight N d p ^ 2 := by
  classical
  let v : finiteKernelTensorIndex N d → ℂ := fun p =>
    L (finiteKernelTensorDegree N d p) / (finiteKernelTensorRootWeight N d p : ℂ)
  have h := exteriorGeneralGrunskyTensor_bilinear_bound F hc N d v
  have heq :
      (∑ p : finiteKernelTensorIndex N d, v p *
        (∑ q : finiteKernelTensorIndex N d,
          finiteKernelTensorPower N (exteriorGeneralGrunskyMatrix F N) d p q * v q)) =
      ∑ p : finiteKernelTensorIndex N d, L (finiteKernelTensorDegree N d p) *
        (∑ q : finiteKernelTensorIndex N d,
          finiteKernelTensorPower N (exteriorGeneralUnweightedKernel F N) d p q *
            L (finiteKernelTensorDegree N d q)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    have hp0 : (finiteKernelTensorRootWeight N d p : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (finiteKernelTensorRootWeight_pos N d p)
    have hq0 : (finiteKernelTensorRootWeight N d q : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (finiteKernelTensorRootWeight_pos N d q)
    rw [exteriorGeneralGrunskyTensor_normalization]
    dsimp only [v]
    field_simp
  rw [heq] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro p hp
  simp [v, norm_div, Complex.norm_real,
    abs_of_pos (finiteKernelTensorRootWeight_pos N d p), div_pow]

end SpringerLean
