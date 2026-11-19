import SpringerLean.Round265AllFiniteGrunsky
import SpringerLean.Round67TensorContraction

namespace SpringerLean

/-- Ordered tensor indices, without committing to a separately handwritten
tuple type at each Schober order. -/
def finiteKernelTensorIndex (N : ℕ) : ℕ → Type
  | 0 => PUnit
  | d + 1 => finiteKernelTensorIndex N d × Fin N

instance finiteKernelTensorIndex_fintype (N d : ℕ) : Fintype (finiteKernelTensorIndex N d) := by
  induction d with
  | zero => change Fintype PUnit; infer_instance
  | succ d ih =>
      letI := ih
      change Fintype (finiteKernelTensorIndex N d × Fin N)
      infer_instance

instance finiteKernelTensorIndex_decidableEq (N d : ℕ) :
    DecidableEq (finiteKernelTensorIndex N d) := by
  induction d with
  | zero => change DecidableEq PUnit; infer_instance
  | succ d ih =>
      letI := ih
      change DecidableEq (finiteKernelTensorIndex N d × Fin N)
      infer_instance

noncomputable def finiteKernelTensorPower (N : ℕ) (C : Fin N → Fin N → ℂ) :
    (d : ℕ) → finiteKernelTensorIndex N d → finiteKernelTensorIndex N d → ℂ
  | 0 => fun _ _ => 1
  | d + 1 => fun p q =>
      finiteKernelTensorPower N C d p.1 q.1 * C p.2 q.2

theorem finiteKernelTensorPower_contraction
    (N : ℕ) (C : Fin N → Fin N → ℂ)
    (hC : ∀ v : Fin N → ℂ,
      (∑ j : Fin N, ‖∑ i : Fin N, C j i * v i‖ ^ 2) ≤
        ∑ i : Fin N, ‖v i‖ ^ 2) (d : ℕ)
    (v : finiteKernelTensorIndex N d → ℂ) :
    (∑ p : finiteKernelTensorIndex N d,
      ‖∑ q : finiteKernelTensorIndex N d,
        finiteKernelTensorPower N C d p q * v q‖ ^ 2) ≤
      ∑ q : finiteKernelTensorIndex N d, ‖v q‖ ^ 2 := by
  classical
  induction d with
  | zero =>
      letI : Unique (finiteKernelTensorIndex N 0) := inferInstanceAs (Unique PUnit)
      simp [finiteKernelTensorPower, Fintype.sum_unique]
  | succ d ih =>
      exact finiteComplexTensor_contraction
        (finiteKernelTensorPower N C d) C (fun w => ih w) hC v

noncomputable def exteriorGeneralGrunskyMatrix
    (F : ℂ → ℂ) (N : ℕ) (j i : Fin N) : ℂ :=
  ((Real.sqrt ((j.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
    ((Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      PowerSeries.coeff (j.val + 1)
        (PowerSeries.coeff (i.val + 1) (exteriorFormalGrunskyKernel F))

theorem exteriorGeneralGrunskyTensor_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N d : ℕ) (v : finiteKernelTensorIndex N d → ℂ) :
    (∑ p : finiteKernelTensorIndex N d,
      ‖∑ q : finiteKernelTensorIndex N d,
        finiteKernelTensorPower N (exteriorGeneralGrunskyMatrix F N) d p q * v q‖ ^ 2) ≤
      ∑ q : finiteKernelTensorIndex N d, ‖v q‖ ^ 2 := by
  exact finiteKernelTensorPower_contraction N (exteriorGeneralGrunskyMatrix F N)
    (fun w => exterior_generalGrunsky_normalized_contraction F hc N w) d v

theorem exteriorGeneralGrunskyTensor_bilinear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N d : ℕ) (v : finiteKernelTensorIndex N d → ℂ) :
    ‖∑ p : finiteKernelTensorIndex N d, v p *
      (∑ q : finiteKernelTensorIndex N d,
        finiteKernelTensorPower N (exteriorGeneralGrunskyMatrix F N) d p q * v q)‖ ≤
      ∑ p : finiteKernelTensorIndex N d, ‖v p‖ ^ 2 := by
  exact finiteComplexBilinear_norm_le_of_l2_contraction
    (finiteKernelTensorPower N (exteriorGeneralGrunskyMatrix F N) d)
    (fun w => exteriorGeneralGrunskyTensor_contraction F hc N d w) v

end SpringerLean
