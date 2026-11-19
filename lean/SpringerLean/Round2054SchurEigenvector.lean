import SpringerLean.Round2053UnitaryFirstColumn
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

open Matrix

namespace SpringerLean

/-- A first unitary basis change moves a complex eigenvector to the
first coordinate. Every entry below the first diagonal entry vanishes. -/
theorem exists_unitary_first_column_eigenvector (n : ℕ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    ∃ U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
        ∀ i : Fin n, (Uᴴ * A * U) i.succ 0 = 0 := by
  classical
  obtain ⟨eigenvalue, heigenvalue⟩ := Module.End.exists_eigenvalue A.toLin'
  obtain ⟨v, hv⟩ := heigenvalue.exists_hasEigenvector
  let y : EuclideanSpace ℂ (Fin (n+1)) := WithLp.toLp 2 v
  have hy0 : y ≠ 0 := by
    intro hy
    apply hv.2
    exact congrArg (fun y : EuclideanSpace ℂ (Fin (n+1)) => y.ofLp) hy
  let c : ℂ := (‖y‖⁻¹ : ℝ)
  let x : EuclideanSpace ℂ (Fin (n+1)) := c • y
  have hx : ‖x‖ = 1 := by
    rw [norm_smul, show ‖c‖ = ‖y‖⁻¹ by
      simp [c]]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)
  obtain ⟨U, hU₁, hU₂, hxU⟩ := exists_unitary_prescribed_column 0 x hx
  have hvA : A *ᵥ v = eigenvalue • v := hv.apply_eq_smul
  have hxA : A *ᵥ (fun i => x i) = eigenvalue • (fun i => x i) := by
    change A *ᵥ (c • v) = eigenvalue • (c • v)
    rw [mulVec_smul, hvA, smul_comm]
  have hEq : (Uᴴ * A * U) *ᵥ Pi.single 0 1 =
      eigenvalue • Pi.single 0 1 := by
    have hcol : U *ᵥ Pi.single 0 1 = fun i => x i := by
      ext i
      simpa only [mulVec_single_one, Matrix.col_apply] using hxU i
    rw [← mulVec_mulVec, ← mulVec_mulVec, hcol, hxA, mulVec_smul, ← hcol,
      mulVec_mulVec, hU₁, one_mulVec]
  refine ⟨U, hU₁, hU₂, fun i => ?_⟩
  have h := congrFun hEq i.succ
  simpa [mulVec_single_one, Fin.succ_ne_zero] using h

end SpringerLean
