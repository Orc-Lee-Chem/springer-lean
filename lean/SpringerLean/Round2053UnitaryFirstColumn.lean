import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Polynomial.Basic

open Matrix Set

namespace SpringerLean

/-- Extend a prescribed unit vector to a unitary matrix with that
vector in the indicated column. -/
theorem exists_unitary_prescribed_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) :
    ∃ U : Matrix ι ι ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ ∀ i, U i i₀ = x i := by
  classical
  let s : Set ι := {i₀}
  let a : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι) := EuclideanSpace.basisFun ι ℂ
  have : Subsingleton s := by
    unfold s
    infer_instance
  have hon : Orthonormal ℂ (s.domRestrict fun _ => x) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hx
  obtain ⟨b, hfirst⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    (Module.finrank_eq_card_basis a.toBasis)
  refine ⟨a.toBasis.toMatrix b.toBasis,
    a.toMatrix_orthonormalBasis_conjTranspose_mul_self b,
    a.toMatrix_orthonormalBasis_self_mul_conjTranspose b, ?_⟩
  intro i
  change a.toBasis.repr (b i₀) i = x i
  rw [hfirst i₀ (by simp [s])]
  rfl

/-- Choose the first unit vector with uniform squared modulus, as
needed for the polynomial derivative compression. -/
theorem exists_unitary_uniform_first_column (n : ℕ) :
    ∃ U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
        ∀ i, ‖U i 0‖ ^ 2 = ((n+1 : ℕ) : ℝ)⁻¹ := by
  let a : ℝ := ((n+1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  let x : EuclideanSpace ℂ (Fin (n+1)) :=
    WithLp.toLp 2 (fun _ => (Real.sqrt a)⁻¹ : Fin (n+1) → ℂ)
  have hcoord (i : Fin (n+1)) : ‖x i‖ ^ 2 = a⁻¹ := by
    change ‖((Real.sqrt a)⁻¹ : ℂ)‖ ^ 2 = _
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt ha.le]
  have hx : ‖x‖ = 1 := by
    have hsq : ‖x‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp_rw [hcoord]
      simp [a, show (n : ℝ) + 1 ≠ 0 by positivity]
    nlinarith [norm_nonneg x]
  obtain ⟨U, hU₁, hU₂, hU₀⟩ := exists_unitary_prescribed_column 0 x hx
  exact ⟨U, hU₁, hU₂, fun i => (congrArg (fun z : ℂ => ‖z‖^2) (hU₀ i)).trans (hcoord i)⟩

end SpringerLean
