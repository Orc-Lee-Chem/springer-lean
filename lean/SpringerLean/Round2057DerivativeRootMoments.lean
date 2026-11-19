import SpringerLean.Round2052CompressionDeterminant
import SpringerLean.Round2055UnitarySchur
import SpringerLean.Round2056CompressionJensen

open Polynomial Matrix
open scoped ComplexConjugate

namespace SpringerLean

private theorem charpoly_unitary_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    (Uᴴ * A * U).charpoly = A.charpoly := by
  rw [Matrix.mul_assoc, charpoly_mul_comm Uᴴ, Matrix.mul_assoc, hU, Matrix.mul_one]

private theorem unitary_schur_on_compression
    {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1) :
    ∃ W : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      (∀ i, W i 0 = U i 0) ∧
      ((Wᴴ * A * W).submatrix Fin.succ Fin.succ).BlockTriangular id ∧
      ((Wᴴ * A * W).submatrix Fin.succ Fin.succ).charpoly =
        ((Uᴴ * A * U).submatrix Fin.succ Fin.succ).charpoly := by
  let B := Uᴴ * A * U
  obtain ⟨V, hV₁, hV₂, htri⟩ := exists_unitary_schur_triangular n
    (B.submatrix Fin.succ Fin.succ)
  let E := unitarySchurExtend V
  have hE₁ : Eᴴ * E = 1 := by
    dsimp [E]
    rw [unitarySchurExtend_conjTranspose, unitarySchurExtend_mul, hV₁,
      unitarySchurExtend_one]
  have hE₂ : E * Eᴴ = 1 := by
    dsimp [E]
    rw [unitarySchurExtend_conjTranspose, unitarySchurExtend_mul, hV₂,
      unitarySchurExtend_one]
  have hB : (U * E)ᴴ * A * (U * E) = Eᴴ * B * E := by simp [B, Matrix.mul_assoc]
  have hS : ((U * E)ᴴ * A * (U * E)).submatrix Fin.succ Fin.succ =
      Vᴴ * B.submatrix Fin.succ Fin.succ * V := by
    rw [hB]
    ext i j
    exact unitarySchurExtend_conjugate_succ_succ B V i j
  refine ⟨U*E, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U E, hU₁, Matrix.one_mul, hE₁]
  · simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc E Eᴴ Uᴴ, hE₂, Matrix.one_mul, hU₂]
  · intro i
    simp [Matrix.mul_apply, Fin.sum_univ_succ, E]
  · rw [hS]
    exact htri
  · rw [hS, charpoly_unitary_conjugate _ V hV₂]

private theorem derivative_linear_factor_power_mean
    (n : ℕ) (hn : 0 < n) (d : Fin (n+1) → ℂ) (p : ℝ) (hp : 1 ≤ p) :
    let Q := ∏ i : Fin (n+1), (X - C (d i))
    ((Q.derivative.roots.map (fun z : ℂ => ‖z‖ ^ p)).sum) / (n : ℝ) ≤
      (∑ i, ‖d i‖ ^ p) / ((n+1 : ℕ) : ℝ) := by
  classical
  let Q := ∏ i : Fin (n+1), (X - C (d i))
  obtain ⟨U, hU₁, hU₂, hU₀⟩ := exists_unitary_uniform_first_column n
  obtain ⟨W, hW₁, hW₂, hW₀, htri, hchar⟩ := unitary_schur_on_compression
    (diagonal d) U hU₁ hU₂
  let d' (j : Fin n) := (Wᴴ * diagonal d * W) j.succ j.succ
  have hc0 : ((n+1 : ℕ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  have hweight (i : Fin (n+1)) :
      Uᴴ 0 i * U i 0 = ((n+1 : ℕ) : ℂ)⁻¹ := by
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
    rw [← Complex.ofReal_pow, hU₀, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hcomp :=
    charpoly_uniform_diagonal_compression d U Uᴴ hU₂ hU₁ _ hweight
  simp only [Fin.succAbove_zero] at hcomp
  have hpoly : (∏ i : Fin n, (X - C (d' i))) = C (((n+1 : ℕ) : ℂ)⁻¹) * Q.derivative := by
    calc
      _ = ((Wᴴ * diagonal d * W).submatrix Fin.succ Fin.succ).charpoly := by
        simpa only [d', Matrix.submatrix_apply] using
          (charpoly_of_isUpperTriangular _ htri).symm
      _ = _ := hchar.trans hcomp
  have hroot : Q.derivative.roots = Finset.univ.val.map d' := by
    rw [← roots_C_mul _ hc0, ← hpoly]
    simpa only [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod] using
      (roots_multiset_prod_X_sub_C (Finset.univ.val.map d'))
  have hsum := unitary_uniform_compression_diagonal_power_sum n W hW₁ hW₂
    (fun i => by rw [hW₀, hU₀]) d p hp
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  dsimp only
  change (Q.derivative.roots.map _).sum / _ ≤ _
  rw [hroot, Multiset.map_map]
  change (∑ j, ‖d' j‖ ^ p) / (n : ℝ) ≤ _
  apply (div_le_iff₀ hn').mpr
  exact hsum.trans_eq (by ring)

set_option maxHeartbeats 600000 in
/-- One derivative does not increase the normalized root power mean.
Repeated roots contribute with their algebraic multiplicities. -/
theorem polynomial_derivative_root_power_mean_le
    (Q : ℂ[X]) (hQ : 1 < Q.natDegree) (p : ℝ) (hp : 1 ≤ p) :
    (Q.derivative.roots.map (fun z : ℂ => ‖z‖ ^ p)).sum /
      ((Q.natDegree-1 : ℕ) : ℝ) ≤
    (Q.roots.map (fun z : ℂ => ‖z‖ ^ p)).sum / (Q.natDegree : ℝ) := by
  classical
  let n := Q.natDegree - 1
  have hn : 0 < n := by dsimp [n]; omega
  have hnQ : n+1 = Q.natDegree := by dsimp [n]; omega
  have hlen : Q.roots.toList.length = n+1 := by
    exact (Multiset.length_toList _).trans
      ((IsAlgClosed.splits Q).natDegree_eq_card_roots.symm.trans hnQ.symm)
  let d : Fin (n+1) → ℂ := fun i => Q.roots.toList.get (i.cast hlen.symm)
  have hd : Finset.univ.val.map d = Q.roots := by
    rw [Fin.univ_val_map]
    have hlist := List.ofFn_congr hlen Q.roots.toList.get
    exact congrArg (fun l : List ℂ => (l : Multiset ℂ))
      (hlist.symm.trans (List.ofFn_get _)) |>.trans (Multiset.coe_toList _)
  let R := ∏ i : Fin (n+1), (X - C (d i))
  have hfactor : Q = C Q.leadingCoeff * R := by
    calc
      _ = C Q.leadingCoeff * (Q.roots.map (fun a => X - C a)).prod :=
        (IsAlgClosed.splits Q).eq_prod_roots
      _ = _ := by rw [← hd, Multiset.map_map]; rfl
  have hQ0 : Q ≠ 0 := by intro H; simp [H] at hQ
  have hrootsD : Q.derivative.roots = R.derivative.roots := by
    have h := congrArg derivative hfactor
    rw [derivative_C_mul] at h
    rw [h, roots_C_mul _ (leadingCoeff_ne_zero.mpr hQ0)]
  rw [hrootsD, ← hd, Multiset.map_map, ← hnQ]
  exact derivative_linear_factor_power_mean n hn d p hp

theorem polynomial_iterated_derivative_natDegree (Q : ℂ[X]) (j : ℕ) :
    ((derivative^[j]) Q).natDegree = Q.natDegree - j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', natDegree_derivative, ih]
    omega

/-- Arbitrarily many derivatives preserve the normalized power
comparison as long as the final degree is positive. -/
theorem polynomial_iterated_derivative_root_power_mean_le
    (Q : ℂ[X]) (j : ℕ) (hj : j < Q.natDegree) (p : ℝ) (hp : 1 ≤ p) :
    ((((derivative^[j]) Q).roots.map (fun z : ℂ => ‖z‖ ^ p)).sum) /
      ((Q.natDegree-j : ℕ) : ℝ) ≤
    (Q.roots.map (fun z : ℂ => ‖z‖ ^ p)).sum / (Q.natDegree : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    let Qj := (derivative^[j]) Q
    have hdeg : Qj.natDegree = Q.natDegree - j := polynomial_iterated_derivative_natDegree Q j
    have hpos : 1 < Qj.natDegree := by rw [hdeg]; omega
    have hstep := polynomial_derivative_root_power_mean_le Qj hpos p hp
    have hj' : j < Q.natDegree := by omega
    rw [Function.iterate_succ_apply']
    have heq : Q.natDegree - (j+1) = Qj.natDegree - 1 := by rw [hdeg]; omega
    rw [heq]
    exact hstep.trans (by simpa only [hdeg] using ih hj')

end SpringerLean
