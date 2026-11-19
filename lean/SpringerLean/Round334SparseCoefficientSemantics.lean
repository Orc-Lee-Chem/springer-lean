import SpringerLean.Round295CoefficientExpressions
import SpringerLean.Round332SparseTableLemmas

namespace SpringerLean.RatPolyCheck
open PowerSeries

theorem coreInsertVar_eq_orderedInsert {σ : Type*} (r : σ → σ → Bool)
    (a : σ) (l : List σ) : Structural.insertVar r a l =
      List.orderedInsert (fun x y => r x y = true) a l := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp only [Structural.insertVar, List.orderedInsert, ih]

theorem coreSortVars_eq_insertionSort {σ : Type*} (r : σ → σ → Bool)
    (l : List σ) : Structural.sortVars r l =
      List.insertionSort (fun x y => r x y = true) l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [Structural.sortVars, List.insertionSort_cons, coreInsertVar_eq_orderedInsert, ih]

theorem sparseStructuralMulTerm_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (t u : List σ × ℚ) :
    termEval v (Structural.mulTerm r t u) = termEval v t * termEval v u := by
  have hs := (List.perm_insertionSort (fun x y => r x y = true) (t.1 ++ u.1)).map v
  have hp := hs.prod_eq
  simp only [termEval, Structural.mulTerm, map_mul, coreSortVars_eq_insertionSort]
  rw [hp, List.map_append, List.prod_append]
  ring

theorem sparseStructuralMul_sound {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (r : σ → σ → Bool) (p q : Sparse σ) :
    eval v (Structural.mul r p q) = eval v p * eval v q := by
  have hm (t : List σ × ℚ) :
      eval v (q.map (Structural.mulTerm r t)) = termEval v t * eval v q := by
    induction q with
    | nil => simp
    | cons u q ih =>
        simp only [List.map_cons, eval_cons, sparseStructuralMulTerm_sound, ih]
        ring
  induction p with
  | nil => simp [Structural.mul]
  | cons t p ih =>
      rw [Structural.mul, add_sound, hm, ih, eval_cons]
      ring

theorem sparseSum_eval {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (f : ℕ → Sparse σ) (n : ℕ) :
    eval v (sparseSum f n) = ∑ i ∈ Finset.range n, eval v (f i) := by
  induction n with
  | zero => simp [sparseSum]
  | succ n ih => rw [sparseSum, add_sound, ih, Finset.sum_range_succ]

theorem sparseCauchyCoeff_eval {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (r : σ → σ → Bool)
    (A₀ B₀ : List (Sparse σ)) (p q : PowerSeries A) (n : ℕ)
    (hA : ∀ i, i ≤ n → eval v (A₀.getD i []) = PowerSeries.coeff i p)
    (hB : ∀ i, i ≤ n → eval v (B₀.getD i []) = PowerSeries.coeff i q) :
    eval v (sparseCauchyCoeff r A₀ B₀ n) = PowerSeries.coeff n (p * q) := by
  rw [sparseCauchyCoeff, sparseSum_eval, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sparseStructuralMul_sound, hA i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
    hB (n - i) (Nat.sub_le n i)]

theorem sparseSeriesPow_eval {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (r : σ → σ → Bool)
    (f : List (Sparse σ)) (p : PowerSeries A) (N : ℕ)
    (hf : ∀ i, i ≤ N → eval v (f.getD i []) = PowerSeries.coeff i p) (k : ℕ) :
    ∀ n, n ≤ N → eval v ((sparseSeriesPow r f N k).getD n []) =
      PowerSeries.coeff n (p ^ k) := by
  induction k with
  | zero =>
      intro n hn
      rw [sparseSeriesPow, sparseSeriesOne_getD N n hn]
      by_cases hz : n = 0 <;> simp [hz, eval, termEval, PowerSeries.coeff_one]
  | succ k ih =>
      intro n hn
      rw [sparseSeriesPow, sparseSeriesMul_getD r _ _ N n hn, pow_succ]
      apply sparseCauchyCoeff_eval
      · intro i hi
        exact ih i (hi.trans hn)
      · intro i hi
        exact hf i (hi.trans hn)

theorem variableProductExpr_eval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (m : List σ) : (variableProductExpr m).eval v = (m.map v).prod := by
  induction m with
  | nil => simp [variableProductExpr, Expr.eval]
  | cons a as ih => simp [variableProductExpr, Expr.eval, ih]

theorem sparseToExpr_eval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (p : Sparse σ) : (sparseToExpr p).eval v = eval v p := by
  induction p with
  | nil => simp [sparseToExpr, Expr.eval]
  | cons t p ih =>
      rcases t with ⟨m, q⟩
      simp only [sparseToExpr, Expr.smartAdd_eval, Expr.eval, variableProductExpr_eval,
        ih, eval_cons, termEval]

noncomputable def phiSeriesOf {A : Type*} [CommRing A] [Algebra ℚ A]
    (v : Bool × ℕ → A) : PowerSeries A :=
  PowerSeries.mk (fun n => if n = 0 then 1 else if n = 1 then 0 else v (false, n - 1))

theorem phiSparseCoefficients_eval {A : Type*} [CommRing A] [Algebra ℚ A]
    (v : Bool × ℕ → A) (N n : ℕ) (hn : n ≤ N) :
    eval v ((SpringerLean.phiSparseCoefficients N).getD n []) =
      PowerSeries.coeff n (phiSeriesOf v) := by
  rw [phiSparseCoefficients_getD N n hn]
  by_cases h0 : n = 0 <;> by_cases h1 : n = 1 <;>
    simp [phiSeriesOf, PowerSeries.coeff_mk, h0, h1, eval, termEval]

theorem fastPhiPowerCoefficients_eval {A : Type*} [CommRing A] [Algebra ℚ A]
    (v : Bool × ℕ → A) (k N n : ℕ) (hn : n ≤ N) :
    eval v ((SpringerLean.fastPhiPowerCoefficients k N).getD n []) =
      PowerSeries.coeff n ((phiSeriesOf v) ^ k) :=
  sparseSeriesPow_eval v _ _ _ N (phiSparseCoefficients_eval v N) k n hn

end SpringerLean.RatPolyCheck
