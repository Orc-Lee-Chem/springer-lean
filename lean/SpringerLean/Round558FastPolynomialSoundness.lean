import SpringerLean.Round557FastPolynomialCore
import SpringerLean.Round348OrderedPolynomialSemantics

namespace SpringerLean.RatPolyCheck.Fast

theorem rawMul_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (p q : Sparse σ) :
    eval v (rawMul r p q) = eval v p * eval v q := by
  have hm (t : List σ × Rat) (q : Sparse σ) :
      eval v (q.map (Structural.mulTerm r t)) = termEval v t * eval v q := by
    induction q with
    | nil => simp
    | cons u q ih =>
        simp only [List.map_cons, eval_cons, sparseStructuralMulTerm_sound, ih]
        ring
  induction p with
  | nil => simp [rawMul]
  | cons t p ih =>
      simp only [rawMul, List.flatMap_cons, Ordered.eval_append] at *
      rw [hm t q]
      rw [ih, eval_cons]
      ring

theorem expandAcc_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (e : Expr σ) (p : Sparse σ) :
    eval v (expandAcc r e p) = e.eval v + eval v p := by
  induction e generalizing p with
  | const q => simp [expandAcc, Expr.eval, eval_cons, termEval]
  | var i => simp [expandAcc, Expr.eval, eval_cons, termEval]
  | add e f he hf => rw [expandAcc, he, hf, Expr.eval, add_assoc]
  | mul e f he hf =>
      rw [expandAcc, Ordered.eval_append, rawMul_sound, he, hf]
      simp only [eval_nil, add_zero, Expr.eval]

theorem expand_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (e : Expr σ) :
    eval v (expand r e) = e.eval v := by
  simpa only [expand, eval_nil, add_zero] using expandAcc_sound v r e []

theorem mergeHead_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (t : List σ × Rat) (p : Sparse σ) :
    eval v (mergeHead t p) = termEval v t + eval v p := by
  cases p with
  | nil => simp [mergeHead]
  | cons u p =>
      rcases t with ⟨m,c⟩
      rcases u with ⟨l,d⟩
      by_cases h : m = l
      · subst l
        simp only [mergeHead, ite_true, eval_cons, termEval, map_add]
        ring
      · simp only [mergeHead, h, ite_false, eval_cons]

theorem pack_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (p : Sparse σ) : eval v (pack p) = eval v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      simpa only [pack, List.foldr_cons, mergeHead_sound, eval_cons] using
        congrArg (fun x => termEval v t + x) ih

theorem filter_zero_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (p : Sparse σ) :
    eval v (p.filter (fun t => t.2 != 0)) = eval v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      by_cases h : t.2 = 0
      · simp [List.filter_cons, h, eval_cons, termEval, ih]
      · simp [List.filter_cons, h, eval_cons, ih]

theorem sortFuel_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (n : Nat) (p : Sparse σ) :
    eval v (sortFuel r n p) = eval v p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      cases p with
      | nil => rfl
      | cons t p =>
          cases p with
          | nil => rfl
          | cons u p =>
              rw [sortFuel, Ordered.add_sound, ih, ih, ← Ordered.eval_append,
                List.take_append_drop]

theorem normalize_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (e : Expr σ) :
    eval v (normalize r e) = e.eval v := by
  rw [normalize, filter_zero_sound, sortFuel_sound, expand_sound]

theorem check_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (e f : Expr σ)
    (hc : check r e f = true) : e.eval v = f.eval v := by
  have hz : normalize r (.add e (.mul (.const (-1)) f)) = [] := by
    simpa only [check, List.isEmpty_iff] using hc
  have hs := normalize_sound v r (.add e (.mul (.const (-1)) f))
  rw [hz, eval_nil] at hs
  exact eq_of_sub_eq_zero (show e.eval v - f.eval v = 0 by
    simpa [Expr.eval, sub_eq_add_neg] using hs.symm)

end SpringerLean.RatPolyCheck.Fast
