import SpringerLean.Round321CertificateCore
import Mathlib.Data.List.Sort
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace SpringerLean.RatPolyCheck



noncomputable def termEval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (t : List σ × ℚ) : A :=
  algebraMap ℚ A t.2 * (t.1.map v).prod

noncomputable def eval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (p : Sparse σ) : A := (p.map (termEval v)).sum

@[simp] theorem eval_nil {σ A : Type*} [CommRing A] [Algebra ℚ A] (v : σ → A) :
    eval v [] = 0 := rfl

@[simp] theorem eval_cons {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (t : List σ × ℚ) (p : Sparse σ) :
    eval v (t :: p) = termEval v t + eval v p := rfl



theorem insertTerm_sound {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (t : List σ × ℚ) (p : Sparse σ) :
    eval v (insertTerm t p) = termEval v t + eval v p := by
  induction p with
  | nil =>
      by_cases h : t.2 = 0 <;> simp [insertTerm, h, eval, termEval]
  | cons a p ih =>
      rcases t with ⟨m, c⟩
      rcases a with ⟨n, d⟩
      by_cases hc : c = 0
      · simp [insertTerm, hc, termEval]
      by_cases hmn : m = n
      · subst n
        by_cases hcd : c + d = 0
        · have hmap : algebraMap ℚ A c + algebraMap ℚ A d = 0 := by
            rw [← map_add, hcd, map_zero]
          simp only [insertTerm, hc, ite_false, ite_true, hcd, eval_cons, termEval]
          linear_combination -hmap * (m.map v).prod
        · simp only [insertTerm, hc, ite_false, ite_true, hcd, eval_cons, termEval, map_add]
          ring
      · simp only [insertTerm, hc, ite_false, hmn, eval_cons, ih]
        ring



theorem add_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (p q : Sparse σ) : eval v (add p q) = eval v p + eval v q := by
  induction p with
  | nil => simp [add]
  | cons t p ih => rw [add, insertTerm_sound, ih, eval_cons]; ring



theorem mulTerm_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (t u : List σ × ℚ) :
    termEval v (mulTerm r t u) = termEval v t * termEval v u := by
  have hs := (List.mergeSort_perm (t.1 ++ u.1) r).map v
  have hp := hs.prod_eq
  simp only [termEval, mulTerm, map_mul]
  rw [hp, List.map_append, List.prod_append]
  ring



theorem eval_map_mulTerm {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (t : List σ × ℚ) (q : Sparse σ) :
    eval v (q.map (mulTerm r t)) = termEval v t * eval v q := by
  induction q with
  | nil => simp
  | cons u q ih =>
      simp only [List.map_cons, eval_cons, mulTerm_sound, ih]
      ring

theorem mul_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (p q : Sparse σ) :
    eval v (mul r p q) = eval v p * eval v q := by
  induction p with
  | nil => simp [mul]
  | cons t p ih =>
      rw [mul, add_sound, eval_map_mulTerm, ih, eval_cons]
      ring



noncomputable def Expr.eval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) : Expr σ → A
  | .const q => algebraMap ℚ A q
  | .var i => v i
  | .add e f => e.eval v + f.eval v
  | .mul e f => e.eval v * f.eval v



theorem normalize_sound {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (r : σ → σ → Bool) (e : Expr σ) :
    eval v (normalize r e) = e.eval v := by
  induction e with
  | const q => by_cases hq : q = 0 <;> simp [normalize, Expr.eval, eval, termEval, hq]
  | var i => simp [normalize, Expr.eval, eval, termEval]
  | add e f he hf => rw [normalize, add_sound, he, hf]; rfl
  | mul e f he hf => rw [normalize, mul_sound, he, hf]; rfl

/-- Executable rational identity checker. No native evaluator, external
oracle, analytic premise or choice of mathematical conclusions is used. -/


theorem check_sound {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (r : σ → σ → Bool)
    (e f : Expr σ) (hcheck : check r e f = true) : e.eval v = f.eval v := by
  have hz : normalize r (.add e (.mul (.const (-1)) f)) = [] := by
    simpa only [check, List.isEmpty_iff] using hcheck
  have hs := normalize_sound v r (.add e (.mul (.const (-1)) f))
  rw [hz, eval_nil] at hs
  exact eq_of_sub_eq_zero (show e.eval v - f.eval v = 0 by
    simpa [Expr.eval, sub_eq_add_neg] using hs.symm)

theorem check_double_variable :
    check (fun i j : ℕ => decide (i ≤ j))
      (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)) = true := by
  norm_num [check, normalize, add, mul, insertTerm, mulTerm]

end SpringerLean.RatPolyCheck
