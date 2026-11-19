import SpringerLean.Round334SparseCoefficientSemantics
import SpringerLean.Round346OrderedPolynomialCore

namespace SpringerLean.RatPolyCheck.Ordered

theorem eval_append {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (p q : Sparse σ) : eval v (p ++ q) = eval v p + eval v q := by
  simp [eval, List.map_append, List.sum_append]

theorem addFuel_sound {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (r : σ → σ → Bool)
    (fuel : ℕ) (p q : Sparse σ) :
    eval v (addFuel r fuel p q) = eval v p + eval v q := by
  induction fuel generalizing p q with
  | zero => simpa only [addFuel] using eval_append v p q
  | succ n ih =>
      cases p with
      | nil => simp [addFuel]
      | cons t p =>
          cases q with
          | nil => simp [addFuel]
          | cons u q =>
              rcases t with ⟨m,c⟩
              rcases u with ⟨l,d⟩
              by_cases h : m = l
              · subst l
                by_cases hc : c + d = 0
                · have hm : algebraMap ℚ A c + algebraMap ℚ A d = 0 := by
                    rw [← map_add, hc, map_zero]
                  rw [addFuel, if_pos rfl, if_pos hc, ih]
                  simp only [eval_cons, termEval]
                  linear_combination -hm * (m.map v).prod
                · rw [addFuel, if_pos rfl, if_neg hc, eval_cons, ih]
                  simp only [eval_cons, termEval, map_add]
                  ring
              · by_cases hl : monomialLE r m l = true
                · rw [addFuel, if_neg h, if_pos hl, eval_cons, ih]
                  simp only [eval_cons]
                  ring
                · rw [addFuel, if_neg h, if_neg hl, eval_cons, ih]
                  simp only [eval_cons]
                  ring

theorem add_sound {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (r : σ → σ → Bool) (p q : Sparse σ) :
    eval v (add r p q) = eval v p + eval v q :=
  addFuel_sound v r _ p q

theorem mul_sound {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (r : σ → σ → Bool) (p q : Sparse σ) :
    eval v (mul r p q) = eval v p * eval v q := by
  have hm (t : List σ × ℚ) :
      eval v (q.map (Structural.mulTerm r t)) = termEval v t * eval v q := by
    induction q with
    | nil => simp
    | cons u q ih =>
        simp only [List.map_cons, eval_cons, sparseStructuralMulTerm_sound, ih]
        ring
  induction p with
  | nil => simp [mul]
  | cons t p ih =>
      rw [mul, add_sound, hm, ih, eval_cons]
      ring

theorem normalize_sound {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (r : σ → σ → Bool) (e : Expr σ) :
    eval v (normalize r e) = e.eval v := by
  induction e with
  | const q => by_cases hq : q = 0 <;> simp [normalize, Expr.eval, eval, termEval, hq]
  | var i => simp [normalize, Expr.eval, eval, termEval]
  | add e f he hf => rw [normalize, add_sound, he, hf]; rfl
  | mul e f he hf => rw [normalize, mul_sound, he, hf]; rfl

theorem check_sound {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A] (v : σ → A) (r : σ → σ → Bool)
    (e f : Expr σ) (hc : check r e f = true) : e.eval v = f.eval v := by
  have hz : normalize r (.add e (.mul (.const (-1)) f)) = [] := by
    simpa only [check, List.isEmpty_iff] using hc
  have hs := normalize_sound v r (.add e (.mul (.const (-1)) f))
  rw [hz, eval_nil] at hs
  exact eq_of_sub_eq_zero (show e.eval v - f.eval v = 0 by
    simpa [Expr.eval, sub_eq_add_neg] using hs.symm)

end SpringerLean.RatPolyCheck.Ordered
