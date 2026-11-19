import SpringerLean.Round626HybridPolynomialCore
import SpringerLean.Round558FastPolynomialSoundness

namespace SpringerLean.RatPolyCheck.Hybrid

theorem expandWith_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (nf : Expr σ → Sparse σ)
    (hnf : ∀ e, eval v (nf e) = e.eval v) (e : Expr σ) (p : Sparse σ) :
    eval v (expandWith r nf e p) = e.eval v + eval v p := by
  induction e generalizing p with
  | const q => simp [expandWith,Expr.eval,eval_cons,termEval]
  | var i => simp [expandWith,Expr.eval,eval_cons,termEval]
  | add e f he hf => rw [expandWith,he,hf,Expr.eval,add_assoc]
  | mul e f he hf =>
      rw [expandWith,Ordered.eval_append,Fast.rawMul_sound,hnf,hnf,Expr.eval]

theorem finish_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (p : Sparse σ) :
    eval v (finish r p) = eval v p := by
  rw [finish,Fast.filter_zero_sound,Fast.sortFuel_sound]

theorem normalize_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (n : Nat) (e : Expr σ) :
    eval v (normalize r n e) = e.eval v := by
  induction n generalizing e with
  | zero => exact Fast.normalize_sound v r e
  | succ n ih =>
      rw [normalize,finish_sound,expandWith_sound v r _ ih]
      simp only [eval_nil,add_zero]

theorem check_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (n : Nat) (e f : Expr σ)
    (hc : check r n e f = true) : e.eval v = f.eval v := by
  have hz : normalize r n (.add e (.mul (.const (-1)) f)) = [] := by
    simpa only [check,List.isEmpty_iff] using hc
  have hs := normalize_sound v r n (.add e (.mul (.const (-1)) f))
  rw [hz,eval_nil] at hs
  exact eq_of_sub_eq_zero (show e.eval v - f.eval v = 0 by
    simpa [Expr.eval,sub_eq_add_neg] using hs.symm)

end SpringerLean.RatPolyCheck.Hybrid
