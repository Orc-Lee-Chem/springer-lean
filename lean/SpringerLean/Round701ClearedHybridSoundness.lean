import SpringerLean.Round695ClearedSumSoundness
import SpringerLean.Round627HybridPolynomialSoundness

/-! A denominator-cleared final identity check. Products retain the
factor normalization used by Hybrid; common denominators are cleared
before the final sparse merge. The proposed denominator is checked. -/
namespace SpringerLean.RatPolyCheck.ClearedHybrid
set_option Elab.async false

def check {σ : Type*} [DecidableEq σ] (r : σ → σ → Bool)
    (fuel D : Nat) (e f : Expr σ) : Bool :=
  ClearedSum.checkSparse r D
    (Hybrid.expandWith r (Hybrid.normalize r fuel) e [])
    (Hybrid.expandWith r (Hybrid.normalize r fuel) f []) []

theorem check_sound {σ A : Type*} [DecidableEq σ]
    [Field A] [CharZero A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (fuel D : Nat) (e f : Expr σ)
    (hc : check r fuel D e f = true) : e.eval v = f.eval v := by
  have hs := ClearedSum.checkSparse_sound v r D
    (Hybrid.expandWith r (Hybrid.normalize r fuel) e [])
    (Hybrid.expandWith r (Hybrid.normalize r fuel) f []) [] hc
  simpa only [Hybrid.expandWith_sound v r _ (Hybrid.normalize_sound v r fuel),
    eval_nil, add_zero] using hs

theorem square_smoke (v : Nat → Rat) :
    (Expr.mul (.add (.var 0) (.const (1/2)))
      (.add (.var 0) (.const (1/2)))).eval v =
    (Expr.add (.mul (.var 0) (.var 0))
      (.add (.var 0) (.const (1/4)))).eval v := by
  exact check_sound v (fun i j : Nat => decide (i ≤ j)) 2 4 _ _ (by decide +kernel)

end SpringerLean.RatPolyCheck.ClearedHybrid

#print axioms SpringerLean.RatPolyCheck.ClearedHybrid.check_sound
#print axioms SpringerLean.RatPolyCheck.ClearedHybrid.square_smoke
