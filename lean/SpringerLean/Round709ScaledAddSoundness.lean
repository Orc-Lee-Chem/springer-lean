import SpringerLean.Round695ClearedSumSoundness

namespace SpringerLean.RatPolyCheck.ScaledAdd
set_option Elab.async false

/-- Push a scalar through additions and into the left factor of products.
In particular it reaches a leaf's rational weight before its integer
polynomial is expanded. This avoids repeatedly reducing large fractions. -/
def scaleConst {σ : Type*} (q : Rat) : Expr σ → Expr σ
  | .const c => .const (q*c)
  | .var i => .mul (.const q) (.var i)
  | .add e f => .add (scaleConst q e) (scaleConst q f)
  | .mul e f => .mul (scaleConst q e) f

theorem scaleConst_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (q : Rat) (e : Expr σ) :
    (scaleConst q e).eval v = algebraMap ℚ A q * e.eval v := by
  induction e with
  | const c => simp only [scaleConst, Expr.eval, map_mul]
  | var i => rfl
  | add e f he hf => simp only [scaleConst, Expr.eval, he, hf]; ring
  | mul e f he hf => simp only [scaleConst, Expr.eval, he]; ring

/-- D is an optimization proposal. Soundness only requires D>0 and the
FULL scaled polynomial identity, both checked in the kernel. No claim
that denominators have been cleared is needed as a premise. -/
def check {σ : Type*} [DecidableEq σ] (r : σ → σ → Bool)
    (D : Nat) (e l q : Expr σ) : Bool :=
  decide (0 < D) && Fast.check r (scaleConst (D : Rat) e)
    (.add (scaleConst (D : Rat) l) (scaleConst (D : Rat) q))

theorem check_sound {σ A : Type*} [DecidableEq σ]
    [Field A] [CharZero A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (D : Nat) (e l q : Expr σ)
    (hc : check r D e l q = true) : e.eval v = l.eval v+q.eval v := by
  have hs : decide (0 < D) = true ∧
      Fast.check r (scaleConst (D : Rat) e)
        (.add (scaleConst (D : Rat) l) (scaleConst (D : Rat) q)) = true := by
    simpa only [check, Bool.and_eq_true] using hc
  have he := Fast.check_sound v r _ _ hs.2
  simp only [Expr.eval, scaleConst_sound] at he
  have hD : algebraMap ℚ A (D : Rat) ≠ 0 := by
    simp only [map_natCast]
    exact_mod_cast ne_of_gt (of_decide_eq_true hs.1)
  apply mul_left_cancel₀ hD
  simpa only [mul_add] using he

theorem half_plus_variable_smoke (v : Nat → Rat) :
    (Expr.add (.const (1/2)) (.var 0)).eval v =
      (Expr.const (1/2)).eval v+(Expr.var 0).eval v := by
  exact check_sound v (fun i j : Nat => decide (i ≤ j)) 2
    (.add (.const (1/2)) (.var 0)) (.const (1/2)) (.var 0) (by decide +kernel)

end SpringerLean.RatPolyCheck.ScaledAdd

#print axioms SpringerLean.RatPolyCheck.ScaledAdd.scaleConst_sound
#print axioms SpringerLean.RatPolyCheck.ScaledAdd.check_sound
#print axioms SpringerLean.RatPolyCheck.ScaledAdd.half_plus_variable_smoke
