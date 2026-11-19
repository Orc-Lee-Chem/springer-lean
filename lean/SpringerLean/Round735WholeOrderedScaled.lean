import SpringerLean.Round709ScaledAddSoundness

namespace SpringerLean.RatPolyCheck.WholeOrderedScaled
set_option Elab.async false

/-- A proposed scalar is propagated before the existing proved ordered
normalizer is run.  The check is the FULL two-expression identity, and a
bad term order cannot certify a false identity. -/
def check {σ : Type*} [DecidableEq σ] (r : σ → σ → Bool)
    (D : Nat) (e f : Expr σ) : Bool :=
  decide (0 < D) && Ordered.check r (ScaledAdd.scaleConst (D : Rat) e)
    (ScaledAdd.scaleConst (D : Rat) f)

theorem check_sound {σ A : Type*} [DecidableEq σ]
    [Field A] [CharZero A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (D : Nat) (e f : Expr σ)
    (hc : check r D e f = true) : e.eval v = f.eval v := by
  have hs : decide (0 < D) = true ∧
      Ordered.check r (ScaledAdd.scaleConst (D : Rat) e)
        (ScaledAdd.scaleConst (D : Rat) f) = true := by
    simpa only [check, Bool.and_eq_true] using hc
  have he := Ordered.check_sound v r _ _ hs.2
  rw [ScaledAdd.scaleConst_sound, ScaledAdd.scaleConst_sound] at he
  have hD : algebraMap ℚ A (D : Rat) ≠ 0 := by
    simp only [map_natCast]
    exact_mod_cast ne_of_gt (of_decide_eq_true hs.1)
  exact mul_left_cancel₀ hD he

theorem half_square_smoke (v : Nat → Rat) :
    (Expr.mul (.add (.var 0) (.const (1/2))) (.add (.var 0) (.const (1/2)))).eval v =
      (Expr.add (.mul (.var 0) (.var 0)) (.add (.var 0) (.const (1/4)))).eval v := by
  exact check_sound v (fun i j : Nat => decide (i ≤ j)) 4 _ _ (by decide +kernel)

end SpringerLean.RatPolyCheck.WholeOrderedScaled

#print axioms SpringerLean.RatPolyCheck.WholeOrderedScaled.check_sound
#print axioms SpringerLean.RatPolyCheck.WholeOrderedScaled.half_square_smoke
