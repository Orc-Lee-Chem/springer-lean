import SpringerLean.Round694ClearedSumCore
import SpringerLean.Round558FastPolynomialSoundness

namespace SpringerLean.RatPolyCheck.ClearedSum
set_option Elab.async false

theorem clearCoeff_eq_mul (D : Nat) (q : Rat) (hd : q.den ∣ D) :
    clearCoeff D q = (D : Rat)*q := by
  have hden : (q.den : Rat) ≠ 0 := by exact_mod_cast q.den_nz
  have hnum : (q.num : Rat) = q*(q.den : Rat) :=
    (div_eq_iff hden).mp q.num_div_den
  have hD : (D : Rat) = (q.den : Rat)*((D/q.den : Nat) : Rat) := by
    exact_mod_cast (Nat.mul_div_cancel' hd).symm
  calc
    clearCoeff D q = (q.num : Rat)*((D/q.den : Nat) : Rat) := by
      simp only [clearCoeff, Int.cast_mul, Int.cast_natCast]
    _ = (q*(q.den : Rat))*((D/q.den : Nat) : Rat) := by rw [hnum]
    _ = (D : Rat)*q := by rw [hD]; ring

theorem clear_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (D : Nat) (p : Sparse σ)
    (hc : denominatorsDivide D p = true) :
    eval v (clear D p) = algebraMap ℚ A (D : Rat)*eval v p := by
  induction p with
  | nil => simp [clear, eval_nil]
  | cons t p ih =>
      have hcons : decide (t.2.den ∣ D) = true ∧ denominatorsDivide D p = true := by
        simpa only [denominatorsDivide, List.all_cons, Bool.and_eq_true] using hc
      have htail := ih hcons.2
      simp only [clear] at htail
      simp only [clear, List.map_cons, eval_cons, termEval]
      rw [htail, clearCoeff_eq_mul D t.2 (of_decide_eq_true hcons.1), map_mul]
      ring

theorem difference_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (D : Nat) (p l q : Sparse σ)
    (hp : denominatorsDivide D p = true)
    (hl : denominatorsDivide D l = true)
    (hq : denominatorsDivide D q = true) :
    eval v (difference r D p l q) =
      algebraMap ℚ A (D : Rat)*(eval v p-(eval v l+eval v q)) := by
  have hminus : eval v [([], (-1 : Rat))] = (-1 : A) := by
    simp [eval_cons, eval_nil, termEval]
  rw [difference, Ordered.eval_append, Fast.rawMul_sound, hminus,
    Ordered.eval_append, clear_sound v D p hp, clear_sound v D l hl,
    clear_sound v D q hq]
  ring

theorem reduced_sound {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (D : Nat) (p l q : Sparse σ) :
    eval v (reduced r D p l q) = eval v (difference r D p l q) := by
  rw [reduced, Fast.filter_zero_sound, Fast.sortFuel_sound]

/-- Soundness needs no ordering assumption. A wrong denominator or an
incorrect identity simply fails the checked Boolean premise. -/
theorem checkSparse_sound {σ A : Type*} [DecidableEq σ]
    [Field A] [CharZero A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (D : Nat) (p l q : Sparse σ)
    (hc : checkSparse r D p l q = true) : eval v p = eval v l+eval v q := by
  have hs : decide (0 < D) = true ∧ denominatorsDivide D p = true ∧
      denominatorsDivide D l = true ∧ denominatorsDivide D q = true ∧
      (reduced r D p l q).isEmpty = true := by
    simpa only [checkSparse, Bool.and_eq_true] using hc
  obtain ⟨hD, hp, hl, hq, hempty⟩ := hs
  have hzero : reduced r D p l q = [] := by
    simpa only [List.isEmpty_iff] using hempty
  have he := (reduced_sound v r D p l q).trans (difference_sound v r D p l q hp hl hq)
  rw [hzero, eval_nil] at he
  have hDne : algebraMap ℚ A (D : Rat) ≠ 0 := by
    simp only [map_natCast]
    exact_mod_cast ne_of_gt (of_decide_eq_true hD)
  exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left hDne)

theorem checkAdd_sound {σ A : Type*} [DecidableEq σ]
    [Field A] [CharZero A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (D : Nat) (e l q : Expr σ)
    (hc : checkAdd r D e l q = true) : e.eval v = l.eval v+q.eval v := by
  have hs := checkSparse_sound v r D (Fast.expand r e) (Fast.expand r l)
    (Fast.expand r q) hc
  simpa only [Fast.expand_sound] using hs

theorem half_plus_variable_smoke (v : Nat → Rat) :
    (Expr.add (.const (1/2)) (.var 0)).eval v =
      (Expr.const (1/2)).eval v+(Expr.var 0).eval v := by
  exact checkAdd_sound v (fun i j : Nat => decide (i ≤ j)) 2
    (.add (.const (1/2)) (.var 0)) (.const (1/2)) (.var 0) (by decide +kernel)

end SpringerLean.RatPolyCheck.ClearedSum

#print axioms SpringerLean.RatPolyCheck.ClearedSum.clearCoeff_eq_mul
#print axioms SpringerLean.RatPolyCheck.ClearedSum.checkAdd_sound
#print axioms SpringerLean.RatPolyCheck.ClearedSum.half_plus_variable_smoke
