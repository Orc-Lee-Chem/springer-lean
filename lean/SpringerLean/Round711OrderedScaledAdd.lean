import SpringerLean.Round709ScaledAddSoundness

namespace SpringerLean.RatPolyCheck.OrderedScaledAdd
set_option Elab.async false

/-- Remove zero terms after propagating the proposed scalar. -/
def expanded {σ : Type*} (r : σ → σ → Bool) (D : Nat) (e : Expr σ) : Sparse σ :=
  (Fast.expand r (ScaledAdd.scaleConst (D : Rat) e)).filter (fun t => t.2 != 0)

def neg {σ : Type*} (p : Sparse σ) : Sparse σ := p.map (fun t => (t.1, -t.2))

def difference {σ : Type*} [DecidableEq σ] (r : σ → σ → Bool)
    (D : Nat) (e l q : Expr σ) : Sparse σ :=
  Ordered.add r (expanded r D e)
    (Ordered.add r (neg (expanded r D l)) (neg (expanded r D q)))

/-- Ordering improves completeness and cost, but is NOT a soundness
premise: every merge preserves evaluation even on unsorted inputs. -/
def check {σ : Type*} [DecidableEq σ] (r : σ → σ → Bool)
    (D : Nat) (e l q : Expr σ) : Bool :=
  decide (0 < D) && ((difference r D e l q).filter (fun t => t.2 != 0)).isEmpty

theorem expanded_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (D : Nat) (e : Expr σ) :
    eval v (expanded r D e) = algebraMap ℚ A (D : Rat)*e.eval v := by
  rw [expanded, Fast.filter_zero_sound, Fast.expand_sound, ScaledAdd.scaleConst_sound]

theorem neg_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (p : Sparse σ) : eval v (neg p) = -eval v p := by
  induction p with
  | nil => simp [neg]
  | cons t p ih =>
      simp only [neg, List.map_cons, eval_cons, termEval, map_neg] at *
      rw [ih]
      ring

theorem difference_sound {σ A : Type*} [DecidableEq σ]
    [CommRing A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (D : Nat) (e l q : Expr σ) :
    eval v (difference r D e l q) =
      algebraMap ℚ A (D : Rat)*(e.eval v-(l.eval v+q.eval v)) := by
  rw [difference, Ordered.add_sound, Ordered.add_sound, neg_sound, neg_sound,
    expanded_sound, expanded_sound, expanded_sound]
  ring

theorem check_sound {σ A : Type*} [DecidableEq σ]
    [Field A] [CharZero A] [Algebra ℚ A]
    (v : σ → A) (r : σ → σ → Bool) (D : Nat) (e l q : Expr σ)
    (hc : check r D e l q = true) : e.eval v = l.eval v+q.eval v := by
  have hs : decide (0 < D) = true ∧
      ((difference r D e l q).filter (fun t => t.2 != 0)).isEmpty = true := by
    simpa only [check, Bool.and_eq_true] using hc
  have hz : (difference r D e l q).filter (fun t => t.2 != 0) = [] := by
    simpa only [List.isEmpty_iff] using hs.2
  have he := Fast.filter_zero_sound v (difference r D e l q)
  rw [hz, eval_nil, difference_sound] at he
  have hD : algebraMap ℚ A (D : Rat) ≠ 0 := by
    simp only [map_natCast]
    exact_mod_cast ne_of_gt (of_decide_eq_true hs.1)
  exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left hD)

theorem half_plus_variable_smoke (v : Nat → Rat) :
    (Expr.add (.const (1/2)) (.var 0)).eval v =
      (Expr.const (1/2)).eval v+(Expr.var 0).eval v := by
  exact check_sound v (fun i j : Nat => decide (i ≤ j)) 2
    (.add (.const (1/2)) (.var 0)) (.const (1/2)) (.var 0) (by decide +kernel)

end SpringerLean.RatPolyCheck.OrderedScaledAdd

#print axioms SpringerLean.RatPolyCheck.OrderedScaledAdd.check_sound
#print axioms SpringerLean.RatPolyCheck.OrderedScaledAdd.half_plus_variable_smoke
