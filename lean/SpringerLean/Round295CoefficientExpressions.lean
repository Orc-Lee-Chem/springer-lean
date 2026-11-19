import SpringerLean.Round294RationalIdentityChecker
import Mathlib.RingTheory.PowerSeries.Basic

namespace SpringerLean.RatPolyCheck



theorem Expr.smartMulLeft_eval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (e f : Expr σ) :
    (Expr.smartMulLeft e f).eval v = e.eval v * f.eval v := by
  cases e with
  | const q => by_cases hq : q = 0 <;> simp [smartMulLeft, Expr.eval, hq]
  | var i => rfl
  | add e g => rfl
  | mul e g => rfl

/-- The left expression is a thunk: syntactically zero right factors do
not force an irrelevant recursive coefficient computation. -/


theorem Expr.mulUnlessRightZero_eval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (e : Unit → Expr σ) (f : Expr σ) :
    (Expr.mulUnlessRightZero e f).eval v = (e ()).eval v * f.eval v := by
  cases f with
  | const q => by_cases hq : q = 0 <;> simp [mulUnlessRightZero, Expr.smartMulLeft_eval, Expr.eval, hq]
  | var i => exact Expr.smartMulLeft_eval v _ _
  | add f g => exact Expr.smartMulLeft_eval v _ _
  | mul f g => exact Expr.smartMulLeft_eval v _ _



theorem Expr.smartAddLeft_eval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (e f : Expr σ) :
    (Expr.smartAddLeft e f).eval v = e.eval v + f.eval v := by
  cases e with
  | const q => by_cases hq : q = 0 <;> simp [smartAddLeft, Expr.eval, hq]
  | var i => rfl
  | add e g => rfl
  | mul e g => rfl



theorem Expr.smartAdd_eval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (e f : Expr σ) :
    (Expr.smartAdd e f).eval v = e.eval v + f.eval v := by
  cases f with
  | const q => by_cases hq : q = 0 <;> simp [smartAdd, Expr.smartAddLeft_eval, Expr.eval, hq]
  | var i => exact Expr.smartAddLeft_eval v _ _
  | add f g => exact Expr.smartAddLeft_eval v _ _
  | mul f g => exact Expr.smartAddLeft_eval v _ _



theorem Expr.fsum_eval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (f : ℕ → Expr σ) (n : ℕ) :
    (Expr.fsum f n).eval v = ∑ i ∈ Finset.range n, (f i).eval v := by
  induction n with
  | zero => simp [Expr.fsum, Expr.eval]
  | succ n ih => rw [Expr.fsum, Expr.smartAdd_eval, ih, Finset.sum_range_succ]



theorem Expr.pow_eval {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (e : Expr σ) (n : ℕ) : (Expr.pow e n).eval v = e.eval v ^ n := by
  induction n with
  | zero => simp [Expr.pow, Expr.eval]
  | succ n ih => simp only [Expr.pow, Expr.eval, ih, pow_succ]

/-- Finite Cauchy convolution as rational expression data. The recursion
is on the power, and every coefficient uses only a finite prefix. -/


theorem powerCoeffExpr_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (f : ℕ → Expr σ) (p : PowerSeries A)
    (hf : ∀ i, (f i).eval v = PowerSeries.coeff i p) (d n : ℕ) :
    (powerCoeffExpr f d n).eval v = PowerSeries.coeff n (p ^ d) := by
  induction d generalizing n with
  | zero =>
      by_cases hn : n = 0 <;> simp [powerCoeffExpr, Expr.eval, PowerSeries.coeff_one, hn]
  | succ d ih =>
      rw [powerCoeffExpr, Expr.fsum_eval, pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Expr.mulUnlessRightZero_eval, ih, hf]

/-- Two-variable Cauchy convolution, with i the inner index and j the
outer index. This is a concrete expression generator, not an assumed
table of logarithmic kernel coefficients. -/


theorem bipowerCoeffExpr_sound {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (f : ℕ → ℕ → Expr σ) (p : PowerSeries (PowerSeries A))
    (hf : ∀ i j, (f i j).eval v = PowerSeries.coeff i (PowerSeries.coeff j p))
    (d i j : ℕ) :
    (bipowerCoeffExpr f d i j).eval v =
      PowerSeries.coeff i (PowerSeries.coeff j (p ^ d)) := by
  induction d generalizing i j with
  | zero =>
      by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
        simp [bipowerCoeffExpr, Expr.eval, PowerSeries.coeff_one, hi, hj]
  | succ d ih =>
      rw [bipowerCoeffExpr, Expr.fsum_eval, pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Expr.fsum_eval, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Expr.mulUnlessRightZero_eval, ih, hf]

end SpringerLean.RatPolyCheck
