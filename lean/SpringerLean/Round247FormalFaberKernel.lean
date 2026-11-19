import SpringerLean.Round246FormalLog

namespace SpringerLean
open PowerSeries

/-- Row n of the formal exterior difference-quotient correction. The
constant inner coefficient is zero; its j-th coefficient is b_(n+j-1). -/
noncomputable def formalFaberKernelRow
    {A : Type*} [CommRing A] (f : PowerSeries A) (n : ℕ) :
    PowerSeries A :=
  PowerSeries.mk fun j => if j = 0 then 0 else PowerSeries.coeff (n + j - 1) f

@[simp] theorem formalFaberKernelRow_constantCoeff
    {A : Type*} [CommRing A] (f : PowerSeries A) (n : ℕ) :
    PowerSeries.constantCoeff (formalFaberKernelRow f n) = 0 := by
  simp [formalFaberKernelRow]

@[simp] theorem formalFaberKernelRow_coeff_succ
    {A : Type*} [CommRing A] (f : PowerSeries A) (n j : ℕ) :
    PowerSeries.coeff (j + 1) (formalFaberKernelRow f n) =
      PowerSeries.coeff (n + j) f := by
  simp [formalFaberKernelRow, Nat.add_sub_cancel]

theorem formalFaberKernelRow_one
    {A : Type*} [CommRing A] (f : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 0) :
    formalFaberKernelRow f 1 = f := by
  ext j
  cases j with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff, hf]
  | succ j => simp [Nat.add_comm]

/-- The exact shift relation shared by every row and every truncation. -/
theorem formalFaberKernelRow_shift
    {A : Type*} [CommRing A] (f : PowerSeries A) (n : ℕ) :
    PowerSeries.X * formalFaberKernelRow f (n + 1) =
      formalFaberKernelRow f n -
        PowerSeries.C (PowerSeries.coeff n f) * PowerSeries.X := by
  ext j
  cases j with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ j =>
      cases j with
      | zero => simp
      | succ j => simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

noncomputable def formalFaberKernel
    {A : Type*} [CommRing A] (f : PowerSeries A) :
    PowerSeries (PowerSeries A) :=
  PowerSeries.mk fun n => if n = 0 then 0 else formalFaberKernelRow f n

@[simp] theorem formalFaberKernel_constantCoeff
    {A : Type*} [CommRing A] (f : PowerSeries A) :
    PowerSeries.constantCoeff (formalFaberKernel f) = 0 := by
  simp [formalFaberKernel]

@[simp] theorem formalFaberKernel_coeff_succ
    {A : Type*} [CommRing A] (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff (n + 1) (formalFaberKernel f) =
      formalFaberKernelRow f (n + 1) := by
  simp [formalFaberKernel]

/-- The actual algebraic difference-quotient factorization before any
Laurent inversion. Both variables remain ordinary formal power series.
This is the uniform source of the Faber/logarithmic-kernel connection. -/
theorem formalFaberKernel_factorization
    {A : Type*} [CommRing A] (f : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 0) :
    let φ := 1 + PowerSeries.X * f
    (PowerSeries.C (PowerSeries.X : PowerSeries A) - PowerSeries.X) *
        (1 - formalFaberKernel f) =
      PowerSeries.C (PowerSeries.X : PowerSeries A) *
          PowerSeries.map (PowerSeries.C : A →+* PowerSeries A) φ -
        PowerSeries.X * PowerSeries.C φ := by
  dsimp only
  let T := formalFaberKernel f
  have hform :
      (PowerSeries.C (PowerSeries.X : PowerSeries A) - PowerSeries.X) * (1 - T) =
      PowerSeries.C (PowerSeries.X : PowerSeries A) - PowerSeries.X -
        PowerSeries.C (PowerSeries.X : PowerSeries A) * T + PowerSeries.X * T := by
    ring
  rw [hform]
  ext n
  cases n with
  | zero => simp [T, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
      cases n with
      | zero =>
          simp [T, PowerSeries.coeff_C_mul, PowerSeries.coeff_map,
            formalFaberKernelRow_one f hf,
            PowerSeries.coeff_zero_eq_constantCoeff, hf]
          ring
      | succ n =>
          have hrow := formalFaberKernelRow_shift f (n + 1)
          simp [T, PowerSeries.coeff_C_mul, PowerSeries.coeff_map,
            PowerSeries.coeff_X]
          rw [hrow]
          simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X]

end SpringerLean
