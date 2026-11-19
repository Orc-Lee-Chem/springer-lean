import SpringerLean.Round2018OddStarConditionalFactorBridge

namespace SpringerLean

/-- Rotational covariance of an exterior map under all 2k-th roots of
unity. For an arbitrary continuum this must still be derived from
symmetry and uniqueness of the normalized exterior map. -/
def EvenExteriorCovariant (F : ℂ → ℂ) (k : ℕ) : Prop :=
  ∀ (η z : ℂ), η ^ (2*k) = 1 → z ∈ exteriorDisk →
    F (η*z) = η * F z

theorem evenExterior_power_fiber_eq
    (F : ℂ → ℂ) (k : ℕ)
    (hcov : EvenExteriorCovariant F k)
    (z w : ℂ) (hw : w ∈ exteriorDisk)
    (hpow : z ^ k = w ^ k) :
    (F z) ^ k = (F w) ^ k := by
  have hw0 : w ≠ 0 := by
    intro heq
    subst w
    have hh : 1 < ‖(0:ℂ)‖ := hw
    norm_num at hh
  let η : ℂ := z / w
  have hηk : η ^ k = 1 := by
    dsimp [η]
    rw [div_pow, hpow, div_self (pow_ne_zero k hw0)]
  have hηm : η ^ (2*k) = 1 := by
    rw [mul_comm 2 k, pow_mul, hηk, one_pow]
  have hzform : η*w = z := by
    dsimp [η]
    field_simp
  calc
    (F z) ^ k = (F (η*w)) ^ k := by rw [hzform]
    _ = (η*F w) ^ k := by rw [hcov η w hηm hw]
    _ = (F w) ^ k := by rw [mul_pow, hηk, one_mul]

/-- An algebraic quotient map; analyticity and univalence are separate
obligations. -/
noncomputable def evenExteriorPowerQuotient (F : ℂ → ℂ) (k : ℕ)
    (v : ℂ) : ℂ :=
  (F (v ^ ((k:ℂ)⁻¹))) ^ k

theorem evenExteriorPowerQuotient_comp_pow
    (F : ℂ → ℂ) (k : ℕ) (hk : 0 < k)
    (hcov : EvenExteriorCovariant F k)
    (z : ℂ) (hz : z ∈ exteriorDisk) :
    evenExteriorPowerQuotient F k (z ^ k) = (F z) ^ k := by
  let w : ℂ := (z ^ k) ^ ((k:ℂ)⁻¹)
  have hrootpow : w ^ k = z ^ k := by
    simpa only [w] using
      Complex.cpow_nat_inv_pow (z ^ k) (by omega : k ≠ 0)
  change (F w) ^ k = (F z) ^ k
  exact evenExterior_power_fiber_eq F k hcov w z hz hrootpow

end SpringerLean

#print axioms SpringerLean.evenExterior_power_fiber_eq
#print axioms SpringerLean.evenExteriorPowerQuotient_comp_pow
