import SpringerLean.Round1520ClippedPowerConvex

namespace SpringerLean
noncomputable section

set_option maxHeartbeats 600000

/-- Curvature retained when the lower power is eight degrees lower. -/
def phasePowerRetention (j : ℕ) : ℝ :=
  ((j : ℝ)+2)*((j : ℝ)+1)/(((j : ℝ)+10)*((j : ℝ)+9))

theorem phasePowerRetention_bounds (j : ℕ) :
    0 ≤ phasePowerRetention j ∧ phasePowerRetention j ≤ 1 ∧
      phasePowerRetention j*((j : ℝ)+10) ≤ (j : ℝ)+2 := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold phasePowerRetention
  constructor
  · positivity
  constructor
  · apply (div_le_one (by positivity)).mpr
    nlinarith
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity :
        0 < ((j : ℝ)+10)*((j : ℝ)+9))).mpr
    nlinarith

theorem phasePowerRetention_ge_fortynine_fiftieths
    {j : ℕ} (hj : 1490 ≤ j) : (49 / 50 : ℝ) ≤ phasePowerRetention j := by
  have hj' : (1490 : ℝ) ≤ j := by exact_mod_cast hj
  unfold phasePowerRetention
  apply (le_div_iff₀ (by positivity :
    0 < ((j : ℝ)+10)*((j : ℝ)+9))).mpr
  nlinarith [sq_nonneg ((j : ℝ)-1490)]

def phaseLowerPolynomial (R : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  R^8*x^(j+2)-phasePowerRetention j*x^(j+10)

def phaseLowerPolynomialDeriv (R : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ((j : ℝ)+2)*R^8*x^(j+1)-
    phasePowerRetention j*((j : ℝ)+10)*x^(j+9)

theorem phaseLowerPolynomial_hasDerivAt (R x : ℝ) (j : ℕ) :
    HasDerivAt (phaseLowerPolynomial R j) (phaseLowerPolynomialDeriv R j x) x := by
  convert ((hasDerivAt_pow (j+2) x).const_mul (R^8)).sub
    ((hasDerivAt_pow (j+10) x).const_mul (phasePowerRetention j)) using 1
  · rfl
  · simp only [phaseLowerPolynomialDeriv, Nat.cast_add,
      Nat.cast_ofNat, show j+2-1=j+1 by omega, show j+10-1=j+9 by omega]
    ring

theorem phaseLowerPolynomial_second_hasDerivAt (R x : ℝ) (j : ℕ) :
    HasDerivAt (phaseLowerPolynomialDeriv R j)
      (((j : ℝ)+2)*((j : ℝ)+1)*x^j*(R^8-x^8)) x := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  convert ((hasDerivAt_pow (j+1) x).const_mul (((j : ℝ)+2)*R^8)).sub
    ((hasDerivAt_pow (j+9) x).const_mul
      (phasePowerRetention j*((j : ℝ)+10))) using 1
  · rfl
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat,
      show j+9-1=j+8 by omega]
    unfold phasePowerRetention
    rw [pow_add]
    have h10 : (j : ℝ)+10 ≠ 0 := by positivity
    have h9 : (j : ℝ)+9 ≠ 0 := by positivity
    field_simp
    <;> ring

/-- Exact nonnegative curvature on the lower-power branch. -/
theorem phaseLowerPolynomial_convexOn {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    ConvexOn ℝ (Set.Icc 0 R) (phaseLowerPolynomial R j) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 R)
    (show ContinuousOn (phaseLowerPolynomial R j) _ by
      unfold phaseLowerPolynomial; fun_prop)
    (fun x _ => (phaseLowerPolynomial_hasDerivAt R x j).hasDerivWithinAt)
    (fun x _ => (phaseLowerPolynomial_second_hasDerivAt R x j).hasDerivWithinAt)
  intro x hx
  have hx' : x ∈ Set.Icc 0 R := interior_subset hx
  have hx0 : 0 ≤ x := hx'.1
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  exact mul_nonneg (by positivity)
    (sub_nonneg.mpr (pow_le_pow_left₀ hx'.1 hx'.2 8))

theorem phaseLowerPolynomial_deriv_bounds {R x : ℝ} (hR : 0 ≤ R)
    (hx : 0 ≤ x) (hxR : x ≤ R) (j : ℕ) :
    0 ≤ phaseLowerPolynomialDeriv R j x ∧
      phaseLowerPolynomialDeriv R j x ≤ ((j : ℝ)+2)*R^(j+9) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk := phasePowerRetention_bounds j
  have hxp := pow_le_pow_left₀ hx hxR 8
  have hxp' := pow_le_pow_left₀ hx hxR (j+1)
  have hfac : 0 ≤ ((j : ℝ)+2)*R^8-
      phasePowerRetention j*((j : ℝ)+10)*x^8 := by
    nlinarith [mul_le_mul_of_nonneg_left hxp
      (mul_nonneg hk.1 (by positivity : 0 ≤ (j : ℝ)+10)),
      mul_le_mul_of_nonneg_right hk.2.2 (pow_nonneg hR 8)]
  constructor
  · have hh := mul_nonneg (pow_nonneg hx (j+1)) hfac
    convert hh using 1
    unfold phaseLowerPolynomialDeriv
    rw [show j+9=(j+1)+8 by omega, pow_add]
    ring
  · have hh := mul_le_mul_of_nonneg_left hxp'
      (show 0 ≤ ((j : ℝ)+2)*R^8 by positivity)
    have hn : 0 ≤ phasePowerRetention j*((j : ℝ)+10)*x^(j+9) :=
      mul_nonneg (mul_nonneg hk.1 (by positivity)) (pow_nonneg hx _)
    have hRpow : R^(j+9)=R^8*R^(j+1) := by
      rw [show j+9=8+(j+1) by omega, pow_add]
    unfold phaseLowerPolynomialDeriv
    rw [hRpow]
    nlinarith

theorem phaseLowerPolynomial_monotoneOn {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    MonotoneOn (phaseLowerPolynomial R j) (Set.Icc 0 R) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 R)
    (show ContinuousOn (phaseLowerPolynomial R j) _ by
      unfold phaseLowerPolynomial; fun_prop)
    (fun x _ => (phaseLowerPolynomial_hasDerivAt R x j).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx' : x ∈ Set.Icc 0 R := interior_subset hx
  rw [(phaseLowerPolynomial_hasDerivAt R x j).deriv]
  exact (phaseLowerPolynomial_deriv_bounds hR hx'.1 hx'.2 j).1

theorem phaseLowerPolynomialDeriv_monotoneOn {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    MonotoneOn (phaseLowerPolynomialDeriv R j) (Set.Icc 0 R) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 R)
    (show ContinuousOn (phaseLowerPolynomialDeriv R j) _ by
      unfold phaseLowerPolynomialDeriv; fun_prop)
    (fun x _ => (phaseLowerPolynomial_second_hasDerivAt R x j).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx' : x ∈ Set.Icc 0 R := interior_subset hx
  have hx0 : 0 ≤ x := hx'.1
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [(phaseLowerPolynomial_second_hasDerivAt R x j).deriv]
  exact mul_nonneg (by positivity)
    (sub_nonneg.mpr (pow_le_pow_left₀ hx'.1 hx'.2 8))

end
end SpringerLean

#print axioms SpringerLean.phaseLowerPolynomial_convexOn
#print axioms SpringerLean.phasePowerRetention_ge_fortynine_fiftieths
