import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

namespace SpringerLean
open Set

/-- The exact weighted AM--GM inequality used to show that the real-power
interpolation test has nonpositive derivative on the unit interval. -/
theorem interpolation_power_amgm
    {x θ : ℝ} (hx : 0 ≤ x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    x ^ θ ≤ 1 - θ + θ * x := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 - θ) (w₂ := θ) (p₁ := 1) (p₂ := x)
    (by linarith) hθ0 (by norm_num) hx (by ring)
  simpa using h

/-- Pointwise secant bound for the derivative powers of the adjacent-even
interpolation test. The real parameter `a` will be specialized to 4 or 6. -/
theorem interpolation_rpow_derivative_secant
    {a θ t : ℝ} (ht : 0 < t) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    t ^ (a + 2 * θ - 1) ≤
      (1 - θ) * t ^ (a - 1) + θ * t ^ (a + 1) := by
  have ham := interpolation_power_amgm (x := t ^ 2) (θ := θ)
    (sq_nonneg t) hθ0 hθ1
  have hmul := mul_le_mul_of_nonneg_left ham (Real.rpow_nonneg ht.le (a - 1))
  have hp : t ^ (a + 2 * θ - 1) = t ^ (a - 1) * (t ^ 2) ^ θ := by
    calc
      _ = t ^ ((a - 1) + 2 * θ) := by congr 1; ring
      _ = t ^ (a - 1) * t ^ (2 * θ) := Real.rpow_add ht _ _
      _ = t ^ (a - 1) * (t ^ 2) ^ θ := by
        rw [Real.rpow_mul ht.le, Real.rpow_two]
  have hq : t ^ (a + 1) = t ^ (a - 1) * t ^ 2 := by
    calc
      _ = t ^ ((a - 1) + 2) := by congr 1; ring
      _ = t ^ (a - 1) * t ^ (2 : ℝ) := Real.rpow_add ht _ _
      _ = t ^ (a - 1) * t ^ 2 := by rw [Real.rpow_two]
  rw [hp,hq]
  calc
    _ ≤ t ^ (a - 1) * (1 - θ + θ * t ^ 2) := hmul
    _ = (1 - θ) * t ^ (a - 1) + θ * (t ^ (a - 1) * t ^ 2) := by ring

/-- The real-power test used between adjacent even exponents. -/
noncomputable def interpolationPowerTest (a θ t : ℝ) : ℝ :=
  let p := a + 2 * θ
  t ^ p - (p * (1 - θ) / a) * t ^ a -
    (p * θ / (a + 2)) * t ^ (a + 2)

theorem interpolationPowerTest_antitoneOn
    {a θ : ℝ} (ha : 4 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    AntitoneOn (interpolationPowerTest a θ) (Set.Icc (0 : ℝ) 1) := by
  let p := a + 2 * θ
  have ha0 : a ≠ 0 := by linarith
  have hab0 : a + 2 ≠ 0 := by linarith
  have hpc : 0 ≤ p := by dsimp [p]; linarith
  have hac : 0 ≤ a := by linarith
  have habc : 0 ≤ a + 2 := by linarith
  have hcont : Continuous (interpolationPowerTest a θ) := by
    change Continuous (fun t : ℝ =>
      t ^ p - (p * (1 - θ) / a) * t ^ a -
        (p * θ / (a + 2)) * t ^ (a + 2))
    fun_prop
  have hderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt (interpolationPowerTest a θ)
        (p * t ^ (p - 1) - p * (1 - θ) * t ^ (a - 1) -
          p * θ * t ^ (a + 1)) t := by
    have h1 := Real.hasDerivAt_rpow_const (p := p) (Or.inl ht.ne')
    have h2 := Real.hasDerivAt_rpow_const (p := a) (Or.inl ht.ne')
    have h3 := Real.hasDerivAt_rpow_const (p := a + 2) (Or.inl ht.ne')
    have h := (h1.sub (h2.const_mul (p * (1 - θ) / a))).sub
      (h3.const_mul (p * θ / (a + 2)))
    change HasDerivAt
      (((fun x : ℝ => x ^ p) - fun x => (p * (1 - θ) / a) * x ^ a) -
        fun x => (p * θ / (a + 2)) * x ^ (a + 2))
      (p * t ^ (p - 1) - p * (1 - θ) * t ^ (a - 1) -
        p * θ * t ^ (a + 1)) t
    convert h using 1
    field_simp [ha0,hab0]
    ring
  have hnonpos (t : ℝ) (ht : 0 < t) :
      deriv (interpolationPowerTest a θ) t ≤ 0 := by
    rw [(hderiv t ht).deriv]
    have hsec := interpolation_rpow_derivative_secant
      (a := a) (θ := θ) ht hθ0 hθ1
    have hmul := mul_le_mul_of_nonneg_left hsec hpc
    dsimp [p] at hmul ⊢
    nlinarith
  apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1)
    hcont.continuousOn
  · intro t ht
    have hti : 0 < t := by
      have : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
      exact this.1
    exact (hderiv t hti).differentiableAt.differentiableWithinAt
  · intro t ht
    have hti : 0 < t := by
      have : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
      exact this.1
    exact hnonpos t hti

end SpringerLean

#check @SpringerLean.interpolation_power_amgm
#print axioms SpringerLean.interpolation_power_amgm
#check @SpringerLean.interpolation_rpow_derivative_secant
#print axioms SpringerLean.interpolation_rpow_derivative_secant
#check @SpringerLean.interpolationPowerTest_antitoneOn
#print axioms SpringerLean.interpolationPowerTest_antitoneOn
