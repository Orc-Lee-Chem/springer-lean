import SpringerLean.Round1392SmoothPowerC2
import Mathlib.Analysis.Convex.Deriv

namespace SpringerLean

/-- Subtracting half the verified curvature times `x²` leaves a
convex function on the entire short projection interval. -/
theorem coarseSmoothPower_sub_quadratic_convexOn
    (n : ℕ) (hn : 1501 ≤ n) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let m : ℝ := (2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5
    ConvexOn ℝ (Set.Icc (2*Real.cos b) 2)
      (fun x : ℝ => coarseSmoothRadius x^n - (m/2)*x^2) := by
  dsimp
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  let m : ℝ := (2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5
  let f : ℝ → ℝ := fun x => coarseSmoothRadius x^n
  let G : ℝ → ℝ := fun x => f x-(m/2)*x^2
  let D : Set ℝ := Set.Icc (2*Real.cos b) 2
  have hcont : ContinuousOn G D := by
    intro x hx
    have hxA : x < 41/20 := by dsimp [D] at hx; linarith [hx.2]
    have hf := (coarseSmoothPower_contDiffAt_two n hxA).continuousAt
    have hq : ContinuousAt (fun y : ℝ => (m/2)*y^2) x := by fun_prop
    exact (hf.sub hq).continuousWithinAt
  have hDeriv : ∀ x ∈ interior D,
      HasDerivAt G (deriv f x-m*x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (2*Real.cos b) 2 := by
      simpa [D, interior_Icc] using hx
    have hxA : x < 41/20 := by linarith [hx'.2]
    have hf : HasDerivAt f (deriv f x) x :=
      (coarseSmoothPower_contDiffAt_two n hxA).differentiableAt
        (by norm_num) |>.hasDerivAt
    have hq := ((hasDerivAt_id x).pow 2).const_mul (m/2)
    have hsub := hf.sub hq
    convert hsub using 1
    · funext y; dsimp [G]
    · simp only [id_eq, Nat.cast_ofNat, pow_one, mul_one]
      ring
  have hDeriv2 : ∀ x ∈ interior D,
      HasDerivAt (fun y => deriv f y-m*y)
        (deriv (deriv f) x-m) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (2*Real.cos b) 2 := by
      simpa [D, interior_Icc] using hx
    have hxA : x < 41/20 := by linarith [hx'.2]
    have hf : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
      (coarseSmoothPower_deriv_differentiableAt n hxA).hasDerivAt
    have hq := (hasDerivAt_id x).const_mul m
    have hsub := hf.sub hq
    convert hsub using 1
    · funext y; dsimp
    · simp
  have hNonneg : ∀ x ∈ interior D,
      0 ≤ deriv (deriv f) x-m := by
    intro x hx
    have hx' : x ∈ Set.Ioo (2*Real.cos b) 2 := by
      simpa [D, interior_Icc] using hx
    have hcurv := coarseSmoothPower_arc_curvature_lower n hn hx'.1.le hx'.2.le
    dsimp [m,f,b] at *
    linarith
  change ConvexOn ℝ D G
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hcont
    (fun x hx => (hDeriv x hx).hasDerivWithinAt)
    (fun x hx => (hDeriv2 x hx).hasDerivWithinAt)
    hNonneg

end SpringerLean

#print axioms SpringerLean.coarseSmoothPower_sub_quadratic_convexOn
