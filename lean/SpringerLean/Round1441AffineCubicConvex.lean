import SpringerLean.Round1440MovingArcCubicCorrection
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace SpringerLean
set_option maxHeartbeats 250000

/-- Subtracting the cubic correction associated with the exponential
curvature tangent leaves a convex function on the moving deficit arc. -/
theorem refinedAffineSmoothPower_cubic_corrected_convexOn
    (n : ℕ) (hn : 1501 ≤ n)
    {W d : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hd0 : 0 < d) (hnd : (n:ℝ)*d < 1) :
    let b : ℝ := Real.sqrt (3*d)
    let A : ℝ := (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*
      (2:ℝ)^(n-2)
    let B : ℝ := (n:ℝ)/2
    let s₀ : ℝ := 2*b^2/5
    ConvexOn ℝ (Set.Icc 0 (b^2))
      (fun s => refinedAffineSmoothPower W n s -
        A*Real.exp (-B*s₀)*movingArcCubicQ B s₀ s) := by
  dsimp
  let b : ℝ := Real.sqrt (3*d)
  let A : ℝ := (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*
    (2:ℝ)^(n-2)
  let B : ℝ := (n:ℝ)/2
  let s₀ : ℝ := 2*b^2/5
  let C : ℝ := A*Real.exp (-B*s₀)
  let f : ℝ → ℝ := refinedAffineSmoothPower W n
  let q : ℝ → ℝ := movingArcCubicQ B s₀
  let G : ℝ → ℝ := fun s => f s-C*q s
  let D : Set ℝ := Set.Icc 0 (b^2)
  have hbSq : b^2=3*d := Real.sq_sqrt (by positivity)
  have hb0 : 0 ≤ b^2 := sq_nonneg b
  have hcont : ContinuousOn G D := by
    dsimp [G,f,q,refinedAffineSmoothPower,movingArcCubicQ]
    fun_prop
  have hDeriv : ∀ s ∈ interior D,
      HasDerivAt G (deriv f s-C*deriv q s) s := by
    intro s hs
    have hf : HasDerivAt f (deriv f s) s := by
      have hC2 : ContDiffAt ℝ 2 f s := by
        unfold f refinedAffineSmoothPower refinedAffineU refinedAffineV
        fun_prop
      exact (hC2.differentiableAt (by norm_num)).hasDerivAt
    have hq := movingArcCubicQ_hasDerivAt B s₀ s
    have hq' : HasDerivAt q (deriv q s) s := by
      convert hq using 1
      rw [movingArcCubicQ_deriv]
    have hsub := hf.sub (hq'.const_mul C)
    convert hsub using 1
  have hDeriv2 : ∀ s ∈ interior D,
      HasDerivAt (fun y => deriv f y-C*deriv q y)
        (deriv (deriv f) s-C*deriv (deriv q) s) s := by
    intro s hs
    have hF2 : ContDiffAt ℝ 2 f s := by
      unfold f refinedAffineSmoothPower refinedAffineU refinedAffineV
      fun_prop
    have hQ2 : ContDiffAt ℝ 2 q s := by
      unfold q movingArcCubicQ
      fun_prop
    have hf : HasDerivAt (deriv f) (deriv (deriv f) s) s :=
      ((hF2.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasDerivAt
    have hq : HasDerivAt (deriv q) (deriv (deriv q) s) s :=
      ((hQ2.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasDerivAt
    exact hf.sub (hq.const_mul C)
  have hNonneg : ∀ s ∈ interior D,
      0 ≤ deriv (deriv f) s-C*deriv (deriv q) s := by
    intro s hs
    have hs' : s ∈ Set.Ioo 0 (b^2) := by
      simpa [D,interior_Icc] using hs
    have hns : (n:ℝ)*s ≤ 3 := by
      have hn0 : (0:ℝ)≤n := by exact_mod_cast (Nat.zero_le n)
      have hle := mul_le_mul_of_nonneg_left hs'.2.le hn0
      rw [hbSq] at hle
      nlinarith [hnd]
    have hcurv := refinedAffineSmoothPower_curvature_tangent
      n hn hW0 hW hs'.1.le hns (s₀ := s₀)
    change C*(1+B*(s₀-s)) ≤ deriv (deriv f) s at hcurv
    have hq := movingArcCubicQ_second_deriv B s₀ s
    change deriv (deriv q) s=1+B*(s₀-s) at hq
    rw [hq]
    linarith
  change ConvexOn ℝ D G
  exact convexOn_of_hasDerivWithinAt2_nonneg
    (convex_Icc _ _) hcont
    (fun s hs => (hDeriv s hs).hasDerivWithinAt)
    (fun s hs => (hDeriv2 s hs).hasDerivWithinAt)
    hNonneg

end SpringerLean

#print axioms SpringerLean.refinedAffineSmoothPower_cubic_corrected_convexOn
