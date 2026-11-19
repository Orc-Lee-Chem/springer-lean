import SpringerLean.Round2038EvenBLPCurvatureOnSupport
import Mathlib.Analysis.Convex.Deriv

namespace SpringerLean

noncomputable def evenStarBLPCorrectedLog (k : ℕ) (x : ℝ) : ℝ :=
  Real.log (1 + Real.exp ((x-Real.log 2)/(k:ℝ))) -
    Real.exp (2*x)/(64*(k:ℝ)^2)

private theorem evenStarBLPExp_hasDerivAt
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp ((t-Real.log 2)/(k:ℝ)))
      (Real.exp ((x-Real.log 2)/(k:ℝ))/(k:ℝ)) x := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  convert (Real.hasDerivAt_exp ((x-Real.log 2)/(k:ℝ))).comp x
    (((hasDerivAt_id x).sub_const (Real.log 2)).div_const (k:ℝ)) using 1
  · ext t; rfl
  · simp [div_eq_mul_inv]

private theorem evenStarBLPLog_hasDerivAt
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      Real.log (1+Real.exp ((t-Real.log 2)/(k:ℝ))))
      (Real.exp ((x-Real.log 2)/(k:ℝ)) /
        ((k:ℝ)*(1+Real.exp ((x-Real.log 2)/(k:ℝ))))) x := by
  let y := Real.exp ((x-Real.log 2)/(k:ℝ))
  have hy : 0 < 1+y := by dsimp [y]; positivity
  have hinner : HasDerivAt (fun t : ℝ =>
      1+Real.exp ((t-Real.log 2)/(k:ℝ)))
      (y/(k:ℝ)) x := by
    convert (hasDerivAt_const x (1:ℝ)).add
      (evenStarBLPExp_hasDerivAt k hk x) using 1
    simp [y]
  convert (Real.hasDerivAt_log (ne_of_gt hy)).comp x hinner using 1
  · ext t; rfl
  · have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    simp only [y]
    field_simp

private theorem evenStarBLPCorrection_hasDerivAt
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (2*t)/(64*(k:ℝ)^2))
      (Real.exp (2*x)/(32*(k:ℝ)^2)) x := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  convert ((Real.hasDerivAt_exp (2*x)).comp x
    ((hasDerivAt_const x (2:ℝ)).mul (hasDerivAt_id x))).div_const
      (64*(k:ℝ)^2) using 1
  · ext t; rfl
  · simp; ring

theorem evenStarBLPCorrectedLog_hasDerivAt
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    HasDerivAt (evenStarBLPCorrectedLog k)
      (Real.exp ((x-Real.log 2)/(k:ℝ)) /
        ((k:ℝ)*(1+Real.exp ((x-Real.log 2)/(k:ℝ)))) -
       Real.exp (2*x)/(32*(k:ℝ)^2)) x := by
  exact (evenStarBLPLog_hasDerivAt k hk x).sub
    (evenStarBLPCorrection_hasDerivAt k hk x)

private theorem evenStarBLPFirstTerm_hasDerivAt
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      Real.exp ((t-Real.log 2)/(k:ℝ)) /
        ((k:ℝ)*(1+Real.exp ((t-Real.log 2)/(k:ℝ)))))
      (Real.exp ((x-Real.log 2)/(k:ℝ)) /
        ((k:ℝ)^2*(1+Real.exp ((x-Real.log 2)/(k:ℝ)))^2)) x := by
  let y : ℝ := Real.exp ((x-Real.log 2)/(k:ℝ))
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hy0 : 1+y ≠ 0 := by dsimp [y]; positivity
  have hnum := evenStarBLPExp_hasDerivAt k hk x
  have hden : HasDerivAt (fun t : ℝ =>
      (k:ℝ)*(1+Real.exp ((t-Real.log 2)/(k:ℝ)))) y x := by
    convert (hasDerivAt_const x (k:ℝ)).mul
      ((hasDerivAt_const x (1:ℝ)).add hnum) using 1
    simp [y]; field_simp
  have hden0 : (k:ℝ)*(1+y) ≠ 0 := mul_ne_zero hk0 hy0
  convert hnum.div hden hden0 using 1
  simp only [y]
  field_simp
  ring

private theorem evenStarBLPCorrectionDeriv_hasDerivAt
    (k : ℕ) (_hk : 0 < k) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (2*t)/(32*(k:ℝ)^2))
      (Real.exp (2*x)/(16*(k:ℝ)^2)) x := by
  convert ((Real.hasDerivAt_exp (2*x)).comp x
    ((hasDerivAt_const x (2:ℝ)).mul (hasDerivAt_id x))).div_const
      (32*(k:ℝ)^2) using 1
  · ext t; rfl
  · simp; ring

theorem evenStarBLPCorrectedLog_deriv_hasDerivAt
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    HasDerivAt (deriv (evenStarBLPCorrectedLog k))
      (Real.exp ((x-Real.log 2)/(k:ℝ)) /
        ((k:ℝ)^2*(1+Real.exp ((x-Real.log 2)/(k:ℝ)))^2) -
      Real.exp (2*x)/(16*(k:ℝ)^2)) x := by
  let g : ℝ → ℝ := fun t =>
    Real.exp ((t-Real.log 2)/(k:ℝ)) /
      ((k:ℝ)*(1+Real.exp ((t-Real.log 2)/(k:ℝ)))) -
    Real.exp (2*t)/(32*(k:ℝ)^2)
  have hfirst : deriv (evenStarBLPCorrectedLog k) = g := by
    funext t
    exact (evenStarBLPCorrectedLog_hasDerivAt k hk t).deriv
  rw [hfirst]
  exact (evenStarBLPFirstTerm_hasDerivAt k hk x).sub
    (evenStarBLPCorrectionDeriv_hasDerivAt k hk x)

theorem evenStarBLPCorrectedLog_deriv2
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    (deriv^[2] (evenStarBLPCorrectedLog k)) x =
      Real.exp ((x-Real.log 2)/(k:ℝ)) /
        ((k:ℝ)^2*(1+Real.exp ((x-Real.log 2)/(k:ℝ)))^2) -
      Real.exp (2*x)/(16*(k:ℝ)^2) := by
  rw [Function.iterate_succ_apply, Function.iterate_one]
  exact (evenStarBLPCorrectedLog_deriv_hasDerivAt k hk x).deriv

theorem evenStarBLPCorrectedLog_convexOn_support
    (k : ℕ) (hk : 0 < k) :
    ConvexOn ℝ (Set.Iic (Real.log 2)) (evenStarBLPCorrectedLog k) := by
  apply convexOn_of_deriv2_nonneg' (convex_Iic _)
  · intro x hx
    exact (evenStarBLPCorrectedLog_hasDerivAt k hk x).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (evenStarBLPCorrectedLog_deriv_hasDerivAt k hk x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [evenStarBLPCorrectedLog_deriv2 k hk x]
    exact sub_nonneg.mpr (evenStar_log_kernel_curvature_actual_x k hk x hx)

end SpringerLean
