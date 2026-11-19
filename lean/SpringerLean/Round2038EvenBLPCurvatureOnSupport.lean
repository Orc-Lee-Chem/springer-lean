import SpringerLean.Round2037EvenPowerImageBLPHypotheses
import SpringerLean.Round1976EvenStarCurvature

namespace SpringerLean

/-- The scalar curvature comparison on the actual logarithmic support
interval used in the even-star BLP argument. -/
theorem evenStar_log_kernel_curvature_on_support
    (k : ℕ) (hk : 0 < k) (x : ℝ) (hx : x ≤ Real.log 2) :
    let y := Real.exp ((x-Real.log 2)/(k:ℝ))
    y^(2*k)/4 ≤ y/(1+y)^2 := by
  let y : ℝ := Real.exp ((x-Real.log 2)/(k:ℝ))
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast hk
  have harg : (x-Real.log 2)/(k:ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hkpos.le
  have hy1 : y ≤ 1 := by
    change Real.exp ((x-Real.log 2)/(k:ℝ)) ≤ 1
    calc
      Real.exp ((x-Real.log 2)/(k:ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.mpr harg
      _ = 1 := Real.exp_zero
  exact evenStar_log_kernel_curvature k hk y hy0 hy1

theorem evenStar_support_exp_power_identity
    (k : ℕ) (hk : 0 < k) (x : ℝ) :
    (Real.exp ((x-Real.log 2)/(k:ℝ)))^(2*k) =
      Real.exp (2*x)/4 := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have harg : ((2*k:ℕ):ℝ)*((x-Real.log 2)/(k:ℝ)) =
      2*x-2*Real.log 2 := by
    push_cast
    field_simp
  have htwo : Real.exp (2*Real.log 2)=4 := by
    rw [show 2*Real.log 2 = Real.log 2 + Real.log 2 by ring,
      Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [← Real.exp_nat_mul, harg, Real.exp_sub, htwo]

theorem evenStar_log_kernel_curvature_actual_x
    (k : ℕ) (hk : 0 < k) (x : ℝ) (hx : x ≤ Real.log 2) :
    let y := Real.exp ((x-Real.log 2)/(k:ℝ))
    Real.exp (2*x)/(16*(k:ℝ)^2) ≤
      y/((k:ℝ)^2*(1+y)^2) := by
  let y : ℝ := Real.exp ((x-Real.log 2)/(k:ℝ))
  have hcurv : y^(2*k)/4 ≤ y/(1+y)^2 :=
    evenStar_log_kernel_curvature_on_support k hk x hx
  have hid : y^(2*k) = Real.exp (2*x)/4 :=
    evenStar_support_exp_power_identity k hk x
  have hkpos : 0 < (k:ℝ)^2 := by positivity
  have hdiv := div_le_div_of_nonneg_right hcurv hkpos.le
  calc
    Real.exp (2*x)/(16*(k:ℝ)^2) =
        (y^(2*k)/4)/((k:ℝ)^2) := by rw [hid]; ring
    _ ≤ (y/(1+y)^2)/((k:ℝ)^2) := hdiv
    _ = y/((k:ℝ)^2*(1+y)^2) := by
      have hy0 : (1+y)^2 ≠ 0 := by positivity
      have hk0 : (k:ℝ)^2 ≠ 0 := ne_of_gt hkpos
      field_simp

end SpringerLean
