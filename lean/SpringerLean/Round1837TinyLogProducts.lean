import SpringerLean.Round1832RatePowerExpMonotonicity
import SpringerLean.Round1828ActualEndpointScalarRelations

namespace SpringerLean
set_option maxHeartbeats 1600000

theorem small_deficit_log_square_le_one {d : ℝ} (hd : 0 < d)
    (hL : 9 ≤ Real.log (2/d)) : d*(Real.log (2/d))^2 ≤ 1 := by
  let L := Real.log (2/d)
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hmono : L^4/(24 : ℝ) ≤ Real.exp L := by
    have hh := Finset.single_le_sum (s := Finset.range 5) (f := fun i : ℕ => L^i/(i.factorial : ℝ))
      (fun i _ => by positivity) (by norm_num : 4 ∈ Finset.range 5)
    norm_num only [Nat.factorial, Nat.cast_ofNat] at hh
    exact hh.trans (Real.sum_le_exp_of_nonneg hL0 5)
  have hsq : (48 : ℝ) ≤ L^2 := by dsimp [L]; nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg L)
  have hexp : 2*L^2 ≤ 2/d := by
    have he : Real.exp L=2/d := Real.exp_log (div_pos (by norm_num) hd)
    rw [he] at hmono
    nlinarith [hmul]
  have hh := (le_div_iff₀ hd).mp hexp
  dsimp [L] at hh ⊢
  nlinarith

/-- A logarithmic tangent at the explicit cutoff controls d log(2/d).
Only the previously proved coarse bound log(100m)<=m/20 is needed. -/
theorem tiny_deficit_log_product_base
    (k : ℕ) (hk : 751 ≤ k) {d : ℝ} (hd : 0 < d)
    (hsmall : d ≤ (3/100 : ℝ)/
      (((2*k-2 : ℕ) : ℝ)^2*Real.log (100*((2*k-2 : ℕ) : ℝ)))) :
    9*(k : ℝ)^2*d*Real.log (2/d) ≤ 1/4 := by
  let mn := 2*k-2
  let m := (mn : ℝ)
  let X := Real.log (100*m)
  let d₀ := (3/100 : ℝ)/(m^2*X)
  let L₀ := Real.log (2/d₀)
  have hmn : 1500 ≤ mn := by dsimp [mn]; omega
  have hm : 1500 ≤ m := by dsimp [m]; exact_mod_cast hmn
  have hm0 : 0 < m := by linarith
  have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
  have hmc : m=2*(k : ℝ)-2 := by
    dsimp [m,mn]
    rw [Nat.cast_sub (by omega : 2 ≤ 2*k)]
    push_cast
    ring
  have hX : 1 ≤ X := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2^2) (show (2 : ℝ)^2 ≤ 100*m by nlinarith)
    rw [Real.log_pow] at hh
    have ht := Real.log_two_gt_d9
    dsimp [X]
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hX0 : 0 < X := by linarith
  have hXup : X ≤ m/20 := large_log_hundred_mul_le hmn
  have hd₀ : 0 < d₀ := by dsimp [d₀]; positivity
  have hdd : d ≤ d₀ := hsmall
  have hden : 1 ≤ m^2*X := by
    have hh := mul_le_mul_of_nonneg_left hX (sq_nonneg m)
    nlinarith
  have hd₀up : d₀ ≤ 1/2 := by
    dsimp [d₀]
    apply (div_le_iff₀ (by positivity : 0 < m^2*X)).mpr
    nlinarith
  have hL₀ : 1 ≤ L₀ := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2^2)
      (show (2 : ℝ)^2 ≤ 2/d₀ from (le_div_iff₀ hd₀).mpr (by nlinarith))
    rw [Real.log_pow] at hh
    have ht := Real.log_two_gt_d9
    dsimp [L₀]
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hrat : 2/d₀=(200/3 : ℝ)*m^2*X := by dsimp [d₀]; field_simp; ring
  have hL₀up : L₀ ≤ 3*X := by
    have harg : 2/d₀ ≤ (100*m)^3 := by
      rw [hrat]
      have hh := mul_le_mul_of_nonneg_left hXup (show 0 ≤ (200/3 : ℝ)*m^2 by positivity)
      nlinarith [show 0 ≤ m^3 by positivity]
    have hh := Real.log_le_log (div_pos (by norm_num) hd₀) harg
    rw [Real.log_pow] at hh
    exact hh
  have hLpos : 0 < Real.log (2/d) := Real.log_pos ((one_lt_div hd).mpr (by linarith))
  have hlog := Real.log_le_sub_one_of_pos (div_pos hd₀ hd)
  have hlogs : Real.log (2/d)=L₀+Real.log (d₀/d) := by
    dsimp [L₀]
    rw [←Real.log_mul (by positivity : 2/d₀ ≠ 0) (by positivity : d₀/d ≠ 0)]
    congr 1
    field_simp
  have hprodlog : d*Real.log (2/d) ≤ d₀*L₀ := by
    have hh := mul_le_mul_of_nonneg_left hlog hd.le
    have heq : d*(d₀/d-1)=d₀-d := by field_simp
    rw [heq] at hh
    rw [hlogs]
    have hlin := mul_nonneg (sub_nonneg.mpr hdd) (sub_nonneg.mpr hL₀)
    nlinarith
  have hDL : m^2*(d*Real.log (2/d)) ≤ 9/100 := by
    have hh := mul_le_mul_of_nonneg_left (hprodlog.trans (mul_le_mul_of_nonneg_left hL₀up hd₀.le)) (sq_nonneg m)
    have heq : m^2*(d₀*(3*X))=(9/100 : ℝ) := by dsimp [d₀]; field_simp; ring
    rwa [heq] at hh
  have hratio : 81*(k : ℝ)^2 ≤ 25*m^2 := by rw [hmc]; nlinarith
  have hh := mul_le_mul_of_nonneg_right hratio (mul_nonneg hd.le hLpos.le)
  nlinarith [hDL]

end SpringerLean

#print axioms SpringerLean.small_deficit_log_square_le_one
#print axioms SpringerLean.tiny_deficit_log_product_base
