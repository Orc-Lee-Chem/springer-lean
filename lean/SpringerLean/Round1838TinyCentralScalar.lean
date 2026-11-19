import SpringerLean.Round1837TinyLogProducts

namespace SpringerLean
set_option maxHeartbeats 1800000

theorem tiny_central_geometric (k : ℕ) (hk : 751 ≤ k) :
    15*(9 : ℝ)^6*(k : ℝ)^12*(1/4 : ℝ)^(k-7) < 1 := by
  have hstep : (752/751 : ℝ)^12*(1/4 : ℝ) < 1 := by norm_num
  induction k,hk using Nat.le_induction with
  | base =>
    norm_num only [Nat.cast_ofNat,Nat.reduceSub]
    have hp : (1/4 : ℝ)^744 ≤ (1/4 : ℝ)^100 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num : 100 ≤ 744)
    have hh : 15*(9 : ℝ)^6*(751 : ℝ)^12*(1/4 : ℝ)^100 < 1 := by norm_num
    have hle := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ 15*(9 : ℝ)^6*(751 : ℝ)^12 by positivity)
    have hfin := hle.trans_lt hh
    convert hfin using 1 <;> norm_num
  | succ k hk ih =>
    have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
    have hscale : (k : ℝ)+1 ≤ (752/751 : ℝ)*k := by linarith
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ)+1) hscale 12
    have hindex : k+1-7=(k-7)+1 := by omega
    rw [Nat.cast_add,Nat.cast_one,hindex,pow_succ (1/4 : ℝ) (k-7)]
    calc
      _ ≤ 15*(9 : ℝ)^6*((752/751 : ℝ)*k)^12*((1/4 : ℝ)^(k-7)*(1/4)) := by gcongr
      _ = (15*(9 : ℝ)^6*(k : ℝ)^12*(1/4 : ℝ)^(k-7))*((752/751 : ℝ)^12*(1/4)) := by ring
      _ ≤ 15*(9 : ℝ)^6*(k : ℝ)^12*(1/4 : ℝ)^(k-7) := by
        have hnn : 0 ≤ 15*(9 : ℝ)^6*(k : ℝ)^12*(1/4 : ℝ)^(k-7) := by positivity
        nlinarith [mul_nonneg hnn (sub_nonneg.mpr hstep.le)]
      _ < 1 := ih

/-- Six powers absorb d^3 using d log(2/d)^2<=1; every other
power is at most 1/4. This avoids differentiating the tiny ratio. -/
theorem tiny_central_cost_lt_cubic
    (k : ℕ) (hk : 751 ≤ k) {d : ℝ} (hd : 0 < d)
    (hL : 9 ≤ Real.log (2/d))
    (hsmall : d ≤ (3/100 : ℝ)/
      (((2*k-2 : ℕ) : ℝ)^2*Real.log (100*((2*k-2 : ℕ) : ℝ)))) :
    let m := ((2*k-2 : ℕ) : ℝ)
    15*(m*Real.sqrt m)*(3*(k : ℝ)*Real.sqrt (d*Real.log (2/d)))^(2*k-2) < (m*d)^3 := by
  let mn := 2*k-2
  let m := (mn : ℝ)
  let L := Real.log (2/d)
  let J := 9*(k : ℝ)^2
  let B := J*d*L
  have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : (1500 : ℝ) ≤ m := by dsimp [m,mn]; exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hm0 : 0 < m := by linarith
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hE : 0 ≤ d*L := mul_nonneg hd.le hL0.le
  have hB0 : 0 ≤ B := by dsimp [B,J]; positivity
  have hB : B ≤ 1/4 := tiny_deficit_log_product_base k hk hd hsmall
  have hlog := small_deficit_log_square_le_one hd hL
  have hroot : (Real.sqrt (d*L))^2=d*L := Real.sq_sqrt hE
  have hcentral : (3*(k : ℝ)*Real.sqrt (d*L))^mn=B^(k-1) := by
    have hi : mn=2*(k-1) := by dsimp [mn]; omega
    rw [hi,pow_mul]
    congr 1
    rw [mul_pow,mul_pow,hroot]
    dsimp [B,J]
    ring
  have hC : (3*(k : ℝ)*Real.sqrt (d*L))^mn ≤
      (1/4 : ℝ)^(k-7)*J^6*d^3 := by
    rw [hcentral,show k-1=(k-7)+6 by omega,pow_add]
    have hpow := pow_le_pow_left₀ hB0 hB (k-7)
    have hsmallpow := pow_le_pow_left₀ (show 0 ≤ d*L^2 by positivity) hlog 3
    have hh := mul_le_mul_of_nonneg_right hpow (show 0 ≤ B^6 by positivity)
    have heq : (1/4 : ℝ)^(k-7)*B^6=(1/4 : ℝ)^(k-7)*J^6*d^3*(d*L^2)^3 := by dsimp [B]; ring
    rw [heq] at hh
    have hcoef : 0 ≤ (1/4 : ℝ)^(k-7)*J^6*d^3 := by positivity
    have hlast := mul_le_mul_of_nonneg_left hsmallpow hcoef
    norm_num only [one_pow,mul_one] at hlast
    exact hh.trans hlast
  have hNpos : 0 < m*Real.sqrt m*d^3 := by positivity
  have hgeom := mul_lt_mul_of_pos_left (tiny_central_geometric k hk) hNpos
  have hsm : Real.sqrt m ≤ m := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hN : m*Real.sqrt m ≤ m^3 := by
    have hh := mul_le_mul_of_nonneg_left hsm hm0.le
    nlinarith [mul_nonneg (sq_nonneg m) (show 0 ≤ m-1 by linarith)]
  change 15*(m*Real.sqrt m)*(3*(k : ℝ)*Real.sqrt (d*L))^mn < (m*d)^3
  calc
    _ ≤ 15*(m*Real.sqrt m)*((1/4 : ℝ)^(k-7)*J^6*d^3) :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    _ = (m*Real.sqrt m*d^3)*(15*(9 : ℝ)^6*(k : ℝ)^12*(1/4 : ℝ)^(k-7)) := by dsimp [J]; ring
    _ < m*Real.sqrt m*d^3 := by simpa only [mul_one] using hgeom
    _ ≤ m^3*d^3 := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by ring

end SpringerLean

#print axioms SpringerLean.tiny_central_cost_lt_cubic
