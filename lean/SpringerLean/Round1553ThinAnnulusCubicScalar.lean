import SpringerLean.Round1552ActualAnnulusPeakGain

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The constants in the annulus area estimate agree exactly with the
paper's normalized variable D=md. -/
theorem thinAnnulus_normalization_identity
    {m : ℕ} (hm : 1500 ≤ m) {d u : ℝ} (hd0 : 0 < d) :
    let D := (m:ℝ)*d
    ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*
      ((9/(50*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*d^2*Real.sqrt d*
        (2:ℝ)^(m-1:ℕ)*(u/(m:ℝ))) =
      (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D*u := by
  dsimp only
  have hm0 : (0:ℝ) < m := by
    have h : 0 < m := by omega
    exact_mod_cast h
  have htwo : (2:ℝ)^m = (2:ℝ)^(m-1:ℕ)*2 := by
    conv_lhs => rw [show m=m-1+1 by omega,pow_succ]
  have hsqrt : Real.sqrt ((m:ℝ)*d) =
      Real.sqrt (m:ℝ)*Real.sqrt d := Real.sqrt_mul hm0.le d
  rw [htwo,hsqrt]
  have hpow0 : (2:ℝ)^(m-1:ℕ) ≠ 0 := by positivity
  field_simp
  ring

/-- In the actual range 0<md≤3/20, the full outer annulus's
normalised scalar lower bound is strictly larger than D³/30. -/
theorem thinAnnulus_cubic_scalar_margin
    {m : ℕ} (hm : 1500 ≤ m) {d : ℝ}
    (hd0 : 0 < d) (hD : (m:ℝ)*d ≤ 3/20) :
    let D := (m:ℝ)*d
    let a := 1-Real.sqrt d/16
    D^3/30 <
      (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D*
        (1-a^m) := by
  dsimp only
  let D : ℝ := (m:ℝ)*d
  let a : ℝ := 1-Real.sqrt d/16
  have hmR : (1500:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hD0 : 0 < D := mul_pos hm0 hd0
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.2 hD0
  have hrad := thinAnnulus_radial_mass_small hm hd0 hD
  change (4/3:ℝ)*Real.sqrt D ≤ 1-a^m at hrad
  have hfac : (99/100:ℝ) ≤ 1-1/(m:ℝ) := by
    apply (le_sub_iff_add_le).2
    have hmul : (1:ℝ)/(m:ℝ) ≤ 1/1500 := by
      apply (div_le_iff₀ hm0).2
      nlinarith [hmR]
    linarith
  have hpi : Real.pi < (22/7:ℝ) := by
    have hp := Real.pi_lt_d20
    norm_num at hp ⊢
    linarith
  have hpiInv : (7/22:ℝ) < Real.pi⁻¹ := by
    have hp0 := Real.pi_pos
    rw [inv_eq_one_div]
    apply (div_lt_div_iff₀ (by norm_num : (0:ℝ)<22) hp0).2
    nlinarith [hpi]
  have hcoef : (1/30:ℝ) <
      (9/100:ℝ)*Real.pi⁻¹*(1-1/(m:ℝ))*(4/3) := by
    have hp1 := mul_lt_mul_of_pos_left hpiInv (by norm_num : (0:ℝ)<9/100)
    have hp2 := mul_le_mul_of_nonneg_left hfac
      (show 0 ≤ (9/100:ℝ)*Real.pi⁻¹ by positivity)
    nlinarith [hp1,hp2,Real.pi_pos]
  have hsquare : D^2*Real.sqrt D*Real.sqrt D=D^3 := by
    calc
      D^2*Real.sqrt D*Real.sqrt D = D^2*(Real.sqrt D)^2 := by ring
      _ = D^2*D := by rw [Real.sq_sqrt hD0.le]
      _ = D^3 := by ring
  have hprod := mul_le_mul_of_nonneg_left hrad
    (show 0 ≤ (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D by
      have : 0 ≤ 1-1/(m:ℝ) := by linarith [hfac]
      positivity)
  have hD3 : 0 < D^3 := pow_pos hD0 _
  have hcoefScaled := mul_lt_mul_of_pos_right hcoef hD3
  have hcoefNorm :
      (9/100:ℝ)*Real.pi⁻¹*(1-1/(m:ℝ))*(4/3)*D^3 =
      (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D*
        ((4/3:ℝ)*Real.sqrt D) := by
    rw [←hsquare]
    ring
  change D^3/30 <
    (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D*(1-a^m)
  calc
    D^3/30 = (1/30:ℝ)*D^3 := by ring
    _ < (9/100:ℝ)*Real.pi⁻¹*(1-1/(m:ℝ))*(4/3)*D^3 := hcoefScaled
    _ = (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D*
          ((4/3:ℝ)*Real.sqrt D) := hcoefNorm
    _ ≤ _ := hprod

end SpringerLean

#print axioms SpringerLean.thinAnnulus_normalization_identity
#print axioms SpringerLean.thinAnnulus_cubic_scalar_margin
