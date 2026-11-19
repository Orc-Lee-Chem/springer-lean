import SpringerLean.Round1825ReferenceTailIntegralMajorant

namespace SpringerLean
set_option maxHeartbeats 1300000

/-- Uniform reference-tail bound, with the same m^(3/2) normalization
as the actual endpoint savings. -/
theorem alignedPhaseReferenceCost_excess_le_twelve
    (k : ℕ) (hk : 751 ≤ k) (a : ℝ) (ha : 6 ≤ a)
    (hau : a ≤ ((2*k-2 : ℕ) : ℝ)/5) :
    let m := ((2*k-2 : ℕ) : ℝ)
    m*Real.sqrt m*(alignedPhaseReferenceCost k a-comparisonPositiveDiskMoment (2*k-2)) ≤
      12*Real.exp (-a)*Real.sqrt a/m := by
  let mn := 2*k-2
  let m := (mn : ℝ)
  let c := 1-a/m
  let σ := (m-8)/(m-a)
  let ρ := ((mn-8 : ℕ) : ℝ)/c
  have hmn : 1500 ≤ mn := by dsimp [mn]; omega
  have hm : 1500 ≤ m := by dsimp [m]; exact_mod_cast hmn
  have hm0 : 0 < m := by linarith
  have ha0 : 0 < a := by linarith
  have hau' : a ≤ m/5 := hau
  have hc : 0 < c := by
    dsimp [c]
    have hh : a/m ≤ 1/5 := (div_le_iff₀ hm0).mpr (by linarith)
    linarith
  have hden : 0 < m-a := by linarith
  have hσ : 0 < σ := div_pos (by linarith) hden
  have hcast : ((mn-8 : ℕ) : ℝ)=m-8 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 8 ≤ mn),Nat.cast_ofNat]
  have hrel : a+m*c=m := by dsimp [c]; field_simp; ring
  have hρ : ρ=σ*m := by
    dsimp [ρ,σ,c]
    rw [hcast]
    field_simp
    <;> ring
  have hi := reference_tail_integral_majorant ha0 hm0 hc hrel (mn-8) (by omega : 1 ≤ mn-8)
  have hid := alignedPhaseReferenceCost_excess_integral k hk a ha hau
  change alignedPhaseReferenceCost k a-comparisonPositiveDiskMoment mn=
    (2*Real.pi⁻¹)*(∫ x in Set.Ioo 0 c, Real.sqrt (1-x^2)*(x^(mn-8)*(c^8-x^8))) at hid
  have hp := mul_le_mul_of_nonneg_left hi (show 0 ≤ m*Real.sqrt m*(2*Real.pi⁻¹) by positivity)
  have hsqrt : (Real.sqrt m)^2=m := Real.sq_sqrt hm0.le
  have hsqrta : (Real.sqrt a)^2=a := Real.sq_sqrt ha0.le
  have hraw :
      m*Real.sqrt m*(2*Real.pi⁻¹)*
        ((8*c^(mn-8+7)*Real.sqrt (2/m))*
          (Real.sqrt a/(((mn-8 : ℕ) : ℝ)/c)^2+m/(Real.sqrt a*(((mn-8 : ℕ) : ℝ)/c)^3)))=
      (16*Real.sqrt 2/(Real.pi*m))*c^(mn-1)*
        (Real.sqrt a/σ^2+1/(Real.sqrt a*σ^3)) := by
    rw [show mn-8+7=mn-1 by omega]
    change m*Real.sqrt m*(2*Real.pi⁻¹)*
      ((8*c^(mn-1)*Real.sqrt (2/m))*(Real.sqrt a/ρ^2+m/(Real.sqrt a*ρ^3)))=_
    rw [hρ,Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    <;> nlinarith [hsqrt]
  have hcost : m*Real.sqrt m*(alignedPhaseReferenceCost k a-comparisonPositiveDiskMoment mn) ≤
      (16*Real.sqrt 2/(Real.pi*m))*c^(mn-1)*(Real.sqrt a/σ^2+1/(Real.sqrt a*σ^3)) := by
    rw [hraw] at hp
    rw [hid]
    nlinarith
  have hcoef := reference_tail_coefficient_lt_twelve mn hmn a ha hau
  change (16*Real.sqrt 2/Real.pi)*(c^(mn-1)*Real.exp a)*(1/σ^2+1/(a*σ^3)) < 12 at hcoef
  have he : Real.exp a*Real.exp (-a)=1 := by rw [Real.exp_neg]; field_simp
  have hα : 0 < Real.exp (-a)*Real.sqrt a/m := by positivity
  have hh := mul_lt_mul_of_pos_right hcoef hα
  have hnormalize :
      ((16*Real.sqrt 2/Real.pi)*(c^(mn-1)*Real.exp a)*(1/σ^2+1/(a*σ^3)))*
        (Real.exp (-a)*Real.sqrt a/m)=
      (16*Real.sqrt 2/(Real.pi*m))*c^(mn-1)*(Real.sqrt a/σ^2+1/(Real.sqrt a*σ^3)) := by
    field_simp
    simp only [hsqrta]
    linear_combination (σ*a+1)*a*he
  rw [hnormalize] at hh
  convert hcost.trans hh.le using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.alignedPhaseReferenceCost_excess_le_twelve
