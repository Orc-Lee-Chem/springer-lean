import SpringerLean.Round2019EvenExteriorPowerQuotient
import SpringerLean.Round1859OddBoundarySecondMoment

namespace SpringerLean

private theorem even_phase_pow_neg_one (k : ℕ) (hk : 0 < k) :
    (Complex.exp (((Real.pi / (k:ℝ) : ℝ):ℂ)*Complex.I)) ^ k = -1 := by
  rw [← Complex.exp_nat_mul]
  have hkC : (k:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hangle :
      (k:ℂ)*(((Real.pi / (k:ℝ) : ℝ):ℂ)*Complex.I) =
        (Real.pi:ℂ)*Complex.I := by
    push_cast
    field_simp
  rw [hangle, Complex.exp_pi_mul_I]

theorem evenExteriorPowerQuotient_odd
    (F : ℂ → ℂ) (k : ℕ) (hk : 0 < k)
    (hcov : EvenExteriorCovariant F k)
    (v : ℂ) (hv : v ∈ exteriorDisk) :
    evenExteriorPowerQuotient F k (-v) =
      -evenExteriorPowerQuotient F k v := by
  let ζ : ℂ := Complex.exp (((Real.pi / (k:ℝ) : ℝ):ℂ)*Complex.I)
  let z : ℂ := v ^ ((k:ℂ)⁻¹)
  have hζk : ζ ^ k = -1 := even_phase_pow_neg_one k hk
  have hζ2k : ζ ^ (2*k) = 1 := by
    rw [mul_comm 2 k, pow_mul, hζk]
    norm_num
  have hζnorm : ‖ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hζ2k (by omega)
  have hzpow : z ^ k = v := by
    simpa only [z] using Complex.cpow_nat_inv_pow v (by omega : k ≠ 0)
  have hz : z ∈ exteriorDisk := by
    have hvgt : 1 < ‖v‖ := hv
    have hnormpow : ‖z‖ ^ k = ‖v‖ := by
      rw [← norm_pow, hzpow]
    have hpowgt : 1 < ‖z‖ ^ k := by rw [hnormpow]; exact hvgt
    exact (one_lt_pow_iff_of_nonneg (norm_nonneg z)
      (by omega : k ≠ 0)).mp hpowgt
  have hζz : ζ*z ∈ exteriorDisk := by
    change 1 < ‖ζ*z‖
    rw [norm_mul, hζnorm, one_mul]
    exact hz
  have hminus : (ζ*z) ^ k = -v := by
    rw [mul_pow, hζk, hzpow, neg_one_mul]
  calc
    evenExteriorPowerQuotient F k (-v) =
        evenExteriorPowerQuotient F k ((ζ*z)^k) := by rw [hminus]
    _ = (F (ζ*z)) ^ k :=
      evenExteriorPowerQuotient_comp_pow F k hk hcov (ζ*z) hζz
    _ = (ζ*F z) ^ k := by rw [hcov ζ z hζ2k hz]
    _ = -(F z)^k := by rw [mul_pow, hζk, neg_one_mul]
    _ = -evenExteriorPowerQuotient F k v := by
      rw [← hzpow, evenExteriorPowerQuotient_comp_pow F k hk hcov z hz]

/-- Once the algebraic quotient is proved to be a centered exterior
univalent map, its oddness yields the actual second-moment margin. -/
theorem evenExteriorPowerQuotient_secondMoment_margin
    (F : ℂ → ℂ) (k : ℕ) (hk : 0 < k)
    (hcov : EvenExteriorCovariant F k)
    (hc : CenteredExteriorUnivalent (evenExteriorPowerQuotient F k)) :
    actualBoundaryRadialMoment (evenExteriorPowerQuotient F k) 2 ≤
      2 - (2/3:ℝ) *
        (1 - ‖exteriorForwardCoeff (evenExteriorPowerQuotient F k) 1‖^2) :=
  actualBoundaryRadialMoment_two_odd_margin
    (evenExteriorPowerQuotient F k) hc
    (evenExteriorPowerQuotient_odd F k hk hcov)

end SpringerLean

#print axioms SpringerLean.evenExteriorPowerQuotient_odd
#print axioms SpringerLean.evenExteriorPowerQuotient_secondMoment_margin
