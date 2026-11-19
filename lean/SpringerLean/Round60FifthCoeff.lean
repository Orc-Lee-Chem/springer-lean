import SpringerLean.Round59ThirdCoeffRigidity
import SpringerLean.LowOrder

namespace SpringerLean

open PowerSeries

private theorem coeff_two_sq_centered (g : PowerSeries ℂ) :
    PowerSeries.coeff 2 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 2 g +
        (PowerSeries.coeff 1 g) ^ 2 := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

theorem exteriorFormalResidue_five (F : ℂ → ℂ) :
    exteriorFormalResidue F 5 =
      5 * (exteriorForwardCoeff F 5 +
        4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
        2 * (exteriorForwardCoeff F 2) ^ 2 +
        2 * (exteriorForwardCoeff F 1) ^ 3) := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hphi : formalExteriorPhi f = 1 + PowerSeries.X ^ 2 * g := by
    rw [formalExteriorPhi, hf]
    ring
  have hpow : (1 + PowerSeries.X ^ 2 * g) ^ 5 =
      1 + 5 * (PowerSeries.X ^ 2 * g) +
        10 * (PowerSeries.X ^ 2 * g) ^ 2 +
        10 * (PowerSeries.X ^ 2 * g) ^ 3 +
        5 * (PowerSeries.X ^ 2 * g) ^ 4 +
        (PowerSeries.X ^ 2 * g) ^ 5 := by ring
  have hs1 : PowerSeries.coeff 6 (PowerSeries.X ^ 2 * g) =
      PowerSeries.coeff 4 g := by
    simpa using PowerSeries.coeff_X_pow_mul g 2 4
  have hs2 : PowerSeries.coeff 6 ((PowerSeries.X ^ 2 * g) ^ 2) =
      PowerSeries.coeff 2 (g ^ 2) := by
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul (g ^ 2) 4 2 using 1 <;> ring
  have hs3 : PowerSeries.coeff 6 ((PowerSeries.X ^ 2 * g) ^ 3) =
      PowerSeries.coeff 0 (g ^ 3) := by
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul (g ^ 3) 6 0 using 1 <;> ring
  have hs4 : PowerSeries.coeff 6 ((PowerSeries.X ^ 2 * g) ^ 4) = 0 := by
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 4) 8 6 using 1 <;> ring_nf <;> norm_num
  have hs5 : PowerSeries.coeff 6 ((PowerSeries.X ^ 2 * g) ^ 5) = 0 := by
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 5) 10 6 using 1 <;> ring_nf <;> norm_num
  have h0 : PowerSeries.coeff 0 (g ^ 3) =
      (PowerSeries.coeff 0 g) ^ 3 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff]
  have hg0 : PowerSeries.coeff 0 g = exteriorForwardCoeff F 1 := by
    simpa [g, f, PowerSeries.coeff_mk] using
      (exteriorFormalForward_coeff F 1)
  have hg1 : PowerSeries.coeff 1 g = exteriorForwardCoeff F 2 := by
    simpa [g, f, PowerSeries.coeff_mk] using
      (exteriorFormalForward_coeff F 2)
  have hg2 : PowerSeries.coeff 2 g = exteriorForwardCoeff F 3 := by
    simpa [g, f, PowerSeries.coeff_mk] using
      (exteriorFormalForward_coeff F 3)
  have hg4 : PowerSeries.coeff 4 g = exteriorForwardCoeff F 5 := by
    simpa [g, f, PowerSeries.coeff_mk] using
      (exteriorFormalForward_coeff F 5)
  change PowerSeries.coeff 6 ((formalExteriorPhi f) ^ 5) = _
  rw [hphi, hpow]
  simp only [map_add, PowerSeries.coeff_natCast_mul,
    PowerSeries.coeff_ofNat_mul, hs1, hs2, hs3, hs4, hs5]
  rw [coeff_two_sq_centered, h0, hg0, hg1, hg2, hg4]
  simp
  ring

theorem exteriorInverseCoeff_five_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 5 =
      exteriorForwardCoeff F 5 +
        4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
        2 * (exteriorForwardCoeff F 2) ^ 2 +
        2 * (exteriorForwardCoeff F 1) ^ 3 := by
  have h := exteriorInverseCoeff_mul_eq_formalResidue F hc 5 (by omega)
  rw [exteriorFormalResidue_five] at h
  exact mul_left_cancel₀ (by norm_num : (5 : ℂ) ≠ 0) h

theorem exteriorInverseCoeff_slitMap_five
    (a : ℂ) (ha : ‖a‖ = 1) :
    exteriorInverseCoeff (slitMap a) 5 = 2 * a ^ 3 := by
  rw [exteriorInverseCoeff_slitMap]
  simpa [catalan_two, mul_comm] using slitTaylorCoeff_odd a ha 2


/-- The finite area theorem with its first five terms read from the actual forward map. -/
theorem exteriorForwardCoeff_area_five
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorForwardCoeff F 1‖ ^ 2 +
      2 * ‖exteriorForwardCoeff F 2‖ ^ 2 +
      3 * ‖exteriorForwardCoeff F 3‖ ^ 2 +
      4 * ‖exteriorForwardCoeff F 4‖ ^ 2 +
      5 * ‖exteriorForwardCoeff F 5‖ ^ 2 ≤ 1 := by
  simpa [Finset.sum_Icc_succ_top, add_assoc] using exteriorForwardCoeff_finite_area F hc 5

/-- A fifth-coefficient bound valid for every actual centered exterior univalent map. -/
theorem exteriorInverseCoeff_five_norm_param_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 5‖ ≤
      (21 / 20 : ℝ) + ‖exteriorForwardCoeff F 1‖ ^ 2 / 3 +
        2 * ‖exteriorForwardCoeff F 1‖ ^ 3 := by
  let b := exteriorForwardCoeff F
  let x : ℝ := ‖b 1‖
  let y : ℝ := ‖b 3‖
  let t : ℝ := ‖b 5‖
  have harea : x ^ 2 + 2 * ‖b 2‖ ^ 2 + 3 * y ^ 2 +
      4 * ‖b 4‖ ^ 2 + 5 * t ^ 2 ≤ 1 := by
    simpa [b, x, y, t] using exteriorForwardCoeff_area_five F hc
  have htri : ‖exteriorInverseCoeff F 5‖ ≤
      t + 4 * x * y + 2 * ‖b 2‖ ^ 2 + 2 * x ^ 3 := by
    rw [exteriorInverseCoeff_five_eq_forward F hc]
    change ‖b 5 + 4 * b 1 * b 3 + 2 * b 2 ^ 2 + 2 * b 1 ^ 3‖ ≤ _
    calc
      _ ≤ ‖b 5 + 4 * b 1 * b 3 + 2 * b 2 ^ 2‖ +
          ‖2 * b 1 ^ 3‖ := norm_add_le _ _
      _ ≤ ‖b 5 + 4 * b 1 * b 3‖ + ‖2 * b 2 ^ 2‖ +
          ‖2 * b 1 ^ 3‖ := by
            gcongr
            exact norm_add_le _ _
      _ ≤ ‖b 5‖ + ‖4 * b 1 * b 3‖ + ‖2 * b 2 ^ 2‖ +
          ‖2 * b 1 ^ 3‖ := by
            gcongr
            exact norm_add_le _ _
      _ = t + 4 * x * y + 2 * ‖b 2‖ ^ 2 + 2 * x ^ 3 := by
            simp [norm_pow, x, y, t]
  have hxy : 4 * x * y - 3 * y ^ 2 ≤ 4 * x ^ 2 / 3 := by
    nlinarith [sq_nonneg (3 * y - 2 * x)]
  have ht : t - 5 * t ^ 2 ≤ (1 / 20 : ℝ) := by
    nlinarith [sq_nonneg (10 * t - 1)]
  have h4 : 0 ≤ ‖b 4‖ ^ 2 := sq_nonneg _
  dsimp [x, b] at *
  nlinarith

/-- The area-only argument is strictly sharp below the exact cutoff 8/11. -/
theorem exteriorInverseCoeff_five_norm_lt_two_of_firstCoeff_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hx : ‖exteriorForwardCoeff F 1‖ ≤ (8 / 11 : ℝ)) :
    ‖exteriorInverseCoeff F 5‖ < 2 := by
  let x : ℝ := ‖exteriorForwardCoeff F 1‖
  have hx0 : 0 ≤ x := norm_nonneg _
  have hx' : x ≤ (8 / 11 : ℝ) := hx
  have hx2 : x ^ 2 ≤ (8 / 11 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hx0 hx' 2
  have hx3 : x ^ 3 ≤ (8 / 11 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hx0 hx' 3
  have hb := exteriorInverseCoeff_five_norm_param_bound F hc
  change ‖exteriorInverseCoeff F 5‖ ≤ (21 / 20 : ℝ) + x ^ 2 / 3 + 2 * x ^ 3 at hb
  nlinarith


/-- The fifth actual inverse coefficient respects equality of exterior maps. -/
theorem exteriorInverseCoeff_five_eq_of_eqOn_exterior
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hG : CenteredExteriorUnivalent G)
    (hFG : Set.EqOn F G exteriorDisk) :
    exteriorInverseCoeff F 5 = exteriorInverseCoeff G 5 := by
  rw [exteriorInverseCoeff_five_eq_forward F hF,
    exteriorInverseCoeff_five_eq_forward G hG]
  rw [exteriorForwardCoeff_eq_of_eqOn_exterior F G hFG 1,
    exteriorForwardCoeff_eq_of_eqOn_exterior F G hFG 2,
    exteriorForwardCoeff_eq_of_eqOn_exterior F G hFG 3,
    exteriorForwardCoeff_eq_of_eqOn_exterior F G hFG 5]

/-- Every unit slit has the fifth-order equality value, with the actual inverse sign. -/
theorem exteriorInverseCoeff_five_norm_eq_two_of_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (a : ℂ) (ha : ‖a‖ = 1)
    (hFG : Set.EqOn F (slitMap a) exteriorDisk) :
    ‖exteriorInverseCoeff F 5‖ = 2 := by
  rw [exteriorInverseCoeff_five_eq_of_eqOn_exterior F (slitMap a)
    hc (slitMap_centeredExteriorUnivalent a ha) hFG,
    exteriorInverseCoeff_slitMap_five a ha]
  simp [norm_mul, norm_pow, ha]

/-- The first-coefficient saturation endpoint of the k=3 problem. -/
theorem exteriorInverseCoeff_five_endpoint
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hx : ‖exteriorForwardCoeff F 1‖ = 1) :
    ∃ a : ℂ, ‖a‖ = 1 ∧
      Set.EqOn F (slitMap a) exteriorDisk ∧
      ‖exteriorInverseCoeff F 5‖ = 2 := by
  have hB1 : ‖exteriorInverseCoeff F 1‖ = 1 := by
    rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc]
    exact hx
  obtain ⟨a, ha, hFG⟩ :=
    (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).mp hB1
  exact ⟨a, ha, hFG, exteriorInverseCoeff_five_norm_eq_two_of_slit F hc a ha hFG⟩

/-- Area data alone allow this non-univalent fifth-order coefficient pattern. -/
theorem fifth_area_only_counterexample :
    (4 / 5 : ℝ) ^ 2 + 3 * (1 / 3 : ℝ) ^ 2 = 73 / 75 ∧
    4 * (4 / 5 : ℝ) * (1 / 3 : ℝ) +
      2 * (4 / 5 : ℝ) ^ 3 = 784 / 375 ∧
    (2 : ℝ) < 784 / 375 := by
  norm_num


/-- The rational cutoff leaves the exact strict margin 347/79860. -/
theorem fifth_param_bound_cutoff_margin :
    (21 / 20 : ℝ) + (8 / 11 : ℝ) ^ 2 / 3 +
      2 * (8 / 11 : ℝ) ^ 3 = 2 - 347 / 79860 := by
  norm_num

end SpringerLean