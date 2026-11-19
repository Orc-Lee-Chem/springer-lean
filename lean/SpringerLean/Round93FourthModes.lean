import SpringerLean.Round92FaberFour

set_option maxHeartbeats 500000

namespace SpringerLean

open PowerSeries

/-- The first negative Laurent mode of the fourth Faber polynomial equals
four times the fourth forward coefficient. The factor and coefficient both
come from the same actual `F`. -/
theorem formalFaberFour_first_negative_mode (F : ℂ → ℂ) :
    let φ := formalExteriorPhi (exteriorFormalForward F)
    PowerSeries.coeff 5
      (φ ^ 4 -
        PowerSeries.C (4 * exteriorForwardCoeff F 1) *
          PowerSeries.X ^ 2 * φ ^ 2 -
        PowerSeries.C (4 * exteriorForwardCoeff F 2) *
          PowerSeries.X ^ 3 * φ -
        PowerSeries.C (4 * exteriorForwardCoeff F 3 -
          2 * (exteriorForwardCoeff F 1) ^ 2) * PowerSeries.X ^ 4) =
      4 * exteriorForwardCoeff F 4 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let φ := formalExteriorPhi f
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hφ : φ = 1 + PowerSeries.X ^ 2 * g := by
    change formalExteriorPhi f = _
    rw [formalExteriorPhi, hf]
    ring
  have hg0 : PowerSeries.coeff 0 g = b₁ := by
    simpa [g, f, b₁, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 1
  have hg0' : PowerSeries.constantCoeff g = b₁ := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hg0
  have hg1 : PowerSeries.coeff 1 g = b₂ := by
    simpa [g, f, b₂, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 2
  have hg3 : PowerSeries.coeff 3 g = exteriorForwardCoeff F 4 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 4
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  let S : PowerSeries ℂ :=
    φ ^ 4 - PowerSeries.C (4 * b₁) * PowerSeries.X ^ 2 * φ ^ 2 -
      PowerSeries.C (4 * b₂) * PowerSeries.X ^ 3 * φ -
      PowerSeries.C (4 * b₃ - 2 * b₁ ^ 2) * PowerSeries.X ^ 4
  have hA : S =
      1 + PowerSeries.X ^ 2 * (4 * g - PowerSeries.C (4 * b₁)) -
        PowerSeries.X ^ 3 * PowerSeries.C (4 * b₂) +
        PowerSeries.X ^ 4 *
          (6 * g ^ 2 - 2 * PowerSeries.C (4 * b₁) * g -
            PowerSeries.C (4 * b₃ - 2 * b₁ ^ 2)) -
        PowerSeries.X ^ 5 * (PowerSeries.C (4 * b₂) * g) +
        PowerSeries.X ^ 6 *
          (4 * g ^ 3 - PowerSeries.C (4 * b₁) * g ^ 2) +
        PowerSeries.X ^ 8 * g ^ 4 := by
    dsimp [S]
    rw [hφ]
    ring
  change PowerSeries.coeff 5 S = _
  rw [hA]
  simp [PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_C_mul, hsq1, hg0, hg1, hg3]
  have hterm : PowerSeries.coeff 1
      ((2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g) =
        8 * b₁ * b₂ := by
    have hc : (2 : PowerSeries ℂ) *
        PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
          PowerSeries.C (8 * b₁) := by
      have htwo : (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) := by
        calc
          (2 : PowerSeries ℂ) = 1 + 1 := by norm_num
          _ = PowerSeries.C (1 + 1 : ℂ) := by rw [map_add, map_one]
          _ = PowerSeries.C (2 : ℂ) := by norm_num
      calc
        (2 : PowerSeries ℂ) * PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
            PowerSeries.C (2 : ℂ) * PowerSeries.C (4 : ℂ) *
              PowerSeries.C b₁ := by rw [htwo]
        _ = PowerSeries.C (2 * 4 * b₁) := by rw [← map_mul, ← map_mul]
        _ = PowerSeries.C (8 * b₁) := by congr 1; ring
    rw [← mul_assoc, hc, PowerSeries.coeff_C_mul, hg1]
  have hzero : PowerSeries.coeff 1 ((PowerSeries.C b₁) ^ 2) = 0 := by
    simp [pow_two]
  rw [hg0', hterm, hzero]
  ring

/-- The first negative mode of the genuine fourth Faber boundary curve is
read from the same actual forward coefficient `b₄(F)`. -/
theorem fourthFaberFactor_actual_mode_five
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff
      (fun u : ℂ => (exteriorPhi F u) ^ 4 -
        4 * exteriorForwardCoeff F 1 * u ^ 2 * (exteriorPhi F u) ^ 2 -
        4 * exteriorForwardCoeff F 2 * u ^ 3 * exteriorPhi F u -
        (4 * exteriorForwardCoeff F 3 -
          2 * (exteriorForwardCoeff F 1) ^ 2) * u ^ 4) 5 =
      4 * exteriorForwardCoeff F 4 := by
  rw [← actualTaylorSeries_coeff,
    fourthFaberFactor_actualTaylorSeries F hc]
  exact formalFaberFour_first_negative_mode F

/-- Equality of two paper-class maps on the exterior disk preserves their
entire actual inverse Laurent coefficient sequence. This uses the verified
all-order inverse/residue identity and the independent forward-coefficient
uniqueness interface. -/
theorem exteriorInverseCoeff_eq_of_eqOn_exterior_all_orders
    (F G : ℂ → ℂ)
    (hcF : CenteredExteriorUnivalent F)
    (hcG : CenteredExteriorUnivalent G)
    (hFG : Set.EqOn F G exteriorDisk)
    (n : ℕ) (hn : 1 ≤ n) :
    exteriorInverseCoeff F n = exteriorInverseCoeff G n := by
  have hforward : exteriorFormalForward F = exteriorFormalForward G := by
    apply PowerSeries.ext
    intro j
    simpa only [exteriorFormalForward_coeff] using
      exteriorForwardCoeff_eq_of_eqOn_exterior F G hFG j
  have hres : exteriorFormalResidue F n = exteriorFormalResidue G n := by
    simp only [exteriorFormalResidue, hforward]
  have hF := exteriorInverseCoeff_mul_eq_formalResidue F hcF n hn
  have hG := exteriorInverseCoeff_mul_eq_formalResidue G hcG n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact mul_left_cancel₀ hn0 (hF.trans (hres.trans hG.symm))

/-- Every exterior-domain unit-slit equality witness attains the Catalan
value at every positive paper order through the actual inverse coefficient
interface, with no need to extend equality inside the unit disk. -/
theorem exteriorInverseCoeff_sharp_of_eqOn_slit_all_orders
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (a : ℂ) (ha : ‖a‖ = 1)
    (hFG : Set.EqOn F (slitMap a) exteriorDisk)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖exteriorInverseCoeff F (2 * n - 1)‖ =
      (catalan (n - 1) : ℝ) := by
  rw [exteriorInverseCoeff_eq_of_eqOn_exterior_all_orders F (slitMap a)
    hc (slitMap_centeredExteriorUnivalent a ha) hFG
    (2 * n - 1) (by omega)]
  exact slitMap_exteriorInverseCoeff_sharp_witness a ha n hn

/-- The second actual inverse coefficient consumes twice its squared norm
in the original exterior area theorem. -/
theorem exteriorInverseCoeff_two_sq_area_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    2 * ‖exteriorInverseCoeff F 2‖ ^ 2 ≤
      1 - ‖exteriorInverseCoeff F 1‖ ^ 2 := by
  have h := exteriorForwardCoeff_finite_area_tail F hc 2 (by omega)
  norm_num [Finset.sum_Icc_succ_top] at h
  rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc,
    exteriorInverseCoeff_two_eq_forwardCoeff_two F hc]
  exact h

/-- The exact n=4 numerical consequence of the remaining Schober diagonal
comparison. This is deliberately a conditional development lemma; its
premise must be proved from univalence before it is paper-level. -/
theorem exteriorInverseCoeff_seven_param_le_of_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hdiag : ‖exteriorInverseCoeff F 7‖ ≤ schoberActualDiagonal F 4) :
    ‖exteriorInverseCoeff F 7‖ ≤
      (3 + 7 * ‖exteriorForwardCoeff F 1‖ ^ 2) / 2 := by
  have harea := exteriorInverseCoeff_two_sq_area_le F hc
  have hrow := schoberActualDiagonal_four F hc
  rw [hrow] at hdiag
  rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] at hdiag harea
  linarith

/-- If the missing n=4 diagonal comparison is supplied, the manuscript
constant follows immediately from the already proved one-coefficient area
bound. The premise remains visible and is not a final theorem. -/
theorem exteriorInverseCoeff_seven_norm_le_five_of_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hdiag : ‖exteriorInverseCoeff F 7‖ ≤ schoberActualDiagonal F 4) :
    ‖exteriorInverseCoeff F 7‖ ≤ 5 := by
  have hβ := exteriorForwardCoeff_one_norm_le_of_finite_area F
    (fun N => exteriorForwardCoeff_finite_area F hc N)
  have hβ0 : 0 ≤ ‖exteriorForwardCoeff F 1‖ := norm_nonneg _
  have hparam := exteriorInverseCoeff_seven_param_le_of_diagonal F hc hdiag
  nlinarith

theorem exteriorInverseCoeff_seven_norm_lt_five_of_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hdiag : ‖exteriorInverseCoeff F 7‖ ≤ schoberActualDiagonal F 4)
    (hβ : ‖exteriorForwardCoeff F 1‖ < 1) :
    ‖exteriorInverseCoeff F 7‖ < 5 := by
  have hβ0 : 0 ≤ ‖exteriorForwardCoeff F 1‖ := norm_nonneg _
  have hparam := exteriorInverseCoeff_seven_param_le_of_diagonal F hc hdiag
  nlinarith [mul_pos (sub_pos.mpr hβ)
    (by positivity : 0 < 1 + ‖exteriorForwardCoeff F 1‖)]

/-- All n=4 equality algebra is finished under one visible comparison
inequality. This remains conditional until that inequality is derived from
the original function class; its type is intentionally not a paper audit. -/
theorem exteriorInverseCoeff_seven_norm_eq_five_iff_slit_of_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hdiag : ‖exteriorInverseCoeff F 7‖ ≤ schoberActualDiagonal F 4) :
    (‖exteriorInverseCoeff F 7‖ = 5 ↔
      ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) := by
  constructor
  · intro hEq
    have hβle := exteriorForwardCoeff_one_norm_le_of_finite_area F
      (fun N => exteriorForwardCoeff_finite_area F hc N)
    have hβeq : ‖exteriorForwardCoeff F 1‖ = 1 := by
      by_contra hne
      have hβlt : ‖exteriorForwardCoeff F 1‖ < 1 := lt_of_le_of_ne hβle hne
      have hstrict := exteriorInverseCoeff_seven_norm_lt_five_of_diagonal
        F hc hdiag hβlt
      linarith
    have hB1 : ‖exteriorInverseCoeff F 1‖ = 1 := by
      rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc]
      exact hβeq
    exact (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).mp hB1
  · rintro ⟨a, ha, hFG⟩
    have hsharp := exteriorInverseCoeff_sharp_of_eqOn_slit_all_orders
      F hc a ha hFG 4 (by omega)
    simpa only [Nat.reduceMul, Nat.reduceSub, catalan_three,
      Nat.cast_ofNat] using hsharp

end SpringerLean
