import SpringerLean.Round1878ActualSixthMomentSlit

open Filter
open scoped Topology

namespace SpringerLean

set_option maxHeartbeats 2000000

/-- The square completion used in the revised sixth-moment proof. -/
theorem sixthMoment_strong_square_identity (x a b : ℝ) :
    (5 + 6 * x ^ 2) * (2 * a ^ 2 + 4 * b ^ 2) -
      9 * a ^ 2 - 3 * (2 * x * a + b) ^ 2 =
      (a - 6 * x * b) ^ 2 + (17 - 12 * x ^ 2) * b ^ 2 := by
  ring

theorem sixthMoment_strong_scalar_margin
    {x a b g y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g) (hy : 0 ≤ y)
    (harea : 2 * a ^ 2 + 4 * b ^ 2 ≤ 1 - x ^ 2)
    (hgrunsky : g ≤ (1 + x ^ 2) / 2)
    (htriangle : y ≤ 2 * x * a + b) :
    2 + 12 * x ^ 2 + 9 * a ^ 2 + 6 * g ^ 2 + 3 * y ^ 2 ≤
      20 - 7 * (1 - x ^ 2) - (9 / 2) * (1 - x ^ 2) ^ 2 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hcoeff : 0 ≤ 17 - 12 * x ^ 2 := by linarith
  have hnonneg : 0 ≤ 2 * x * a + b := by positivity
  have hy2 : y ^ 2 ≤ (2 * x * a + b) ^ 2 := by nlinarith
  have hg2 : g ^ 2 ≤ ((1 + x ^ 2) / 2) ^ 2 := by nlinarith
  have hid := sixthMoment_strong_square_identity x a b
  have hbudget : 9 * a ^ 2 + 3 * y ^ 2 ≤
      (5 + 6 * x ^ 2) * (2 * a ^ 2 + 4 * b ^ 2) := by
    nlinarith [sq_nonneg (a - 6 * x * b), mul_nonneg hcoeff (sq_nonneg b)]
  have hmul := mul_le_mul_of_nonneg_left harea (by positivity : 0 ≤ 5 + 6 * x ^ 2)
  nlinarith

theorem rescaleExterior_boundary_six_strong_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun z : ℂ => ‖rescaleExterior r F z‖ ^ 6) 0 1 ≤
      20 - 7 * (1 - ‖exteriorForwardCoeff (rescaleExterior r F) 1‖ ^ 2) -
        (9 / 2) * (1 - ‖exteriorForwardCoeff (rescaleExterior r F) 1‖ ^ 2) ^ 2 := by
  let G := rescaleExterior r F
  have hG : CenteredExteriorUnivalent G :=
    rescaleExterior_centeredExteriorUnivalent F hc hr0 hr1
  let b₁ := exteriorForwardCoeff G 1
  let b₂ := exteriorForwardCoeff G 2
  let b₃ := exteriorForwardCoeff G 3
  let b₄ := exteriorForwardCoeff G 4
  have hnorm1 : ‖b₁‖ ≤ 1 := by
    simpa only [b₁, exteriorInverseCoeff_one_eq_forwardCoeff_one G hG] using
      exteriorInverseCoeff_one_norm_le G hG
  have harea := exteriorForwardCoeff_finite_area G hG 4
  have hset : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  rw [hset] at harea
  norm_num at harea
  have hbudget : 2 * ‖b₂‖ ^ 2 + 4 * ‖b₄‖ ^ 2 ≤ 1 - ‖b₁‖ ^ 2 := by
    dsimp only [b₁, b₂, b₄]
    nlinarith [sq_nonneg ‖exteriorForwardCoeff G 3‖]
  have hginv := exteriorInverseCoeff_three_norm_le_half_one_add_sq G hG
  rw [exteriorInverseCoeff_three_eq_forward G hG] at hginv
  have hgrunsky : ‖b₃ + b₁ ^ 2‖ ≤ (1 + ‖b₁‖ ^ 2) / 2 := by
    simpa only [b₁, b₃] using hginv
  have htriangle : ‖b₄ + 2 * b₁ * b₂‖ ≤ 2 * ‖b₁‖ * ‖b₂‖ + ‖b₄‖ := by
    have h := norm_add_le b₄ (2 * b₁ * b₂)
    norm_num [norm_mul] at h
    nlinarith
  have hscalar := sixthMoment_strong_scalar_margin
    (x := ‖b₁‖) (a := ‖b₂‖) (b := ‖b₄‖)
    (g := ‖b₃ + b₁ ^ 2‖) (y := ‖b₄ + 2 * b₁ * b₂‖)
    (norm_nonneg _) hnorm1 (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) hbudget hgrunsky htriangle
  have hfinite := rescaleExterior_boundary_six_le_coeff F hc hr0 hr1
  dsimp only [G, b₁, b₂, b₃, b₄] at hscalar
  exact hfinite.trans hscalar

theorem actualBoundaryRadialMoment_six_strong_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 6 ≤
      20 - 7 * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) -
        (9 / 2) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) ^ 2 := by
  have hleft : Tendsto
      (fun s : ℝ => Real.circleAverage
        (fun z : ℂ => ‖rescaleExterior s F z‖ ^ 6) 0 1)
      (𝓝[<] (1 : ℝ)) (𝓝 (actualBoundaryRadialMoment F 6)) := by
    simpa only [Real.rpow_ofNat] using
      actualBoundaryRadialMoment_rescale_circle_tendsto F hc 6 (by norm_num)
  have hright : Tendsto
      (fun s : ℝ => 20 - 7 *
        (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2) -
        (9 / 2) * (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2) ^ 2)
      (𝓝[<] (1 : ℝ))
      (𝓝 (20 - 7 * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) -
        (9 / 2) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) ^ 2)) := by
    have hcont : Continuous
        (fun s : ℝ => 20 - 7 *
          (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2) -
          (9 / 2) * (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2) ^ 2) := by
      fun_prop
    simpa only [Complex.ofReal_one, one_pow, one_mul] using
      hcont.continuousAt.tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
  have hh := rescaleExterior_boundary_six_strong_margin F hc hs.1 hs.2
  rw [rescaleExterior_forwardCoeff F hc hs.1] at hh
  simpa only [Nat.reduceAdd] using hh

end SpringerLean

namespace SpringerLean.PaperStatementsAudit

/-- Revised sixth-moment bound on the actual radial trace, with the complete
fixed-order equality classification. -/
theorem theorem_9_1_p6_actual_radial_strong
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 6 ≤
        20 - 7 * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) -
          (9 / 2) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) ^ 2 ∧
      (actualBoundaryRadialMoment F 6 = slitRadialMomentConstant 6 ↔
        ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) := by
  refine ⟨actualBoundaryRadialMoment_six_strong_margin F hc, ?_⟩
  exact (theorem_9_1_p6_actual_radial F hc).2

end SpringerLean.PaperStatementsAudit

#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p6_actual_radial_strong
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p6_actual_radial_strong
