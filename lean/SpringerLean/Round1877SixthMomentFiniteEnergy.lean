import SpringerLean.Round1866FourthMomentFiniteEnergy
import SpringerLean.Round376ThirdQuantitative
import SpringerLean.Round1867ActualRescaledMomentLimit

open PowerSeries
open Filter
open scoped Topology

namespace SpringerLean

set_option maxHeartbeats 2000000

/-- The five coefficients needed for the six-power radial energy. -/
theorem formalPhi_cube_first_coefficients (F : ℂ → ℂ) :
    let φ := formalExteriorPhi (exteriorFormalForward F)
    PowerSeries.coeff 0 (φ ^ 3) = 1 ∧
    PowerSeries.coeff 1 (φ ^ 3) = 0 ∧
    PowerSeries.coeff 2 (φ ^ 3) = 3 * exteriorForwardCoeff F 1 ∧
    PowerSeries.coeff 3 (φ ^ 3) = 3 * exteriorForwardCoeff F 2 ∧
    PowerSeries.coeff 4 (φ ^ 3) =
      3 * (exteriorForwardCoeff F 3 + (exteriorForwardCoeff F 1) ^ 2) ∧
    PowerSeries.coeff 5 (φ ^ 3) =
      3 * (exteriorForwardCoeff F 4 +
        2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2) := by
  let φ := formalExteriorPhi (exteriorFormalForward F)
  have h0 : PowerSeries.coeff 0 φ = 1 := by simp [φ, formalExteriorPhi]
  have hsucc (j : ℕ) : PowerSeries.coeff (j + 1) φ = exteriorForwardCoeff F j := by
    simp [φ, formalExteriorPhi, PowerSeries.coeff_succ_X_mul, exteriorFormalForward_coeff]
  have h1 : PowerSeries.coeff 1 φ = 0 := by
    simpa only [Nat.zero_add, exteriorForwardCoeff_zero] using hsucc 0
  have h2 : PowerSeries.coeff 2 φ = exteriorForwardCoeff F 1 := hsucc 1
  have h3 : PowerSeries.coeff 3 φ = exteriorForwardCoeff F 2 := hsucc 2
  have h4 : PowerSeries.coeff 4 φ = exteriorForwardCoeff F 3 := hsucc 3
  have h5 : PowerSeries.coeff 5 φ = exteriorForwardCoeff F 4 := hsucc 4
  change PowerSeries.coeff 0 (φ ^ 3) = 1 ∧
    PowerSeries.coeff 1 (φ ^ 3) = 0 ∧
    PowerSeries.coeff 2 (φ ^ 3) = 3 * exteriorForwardCoeff F 1 ∧
    PowerSeries.coeff 3 (φ ^ 3) = 3 * exteriorForwardCoeff F 2 ∧
    PowerSeries.coeff 4 (φ ^ 3) =
      3 * (exteriorForwardCoeff F 3 + (exteriorForwardCoeff F 1) ^ 2) ∧
    PowerSeries.coeff 5 (φ ^ 3) =
      3 * (exteriorForwardCoeff F 4 +
        2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2)
  norm_num [pow_succ, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    h0, h1, h2, h3, h4, h5] <;> ring <;> simp

/-- Paper equation (rad-area) at the sixth moment, before its Grunsky and
area-theorem estimates. -/
theorem sixthMoment_finite_energy_eq (F : ℂ → ℂ) :
    (∑ d ∈ Finset.range 6, (2 - (d : ℝ) / 3) *
      ‖PowerSeries.coeff d (formalExteriorPhi (exteriorFormalForward F) ^ 3)‖ ^ 2) =
      2 + 12 * ‖exteriorForwardCoeff F 1‖ ^ 2 +
      9 * ‖exteriorForwardCoeff F 2‖ ^ 2 +
      6 * ‖exteriorForwardCoeff F 3 + (exteriorForwardCoeff F 1) ^ 2‖ ^ 2 +
      3 * ‖exteriorForwardCoeff F 4 +
        2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2‖ ^ 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := formalPhi_cube_first_coefficients F
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, norm_mul] <;> ring

theorem rescaleExterior_boundary_six_le_coeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.circleAverage (fun ζ : ℂ => ‖rescaleExterior s F ζ‖ ^ 6) 0 1 ≤
      2 + 12 * ‖exteriorForwardCoeff (rescaleExterior s F) 1‖ ^ 2 +
      9 * ‖exteriorForwardCoeff (rescaleExterior s F) 2‖ ^ 2 +
      6 * ‖exteriorForwardCoeff (rescaleExterior s F) 3 +
        (exteriorForwardCoeff (rescaleExterior s F) 1) ^ 2‖ ^ 2 +
      3 * ‖exteriorForwardCoeff (rescaleExterior s F) 4 +
        2 * exteriorForwardCoeff (rescaleExterior s F) 1 *
          exteriorForwardCoeff (rescaleExterior s F) 2‖ ^ 2 := by
  have hh := rescaleExterior_even_boundary_moment_le_finite_energy F hc hs0 hs1 3
    (by norm_num)
  norm_num only [Nat.cast_ofNat, Nat.reduceMul] at hh
  rwa [sixthMoment_finite_energy_eq] at hh

/-- The sixth-moment deficit follows from the area budget and the
single diagonal Grunsky coefficient. -/
theorem sixthMoment_scalar_margin
    {s a b g y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g) (hy : 0 ≤ y)
    (harea : 2 * a ^ 2 + 4 * b ^ 2 ≤ 1 - s)
    (hgrunsky : g ≤ (1 + s) / 2)
    (htriangle : y ≤ 2 * a + b) :
    2 + 12 * s + 9 * a ^ 2 + 6 * g ^ 2 + 3 * y ^ 2 ≤
      20 - (9 / 2) * (1 - s) := by
  have hy2 : y ^ 2 ≤ (2 * a + b) ^ 2 := by nlinarith
  have hg2 : g ^ 2 ≤ ((1 + s) / 2) ^ 2 := by nlinarith
  have hbudget : 9 * a ^ 2 + 3 * y ^ 2 ≤ 12 * (2 * a ^ 2 + 4 * b ^ 2) := by
    nlinarith [sq_nonneg (a - 2 * b), sq_nonneg b]
  have hs2 : s ^ 2 ≤ s := by nlinarith
  nlinarith

theorem rescaleExterior_boundary_six_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun ζ : ℂ => ‖rescaleExterior r F ζ‖ ^ 6) 0 1 ≤
      20 - (9 / 2) *
        (1 - ‖exteriorForwardCoeff (rescaleExterior r F) 1‖ ^ 2) := by
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
  have htriangle : ‖b₄ + 2 * b₁ * b₂‖ ≤ 2 * ‖b₂‖ + ‖b₄‖ := by
    have h := norm_add_le b₄ (2 * b₁ * b₂)
    have hx : ‖b₁‖ * ‖b₂‖ ≤ ‖b₂‖ := by
      nlinarith [norm_nonneg b₂]
    simp only [norm_mul] at h
    norm_num at h
    nlinarith
  have hscalar := sixthMoment_scalar_margin
    (s := ‖b₁‖ ^ 2) (a := ‖b₂‖) (b := ‖b₄‖)
    (g := ‖b₃ + b₁ ^ 2‖) (y := ‖b₄ + 2 * b₁ * b₂‖)
    (sq_nonneg _) (by nlinarith [sq_nonneg (1 - ‖b₁‖)])
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hbudget hgrunsky htriangle
  have hfinite := rescaleExterior_boundary_six_le_coeff F hc hr0 hr1
  dsimp only [G, b₁, b₂, b₃, b₄] at hscalar
  exact hfinite.trans hscalar

theorem actualBoundaryRadialMoment_six_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 6 ≤
      20 - (9 / 2) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  have hleft : Tendsto
      (fun s : ℝ => Real.circleAverage
        (fun ζ : ℂ => ‖rescaleExterior s F ζ‖ ^ 6) 0 1)
      (𝓝[<] (1 : ℝ)) (𝓝 (actualBoundaryRadialMoment F 6)) := by
    simpa only [Real.rpow_ofNat] using
      actualBoundaryRadialMoment_rescale_circle_tendsto F hc 6 (by norm_num)
  have hright : Tendsto
      (fun s : ℝ => 20 - (9 / 2) *
        (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2))
      (𝓝[<] (1 : ℝ))
      (𝓝 (20 - (9 / 2) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2))) := by
    have hcont : Continuous
        (fun s : ℝ => 20 - (9 / 2) *
          (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2)) := by
      fun_prop
    simpa only [Complex.ofReal_one, one_pow, one_mul] using
      hcont.continuousAt.tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
  have hh := rescaleExterior_boundary_six_margin F hc hs.1 hs.2
  rw [rescaleExterior_forwardCoeff F hc hs.1] at hh
  simpa only [Nat.reduceAdd] using hh

theorem slitRadialMomentConstant_six : slitRadialMomentConstant 6 = 20 := by
  have h4 : Real.Gamma 4 = 6 := by
    convert Real.Gamma_nat_eq_factorial 3 using 1 <;> norm_num
  have h7 : Real.Gamma 7 = 720 := by
    convert Real.Gamma_nat_eq_factorial 6 using 1 <;> norm_num
  norm_num [slitRadialMomentConstant, h4, h7]

theorem actualBoundaryRadialMoment_six_quantitative
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 6 ≤ slitRadialMomentConstant 6 *
      (1 - (9 / 40) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2)) := by
  rw [slitRadialMomentConstant_six]
  convert actualBoundaryRadialMoment_six_margin F hc using 1 <;> ring

theorem actualBoundaryRadialMoment_six_eq_imp_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (heq : actualBoundaryRadialMoment F 6 = slitRadialMomentConstant 6) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  have hmargin := actualBoundaryRadialMoment_six_margin F hc
  have hble : ‖exteriorForwardCoeff F 1‖ ≤ 1 := by
    simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using
      exteriorInverseCoeff_one_norm_le F hc
  rw [slitRadialMomentConstant_six] at heq
  have hb : ‖exteriorForwardCoeff F 1‖ = 1 := by
    nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  apply (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).1
  simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using hb

end SpringerLean

#print axioms SpringerLean.actualBoundaryRadialMoment_six_quantitative
#print axioms SpringerLean.actualBoundaryRadialMoment_six_eq_imp_slit
