import SpringerLean.Round1877SixthMomentFiniteEnergy
import SpringerLean.Round296ActualCoefficientExpressions

open PowerSeries

namespace SpringerLean
open RatPolyCheck

set_option maxHeartbeats 3000000

/-- The low coefficients of the fourth power of the exterior series. -/
theorem formalPhi_fourth_first_coefficients (F : ℂ → ℂ) :
    let φ := formalExteriorPhi (exteriorFormalForward F)
    PowerSeries.coeff 0 (φ ^ 4) = 1 ∧
    PowerSeries.coeff 1 (φ ^ 4) = 0 ∧
    PowerSeries.coeff 2 (φ ^ 4) = 4 * exteriorForwardCoeff F 1 ∧
    PowerSeries.coeff 3 (φ ^ 4) = 4 * exteriorForwardCoeff F 2 ∧
    PowerSeries.coeff 4 (φ ^ 4) =
      4 * exteriorForwardCoeff F 3 + 6 * exteriorForwardCoeff F 1 ^ 2 ∧
    PowerSeries.coeff 5 (φ ^ 4) =
      4 * (exteriorForwardCoeff F 4 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2) ∧
    PowerSeries.coeff 6 (φ ^ 4) =
      4 * (exteriorForwardCoeff F 5 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
        (3 / 2 : ℂ) * exteriorForwardCoeff F 2 ^ 2 +
        exteriorForwardCoeff F 1 ^ 3) ∧
    PowerSeries.coeff 7 (φ ^ 4) =
      4 * (exteriorForwardCoeff F 6 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
        3 * (exteriorForwardCoeff F 3 + exteriorForwardCoeff F 1 ^ 2) *
          exteriorForwardCoeff F 2) := by
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
  have h6 : PowerSeries.coeff 6 φ = exteriorForwardCoeff F 5 := hsucc 5
  have h7 : PowerSeries.coeff 7 φ = exteriorForwardCoeff F 6 := hsucc 6
  change PowerSeries.coeff 0 (φ ^ 4) = 1 ∧
    PowerSeries.coeff 1 (φ ^ 4) = 0 ∧
    PowerSeries.coeff 2 (φ ^ 4) = 4 * exteriorForwardCoeff F 1 ∧
    PowerSeries.coeff 3 (φ ^ 4) = 4 * exteriorForwardCoeff F 2 ∧
    PowerSeries.coeff 4 (φ ^ 4) =
      4 * exteriorForwardCoeff F 3 + 6 * exteriorForwardCoeff F 1 ^ 2 ∧
    PowerSeries.coeff 5 (φ ^ 4) =
      4 * (exteriorForwardCoeff F 4 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2) ∧
    PowerSeries.coeff 6 (φ ^ 4) =
      4 * (exteriorForwardCoeff F 5 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
        (3 / 2 : ℂ) * exteriorForwardCoeff F 2 ^ 2 +
        exteriorForwardCoeff F 1 ^ 3) ∧
    PowerSeries.coeff 7 (φ ^ 4) =
      4 * (exteriorForwardCoeff F 6 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
        3 * (exteriorForwardCoeff F 3 + exteriorForwardCoeff F 1 ^ 2) *
          exteriorForwardCoeff F 2)
  norm_num [pow_succ, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    h0, h1, h2, h3, h4, h5, h6, h7] <;> ring <;> simp

theorem eighthMoment_finite_energy_eq (F : ℂ → ℂ) :
    (∑ d ∈ Finset.range 8, (2 - (d : ℝ) / 4) *
      ‖PowerSeries.coeff d (formalExteriorPhi (exteriorFormalForward F) ^ 4)‖ ^ 2) =
      2 + 24 * ‖exteriorForwardCoeff F 1‖ ^ 2 +
      20 * ‖exteriorForwardCoeff F 2‖ ^ 2 +
      ‖4 * exteriorForwardCoeff F 3 + 6 * exteriorForwardCoeff F 1 ^ 2‖ ^ 2 +
      12 * ‖exteriorForwardCoeff F 4 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2‖ ^ 2 +
      8 * ‖exteriorForwardCoeff F 5 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
        (3 / 2 : ℂ) * exteriorForwardCoeff F 2 ^ 2 +
        exteriorForwardCoeff F 1 ^ 3‖ ^ 2 +
      4 * ‖exteriorForwardCoeff F 6 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
        3 * (exteriorForwardCoeff F 3 + exteriorForwardCoeff F 1 ^ 2) *
          exteriorForwardCoeff F 2‖ ^ 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    formalPhi_fourth_first_coefficients F
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7,
    norm_mul] <;> ring

theorem rescaleExterior_boundary_eight_le_coeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.circleAverage (fun ζ : ℂ => ‖rescaleExterior s F ζ‖ ^ 8) 0 1 ≤
      2 + 24 * ‖exteriorForwardCoeff (rescaleExterior s F) 1‖ ^ 2 +
      20 * ‖exteriorForwardCoeff (rescaleExterior s F) 2‖ ^ 2 +
      ‖4 * exteriorForwardCoeff (rescaleExterior s F) 3 +
        6 * exteriorForwardCoeff (rescaleExterior s F) 1 ^ 2‖ ^ 2 +
      12 * ‖exteriorForwardCoeff (rescaleExterior s F) 4 +
        3 * exteriorForwardCoeff (rescaleExterior s F) 1 *
          exteriorForwardCoeff (rescaleExterior s F) 2‖ ^ 2 +
      8 * ‖exteriorForwardCoeff (rescaleExterior s F) 5 +
        3 * exteriorForwardCoeff (rescaleExterior s F) 1 *
          exteriorForwardCoeff (rescaleExterior s F) 3 +
        (3 / 2 : ℂ) * exteriorForwardCoeff (rescaleExterior s F) 2 ^ 2 +
        exteriorForwardCoeff (rescaleExterior s F) 1 ^ 3‖ ^ 2 +
      4 * ‖exteriorForwardCoeff (rescaleExterior s F) 6 +
        3 * exteriorForwardCoeff (rescaleExterior s F) 1 *
          exteriorForwardCoeff (rescaleExterior s F) 4 +
        3 * (exteriorForwardCoeff (rescaleExterior s F) 3 +
          exteriorForwardCoeff (rescaleExterior s F) 1 ^ 2) *
          exteriorForwardCoeff (rescaleExterior s F) 2‖ ^ 2 := by
  have hh := rescaleExterior_even_boundary_moment_le_finite_energy F hc hs0 hs1 4
    (by norm_num)
  norm_num only [Nat.cast_ofNat, Nat.reduceMul] at hh
  rwa [eighthMoment_finite_energy_eq] at hh

/-- The two additional Grunsky entries needed in the paper's p=8
calculation, obtained from the already proved general analytic kernel. -/
theorem exteriorFormalGrunskyCoeff_two_three (F : ℂ → ℂ) :
    PowerSeries.coeff 3 (PowerSeries.coeff 2 (exteriorFormalGrunskyKernel F)) =
      exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 := by
  have h := logGrunskyCoeffExpr_sound F 3 2
  have he : (logGrunskyCoeffExpr 3 2).eval (actualCoeffVariable F) =
      exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 := by
    norm_num [logGrunskyCoeffExpr, Expr.fsum, bipowerCoeffExpr,
      forwardKernelCoeffExpr, Expr.mulUnlessRightZero, Expr.smartMulLeft,
      Expr.smartAdd, Expr.smartAddLeft, Expr.eval, actualCoeffVariable]
    ring
  exact h.symm.trans he

theorem exteriorFormalGrunskyCoeff_three_three (F : ℂ → ℂ) :
    PowerSeries.coeff 3 (PowerSeries.coeff 3 (exteriorFormalGrunskyKernel F)) =
      exteriorForwardCoeff F 5 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
        exteriorForwardCoeff F 2 ^ 2 +
        (1 / 3 : ℂ) * exteriorForwardCoeff F 1 ^ 3 := by
  have h := logGrunskyCoeffExpr_sound F 3 3
  have he : (logGrunskyCoeffExpr 3 3).eval (actualCoeffVariable F) =
      exteriorForwardCoeff F 5 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
        exteriorForwardCoeff F 2 ^ 2 +
        (1 / 3 : ℂ) * exteriorForwardCoeff F 1 ^ 3 := by
    norm_num [logGrunskyCoeffExpr, Expr.fsum, bipowerCoeffExpr,
      forwardKernelCoeffExpr, Expr.mulUnlessRightZero, Expr.smartMulLeft,
      Expr.smartAdd, Expr.smartAddLeft, Expr.eval, actualCoeffVariable]
    ring
  exact h.symm.trans he

theorem exteriorFormalGrunskyCoeff_two_one (F : ℂ → ℂ) :
    PowerSeries.coeff 1 (PowerSeries.coeff 2 (exteriorFormalGrunskyKernel F)) =
      exteriorForwardCoeff F 2 := by
  have h := logGrunskyCoeffExpr_sound F 1 2
  have he : (logGrunskyCoeffExpr 1 2).eval (actualCoeffVariable F) =
      exteriorForwardCoeff F 2 := by
    norm_num [logGrunskyCoeffExpr, Expr.fsum, bipowerCoeffExpr,
      forwardKernelCoeffExpr, Expr.mulUnlessRightZero, Expr.smartMulLeft,
      Expr.smartAdd, Expr.smartAddLeft, Expr.eval, actualCoeffVariable]
  exact h.symm.trans he

theorem exteriorGrunsky_low_three_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorForwardCoeff F 2‖ ^ 2 +
      2 * ‖exteriorForwardCoeff F 3 +
        (1 / 2 : ℂ) * exteriorForwardCoeff F 1 ^ 2‖ ^ 2 +
      3 * ‖exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2‖ ^ 2 ≤ 1 / 2 := by
  have h := exterior_generalGrunsky_weighted_contraction F hc 3 ![0, 1, 0]
  norm_num [Fin.sum_univ_succ, exteriorFormalGrunskyCoeff_two_one,
    exteriorFormalGrunskyCoeff_two_two,
    exteriorFormalGrunskyCoeff_two_three, norm_mul] at h
  nlinarith

theorem exteriorGrunsky_three_three_norm_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorForwardCoeff F 5 +
      exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      exteriorForwardCoeff F 2 ^ 2 +
      (1 / 3 : ℂ) * exteriorForwardCoeff F 1 ^ 3‖ ≤ 1 / 3 := by
  have h := exterior_generalGrunsky_weighted_contraction F hc 3 ![0, 0, 1]
  norm_num [Fin.sum_univ_succ, exteriorFormalGrunskyCoeff_three_three,
    norm_mul] at h
  nlinarith [norm_nonneg (exteriorForwardCoeff F 5 +
    exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
    exteriorForwardCoeff F 2 ^ 2 +
    (1 / 3 : ℂ) * exteriorForwardCoeff F 1 ^ 3)]

/-- Square completion for the first p=8 Grunsky block. -/
theorem eighth_first_block_identity (b₁ b₃ : ℂ) :
    ‖4 * b₃ + 6 * b₁ ^ 2‖ ^ 2 =
      48 * ‖b₃ + (1 / 2 : ℂ) * b₁ ^ 2‖ ^ 2 +
      24 * ‖b₁ ^ 2‖ ^ 2 - 32 * ‖b₃‖ ^ 2 := by
  let q : ℂ := b₁ ^ 2
  change ‖4 * b₃ + 6 * q‖ ^ 2 =
    48 * ‖b₃ + (1 / 2 : ℂ) * q‖ ^ 2 + 24 * ‖q‖ ^ 2 - 32 * ‖b₃‖ ^ 2
  norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring

theorem eighth_cross_term_bound (u v : ℂ) :
    12 * ‖u + 2 * v‖ ^ 2 - 72 * ‖u‖ ^ 2 ≤
      (288 / 5 : ℝ) * ‖v‖ ^ 2 := by
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have htriangle := norm_add_le u (2 * v)
  norm_num at htriangle
  have hsq : ‖u + 2 * v‖ ^ 2 ≤ (‖u‖ + 2 * ‖v‖) ^ 2 := by
    nlinarith [norm_nonneg (u + 2 * v)]
  nlinarith [sq_nonneg (5 * ‖u‖ - 2 * ‖v‖)]

theorem eighth_first_block_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    20 * ‖exteriorForwardCoeff F 2‖ ^ 2 +
      ‖4 * exteriorForwardCoeff F 3 + 6 * exteriorForwardCoeff F 1 ^ 2‖ ^ 2 +
      12 * ‖exteriorForwardCoeff F 4 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2‖ ^ 2 ≤
      12 + 24 * (‖exteriorForwardCoeff F 1‖ ^ 2) ^ 2 +
        (144 / 5 : ℝ) * ‖exteriorForwardCoeff F 1‖ ^ 2 *
          (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  let u := b₄ + b₁ * b₂
  let v := b₁ * b₂
  have hgrunsky := exteriorGrunsky_low_three_budget F hc
  have harea := exteriorForwardCoeff_finite_area F hc 2
  have hset : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hset] at harea
  norm_num at harea
  have h2t : 2 * ‖b₂‖ ^ 2 ≤ 1 - ‖b₁‖ ^ 2 := by
    dsimp only [b₁, b₂]
    linarith
  have hs : 0 ≤ ‖b₁‖ ^ 2 := sq_nonneg _
  have hvD : 2 * ‖v‖ ^ 2 ≤ ‖b₁‖ ^ 2 * (1 - ‖b₁‖ ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left h2t hs
    dsimp only [v]
    rw [norm_mul]
    nlinarith
  have hcross := eighth_cross_term_bound u v
  have hid := eighth_first_block_identity b₁ b₃
  have hnormpow : ‖b₁ ^ 2‖ ^ 2 = (‖b₁‖ ^ 2) ^ 2 := by
    rw [norm_pow]
  have hplus : u + 2 * v = b₄ + 3 * b₁ * b₂ := by
    dsimp only [u, v]
    ring
  rw [hplus] at hcross
  dsimp only [b₁, b₂, b₃, b₄] at hid hcross hnormpow hvD
  nlinarith [sq_nonneg ‖exteriorForwardCoeff F 3‖]

end SpringerLean
