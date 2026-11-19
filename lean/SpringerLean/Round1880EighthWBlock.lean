import SpringerLean.Round1879EighthMomentFiniteEnergy

namespace SpringerLean

set_option maxHeartbeats 2000000

/-- A complex square identity retaining the favorable cross term in the
fifth Laurent coefficient of F^4. -/
theorem eighth_w_square_identity (s : ℝ) (z q : ℂ) :
    4 * s * ‖z + (1 / 3 : ℂ) * q‖ ^ 2 =
      (4 / 3 : ℝ) * s * ‖z‖ ^ 2 +
      (8 / 3 : ℝ) * s * ‖z + (1 / 2 : ℂ) * q‖ ^ 2 -
      (2 / 9 : ℝ) * s * ‖q‖ ^ 2 := by
  norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring

theorem eighth_w_core_bound
    (s : ℝ) (z q : ℂ) (hs : 0 ≤ s)
    (hq : ‖q‖ ^ 2 = s ^ 2)
    (hc : ‖z + (1 / 2 : ℂ) * q‖ ≤ 1 / 2) :
    4 * s * ‖z + (1 / 3 : ℂ) * q‖ ^ 2 ≤
      (2 / 3 + s * ‖z‖ ^ 2) ^ 2 := by
  have hcsq : ‖z + (1 / 2 : ℂ) * q‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (z + (1 / 2 : ℂ) * q)]
  have hcs := mul_le_mul_of_nonneg_left hcsq hs
  have hbase := eighth_w_square_identity s z q
  have hpoly : 0 ≤ (1 - s) ^ 2 * (s + 2) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [sq_nonneg (s * ‖z‖ ^ 2)]

theorem eighth_w_core_actual_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      (2 / 3 : ℂ) * exteriorForwardCoeff F 1 ^ 3‖ ≤
      2 / 3 + ‖exteriorForwardCoeff F 1‖ ^ 2 *
        ‖exteriorForwardCoeff F 3‖ ^ 2 := by
  let b₁ := exteriorForwardCoeff F 1
  let b₃ := exteriorForwardCoeff F 3
  let q : ℂ := b₁ ^ 2
  let s : ℝ := ‖b₁‖ ^ 2
  have hbudget := exteriorGrunsky_low_three_budget F hc
  have hc22 : ‖b₃ + (1 / 2 : ℂ) * q‖ ≤ 1 / 2 := by
    dsimp only [b₃, q, b₁]
    nlinarith [sq_nonneg ‖exteriorForwardCoeff F 2‖,
      sq_nonneg ‖exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2‖,
      norm_nonneg (exteriorForwardCoeff F 3 +
        (1 / 2 : ℂ) * exteriorForwardCoeff F 1 ^ 2)]
  have hq : ‖q‖ ^ 2 = s ^ 2 := by
    dsimp only [q, s]
    rw [norm_pow]
  have hcore := eighth_w_core_bound s b₃ q (sq_nonneg _) hq hc22
  have hfactor : 2 * b₁ * b₃ + (2 / 3 : ℂ) * b₁ ^ 3 =
      (2 * b₁) * (b₃ + (1 / 3 : ℂ) * q) := by
    dsimp only [q]
    ring
  have hcoreeq : ‖2 * b₁ * b₃ + (2 / 3 : ℂ) * b₁ ^ 3‖ ^ 2 =
      4 * s * ‖b₃ + (1 / 3 : ℂ) * q‖ ^ 2 := by
    rw [hfactor, norm_mul]
    norm_num [s, norm_mul]
    ring
  have hpos : 0 ≤ 2 / 3 + s * ‖b₃‖ ^ 2 := by
    positivity
  have hres : ‖2 * b₁ * b₃ + (2 / 3 : ℂ) * b₁ ^ 3‖ ≤
      2 / 3 + s * ‖b₃‖ ^ 2 := by
    nlinarith [norm_nonneg (2 * b₁ * b₃ + (2 / 3 : ℂ) * b₁ ^ 3)]
  simpa only [b₁, b₃, s] using hres

theorem eighth_w_actual_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorForwardCoeff F 5 +
      3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      (3 / 2 : ℂ) * exteriorForwardCoeff F 2 ^ 2 +
      exteriorForwardCoeff F 1 ^ 3‖ ≤
      1 + (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 3 := by
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₅ := exteriorForwardCoeff F 5
  let c := b₅ + b₁ * b₃ + b₂ ^ 2 + (1 / 3 : ℂ) * b₁ ^ 3
  let u := 2 * b₁ * b₃ + (2 / 3 : ℂ) * b₁ ^ 3
  let w := b₅ + 3 * b₁ * b₃ + (3 / 2 : ℂ) * b₂ ^ 2 + b₁ ^ 3
  have h33 := exteriorGrunsky_three_three_norm_le F hc
  have hcore := eighth_w_core_actual_bound F hc
  have harea := exteriorForwardCoeff_finite_area F hc 3
  have hset : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [hset] at harea
  norm_num at harea
  have hs : ‖b₁‖ ^ 2 ≤ 1 := by
    dsimp only [b₁]
    nlinarith [sq_nonneg ‖exteriorForwardCoeff F 2‖,
      sq_nonneg ‖exteriorForwardCoeff F 3‖]
  have hmid : ‖b₁‖ ^ 2 * ‖b₃‖ ^ 2 + ‖b₂‖ ^ 2 / 2 ≤
      (1 - ‖b₁‖ ^ 2) / 3 := by
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖b₃‖)
    dsimp only [b₁, b₂, b₃]
    nlinarith
  have hdecomp : w = c + u + (1 / 2 : ℂ) * b₂ ^ 2 := by
    dsimp only [w, c, u]
    ring
  have htri : ‖w‖ ≤ ‖c‖ + ‖u‖ + ‖b₂‖ ^ 2 / 2 := by
    rw [hdecomp]
    have h1 := norm_add_le c u
    have h2 := norm_add_le (c + u) ((1 / 2 : ℂ) * b₂ ^ 2)
    norm_num [norm_mul, norm_pow] at h2
    linarith
  dsimp only [w, c, u, b₁, b₂, b₃, b₅] at htri
  dsimp only [b₁, b₂, b₃] at hmid
  linarith

theorem eighth_w_actual_energy_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    8 * ‖exteriorForwardCoeff F 5 +
      3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      (3 / 2 : ℂ) * exteriorForwardCoeff F 2 ^ 2 +
      exteriorForwardCoeff F 1 ^ 3‖ ^ 2 ≤
      8 + (56 / 9 : ℝ) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  let D := 1 - ‖exteriorForwardCoeff F 1‖ ^ 2
  let w := exteriorForwardCoeff F 5 +
    3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
    (3 / 2 : ℂ) * exteriorForwardCoeff F 2 ^ 2 +
    exteriorForwardCoeff F 1 ^ 3
  have hD0 : 0 ≤ D := by
    have h := exteriorInverseCoeff_one_norm_le F hc
    rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] at h
    dsimp only [D]
    nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  have hD1 : D ≤ 1 := by
    dsimp only [D]
    nlinarith [sq_nonneg ‖exteriorForwardCoeff F 1‖]
  have hw : ‖w‖ ≤ 1 + D / 3 := eighth_w_actual_bound F hc
  have hwsq : ‖w‖ ^ 2 ≤ (1 + D / 3) ^ 2 := by
    nlinarith [norm_nonneg w]
  dsimp only [D, w] at *
  nlinarith

end SpringerLean

#print axioms SpringerLean.eighth_w_actual_energy_bound
