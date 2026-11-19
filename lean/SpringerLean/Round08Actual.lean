import SpringerLean.Round08Fatou

open MeasureTheory Filter
open scoped ComplexConjugate Topology

namespace SpringerLean

/-- The actual derivative of every paper-class forward correction has
finite normalized square energy on the full open unit disk. -/
theorem exteriorForwardGerm_deriv_sq_integrable_le_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    IntegrableOn
      (fun z : ℂ => ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)
      (Metric.ball (0 : ℂ) 1) ∧
    (Real.pi)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume) ≤ 1 := by
  let d : ℕ → ℂ := exteriorForwardCoeff F
  let w : ℕ → ℝ := fun j => (j : ℝ) * ‖d j‖ ^ 2
  have hsumFull : Summable w := exteriorForwardCoeff_weighted_summable F hc
  have hsum : Summable (fun j : ℕ => (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2) := by
    simpa only [w, d, Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr hsumFull)
  have hcont : ContinuousOn
      (fun z : ℂ => deriv (exteriorForwardGerm F) (conj z))
      (Metric.ball (0 : ℂ) 1) := by
    have hg := (exteriorForwardGerm_analyticOnNhd_unitBall F hc).deriv.continuousOn
    have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
    apply hg.comp hcconj.continuousOn
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
  have hpoint : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasSum (fun j : ℕ => ((j + 1 : ℂ) * d (j + 1)) * (conj z) ^ j)
        (deriv (exteriorForwardGerm F) (conj z)) := by
    intro z hz
    have hzc : ‖conj z‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
    simpa only [d] using exteriorForwardGerm_deriv_hasSum_coeff_unitBall F hc hzc
  obtain ⟨hint, hbound⟩ :=
    disk_derivative_modes_fatou d
      (fun z => deriv (exteriorForwardGerm F) (conj z)) hcont hpoint hsum
  have hshift : (∑' j : ℕ, (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2) =
      ∑' j : ℕ, w j := by
    have hdecomp := hsumFull.sum_add_tsum_nat_add 1
    simpa [w, d] using hdecomp
  refine ⟨hint, ?_⟩
  calc
    (Real.pi)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume) ≤
      ∑' j : ℕ, (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2 := hbound
    _ = ∑' j : ℕ, w j := hshift
    _ ≤ 1 := exteriorForwardCoeff_weighted_tsum_le_one F hc

/-- The actual derivative difference has the coefficient exponent `j+2`
when the derivative mode is indexed by `j`, equivalently `j+1` for `b_j`. -/
theorem regularForwardGerm_deriv_difference_hasSum
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {u : ℂ} (hu : ‖u‖ < 1) :
    HasSum
      (fun j : ℕ =>
        ((j + 1 : ℂ) *
          (((s : ℂ) ^ (j + 2) - 1) *
            exteriorForwardCoeff F (j + 1))) * u ^ j)
      (deriv (regularForwardGerm s F) u -
        deriv (exteriorForwardGerm F) u) := by
  have hcS := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have hscaled := exteriorForwardGerm_deriv_hasSum_coeff_unitBall
    (rescaleExterior s F) hcS hu
  rw [← regularForwardGerm_eq_actual s hs0 F] at hscaled
  have horig := exteriorForwardGerm_deriv_hasSum_coeff_unitBall F hc hu
  have hsub := hscaled.sub horig
  convert hsub using 1
  ext j
  rw [rescaleExterior_forwardCoeff F hc hs0 (j + 1)]
  ring

/-- Fatou controls the actual derivative difference by the exact weighted
coefficient difference, with no boundary analyticity premise. -/
theorem regularForwardGerm_deriv_difference_sq_integrable_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IntegrableOn
      (fun z : ℂ => ‖deriv (regularForwardGerm s F) (conj z) -
        deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)
      (Metric.ball (0 : ℂ) 1) ∧
    (Real.pi)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖deriv (regularForwardGerm s F) (conj z) -
          deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume) ≤
      ∑' j : ℕ,
        ((j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) *
          (s ^ (j + 1) - 1) ^ 2 := by
  let b : ℕ → ℂ := exteriorForwardCoeff F
  let d : ℕ → ℂ := fun j => ((s : ℂ) ^ (j + 1) - 1) * b j
  let w : ℕ → ℝ := fun j => (j : ℝ) * ‖b j‖ ^ 2
  let wd : ℕ → ℝ := fun j => w j * (s ^ (j + 1) - 1) ^ 2
  have hterm (j : ℕ) :
      (j : ℝ) * ‖d j‖ ^ 2 = wd j := by
    dsimp [d, wd, w]
    rw [norm_mul]
    have hfac : ‖(s : ℂ) ^ (j + 1) - 1‖ = |s ^ (j + 1) - 1| := by
      norm_cast
    rw [hfac, mul_pow, sq_abs]
    ring
  have hw0 (j : ℕ) : 0 ≤ wd j := by
    dsimp [wd, w]
    positivity
  have hwle (j : ℕ) : wd j ≤ w j := by
    have hsPow0 : 0 ≤ s ^ (j + 1) := pow_nonneg hs0.le _
    have hsPow1 : s ^ (j + 1) ≤ 1 := by
      simpa using (pow_le_pow_left₀ hs0.le hs1.le (j + 1))
    have hsSq : (s ^ (j + 1) - 1) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (s ^ (j + 1))]
    exact mul_le_of_le_one_right (by dsimp [w]; positivity) hsSq
  have hwSum : Summable w := exteriorForwardCoeff_weighted_summable F hc
  have hwdSum : Summable wd :=
    Summable.of_nonneg_of_le hw0 hwle hwSum
  have hdsum : Summable (fun j : ℕ =>
      (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2) := by
    convert ((summable_nat_add_iff 1).mpr hwdSum) using 1
    funext j
    simpa only [Nat.cast_add, Nat.cast_one] using hterm (j + 1)
  have hcont : ContinuousOn
      (fun z : ℂ => deriv (regularForwardGerm s F) (conj z) -
        deriv (exteriorForwardGerm F) (conj z))
      (Metric.ball (0 : ℂ) 1) := by
    have hgs : ContinuousOn (deriv (regularForwardGerm s F))
        (Metric.ball (0 : ℂ) 1) := by
      rw [regularForwardGerm_eq_actual s hs0 F]
      exact (exteriorForwardGerm_analyticOnNhd_unitBall
        (rescaleExterior s F)
        (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)).deriv.continuousOn
    have hg := (exteriorForwardGerm_analyticOnNhd_unitBall F hc).deriv.continuousOn
    have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
    have hmaps : Set.MapsTo (fun z : ℂ => conj z)
        (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
      intro z hz
      simpa only [Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
    exact (hgs.comp hcconj.continuousOn hmaps).sub
      (hg.comp hcconj.continuousOn hmaps)
  have hpoint : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasSum (fun j : ℕ => ((j + 1 : ℂ) * d (j + 1)) * (conj z) ^ j)
        (deriv (regularForwardGerm s F) (conj z) -
          deriv (exteriorForwardGerm F) (conj z)) := by
    intro z hz
    have hzc : ‖conj z‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
    simpa only [d, b, Nat.add_assoc, Nat.reduceAdd] using
      regularForwardGerm_deriv_difference_hasSum F hc hs0 hs1 hzc
  obtain ⟨hint, hbound⟩ :=
    disk_derivative_modes_fatou d
      (fun z => deriv (regularForwardGerm s F) (conj z) -
        deriv (exteriorForwardGerm F) (conj z)) hcont hpoint hdsum
  have hshift : (∑' j : ℕ, (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2) =
      ∑' j : ℕ, wd j := by
    have hdecomp := hwdSum.sum_add_tsum_nat_add 1
    calc
      (∑' j : ℕ, (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2) =
          ∑' j : ℕ, wd (j + 1) := by
            congr 1
            funext j
            simpa only [Nat.cast_add, Nat.cast_one] using hterm (j + 1)
      _ = ∑' j : ℕ, wd j := by
        simpa [wd, w] using hdecomp
  refine ⟨hint, ?_⟩
  calc
    (Real.pi)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖deriv (regularForwardGerm s F) (conj z) -
          deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume) ≤
      ∑' j : ℕ, (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2 := hbound
    _ = ∑' j : ℕ, wd j := hshift
    _ = ∑' j : ℕ,
          ((j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) *
            (s ^ (j + 1) - 1) ^ 2 := rfl

/-- The actual derivatives converge strongly in normalized `L²(D)` as
the regularization parameter approaches one from below. -/
theorem regularForwardGerm_deriv_L2_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    Tendsto
      (fun s : ℝ => (Real.pi)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖deriv (regularForwardGerm s F) (conj z) -
            deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let E : ℝ → ℝ := fun s => (Real.pi)⁻¹ *
    (∫ z in Metric.ball (0 : ℂ) 1,
      ‖deriv (regularForwardGerm s F) (conj z) -
        deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume)
  let W : ℝ → ℝ := fun s => ∑' j : ℕ,
    ((j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) *
      (s ^ (j + 1) - 1) ^ 2
  have h0 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have h1 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), E s ≤ W s := by
    filter_upwards [h0, h1] with s hs0 hs1
    exact (regularForwardGerm_deriv_difference_sq_integrable_le
      F hc hs0 hs1).2
  have hnonneg : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ E s := by
    filter_upwards [] with s
    exact mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      (integral_nonneg (fun z => sq_nonneg _))
  have hW : Tendsto W (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
    exteriorForwardCoeff_dilated_difference_energy_tendsto F hc
  exact squeeze_zero' hnonneg hle hW

end SpringerLean
