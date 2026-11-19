import SpringerLean.Round2010OddStarIntegratedVariation

namespace SpringerLean
open scoped Topology

theorem oddStarBoundaryRadius_pow
    (m : ℕ) (hm : 0 < m) (θ : ℝ) :
    oddStarBoundaryRadius m θ ^ m = 2 + 2 * Real.cos θ := by
  have hbase : 0 ≤ 2 + 2 * Real.cos θ := by
    nlinarith [Real.neg_one_le_cos θ]
  simpa only [oddStarBoundaryRadius] using
    Real.rpow_inv_natCast_pow hbase (by omega : m ≠ 0)

theorem oddStarAlpha_norm_eq_one
    (t : ℝ) (ht : |t| < 1) : ‖oddStarAlpha t‖ = 1 := by
  have hq : 0 ≤ 1 - t ^ 2 := by
    have h := abs_lt.mp ht
    nlinarith
  have hs := Real.sq_sqrt hq
  have hsq : ‖oddStarAlpha t‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [oddStarAlpha, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    nlinarith
  nlinarith [norm_nonneg (oddStarAlpha t)]

theorem oddStarCircle_cos_identity (θ : ℝ) :
    (((2 + 2 * Real.cos θ) : ℝ) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I) =
    (Complex.exp ((θ : ℂ) * Complex.I) + 1) ^ 2 := by
  have hcos : Complex.cos (θ : ℂ) = (Real.cos θ : ℂ) := by simp
  have hquad := Complex.cos_eq_iff_quadratic.mp hcos
  have htarget : ((2 : ℂ) + 2 * (Real.cos θ : ℂ)) *
      Complex.exp ((θ : ℂ) * Complex.I) =
      (Complex.exp ((θ : ℂ) * Complex.I) + 1) ^ 2 := by
    linear_combination -hquad
  convert htarget using 1
  push_cast
  ring

theorem oddStarComplexRoot_pow
    (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    (Complex.exp ((m : ℂ)⁻¹ * Complex.log z)) ^ m = z := by
  rw [← Complex.exp_nat_mul]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hmul : (m : ℂ) * ((m : ℂ)⁻¹ * Complex.log z) =
      Complex.log z := by field_simp
  rw [hmul, Complex.exp_log hz]

theorem oddStarMovingBoundaryPoint_pow_eq_seed
    (m : ℕ) (hm : 3 ≤ m) (t θ : ℝ)
    (hfactor : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0) :
    (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t) ^ m =
      oddStarSeed t (oddStarAlpha t *
        Complex.exp ((θ : ℂ) * Complex.I)) := by
  let ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  let α : ℂ := oddStarAlpha t
  let r : ℝ := oddStarBoundaryRadius m θ
  have hm0 : 0 < m := by omega
  have hrpow : r ^ m = 2 + 2 * Real.cos θ :=
    oddStarBoundaryRadius_pow m hm0 θ
  have hrpowC : (r : ℂ) ^ m = ((2 + 2 * Real.cos θ : ℝ) : ℂ) := by
    exact_mod_cast hrpow
  have hroot := oddStarComplexRoot_pow m hm0
    (oddStarBoundaryFactor ζ t) hfactor
  have hcircle := oddStarCircle_cos_identity θ
  have halgebra :
      (((2 + 2 * Real.cos θ : ℝ) : ℂ) *
        oddStarBoundaryFactor ζ t) =
      oddStarSeed t (α * ζ) := by
    have hden : α * ζ - (t : ℂ) * Complex.I =
        oddStarBoundaryDenominator ζ t := by
      rfl
    simp only [oddStarBoundaryFactor, oddStarSeed]
    dsimp [ζ, α, oddStarAlpha] at *
    rw [← mul_div_assoc]
    congr 1
    · calc
        ((2 + 2 * Real.cos θ : ℝ) : ℂ) *
            (((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) ^ 2 *
              Complex.exp ((θ : ℂ) * Complex.I)) =
            (((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) ^ 2) *
              (Complex.exp ((θ : ℂ) * Complex.I) + 1) ^ 2 := by
            rw [mul_left_comm, hcircle]
        _ = (((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) *
              Complex.exp ((θ : ℂ) * Complex.I) -
              (t : ℂ) * Complex.I + Real.sqrt (1 - t ^ 2)) ^ 2 := by
            ring
  calc
    (oddStarMovingBoundaryPoint m r θ t) ^ m =
        (r : ℂ) ^ m *
          (Complex.exp ((m : ℂ)⁻¹ * Complex.log
            (oddStarBoundaryFactor ζ t))) ^ m := by
          simp [oddStarMovingBoundaryPoint, ζ, mul_pow]
    _ = ((2 + 2 * Real.cos θ : ℝ) : ℂ) *
        oddStarBoundaryFactor ζ t := by
          rw [hroot, hrpowC]
    _ = oddStarSeed t (α * ζ) := halgebra

theorem oddStarMovingBoundaryPoint_mem_omitted
    (m : ℕ) (hm : 3 ≤ m) (t θ : ℝ) (ht : |t| < 1)
    (hfactor : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0) :
    oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t ∈
      oddStarPerturbationOmitted m t := by
  let ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  let α : ℂ := oddStarAlpha t
  have hζ : ‖ζ‖ = 1 := by simp [ζ]
  have hα : ‖α‖ = 1 := oddStarAlpha_norm_eq_one t ht
  have hunit : α * ζ ∈ oddStarSeedUnitCircle := by
    simp only [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right]
    rw [norm_mul, hα, hζ, one_mul]
  rw [oddStarPerturbation_omitted_eq_power_preimage m (by omega) t ht]
  change (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t) ^ m ∈
    oddStarSeedOmitted t
  rw [oddStarMovingBoundaryPoint_pow_eq_seed m hm t θ hfactor]
  exact oddStarSeed_boundary_image_subset_omitted t ht ⟨α * ζ, hunit, rfl⟩

theorem oddStarMovingBoundaryPoint_uniform_mem_omitted
    (m : ℕ) (hm : 3 ≤ m) :
    ∃ U : Set ℝ, U ∈ 𝓝 (0 : ℝ) ∧
      ∀ t ∈ U, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t ∈
          oddStarPerturbationOmitted m t := by
  obtain ⟨U, hU, hreg⟩ := oddStarVariation_uniform_regular_domain m hm
  let V : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hV : V ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds isOpen_Ioo
    norm_num [V]
  refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
  intro t ht θ hθ
  have ht1 : |t| < 1 := by
    simpa [V, abs_lt] using ht.2
  have hfactor := (hreg t ht.1 θ hθ).2.1
  exact oddStarMovingBoundaryPoint_mem_omitted m hm t θ ht1
    (Complex.slitPlane_ne_zero hfactor)

end SpringerLean
