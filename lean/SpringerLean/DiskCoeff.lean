import SpringerLean.DiskMoments
import SpringerLean.TaylorBridge
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory
open scoped Topology NNReal ENNReal ComplexConjugate

namespace SpringerLean

/-- Derivative Taylor polynomials converge uniformly on the closed unit disk
when the original function is analytic on a strictly larger disk. -/
theorem analytic_deriv_uniform_closedUnitDisk
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) :
    TendstoUniformlyOn
      (fun M u => ∑ j ∈ Finset.range M,
        ((j + 1 : ℂ) * actualTaylorCoeff h (j + 1)) * u ^ j)
      (deriv h) atTop (Metric.closedBall (0 : ℂ) 1) := by
  let r : ℝ≥0 := ⟨(R + 1) / 2, by linarith⟩
  have hr1 : (1 : ℝ≥0) < r := by
    apply NNReal.coe_lt_coe.mp
    change (1 : ℝ) < (R + 1) / 2
    linarith
  have hrR : (r : ℝ) < R := by
    change (R + 1) / 2 < R
    linarith
  have hr0 : (0 : ℝ≥0) < r := lt_trans (by norm_num) hr1
  have hd : DifferentiableOn ℂ (deriv h) (Metric.closedBall 0 r) :=
    hh.deriv.differentiableOn.mono (Metric.closedBall_subset_ball hrR)
  have hp := hd.hasFPowerSeriesOnBall hr0
  have hzero : (0 : ℂ) ∈ Metric.ball 0 R := by
    simp only [Metric.mem_ball, dist_self]
    linarith
  have hcanon := (hh.deriv 0 hzero).hasFPowerSeriesAt
  have heq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hcanon
  rw [heq] at hp
  let t : ℝ≥0 := ⟨((r : ℝ) + 1) / 2, by positivity⟩
  have h1t : (1 : ℝ) < t := by
    change (1 : ℝ) < ((r : ℝ) + 1) / 2
    have h : (1 : ℝ) < r := by exact_mod_cast hr1
    linarith
  have htr : (t : ℝ) < r := by
    change ((r : ℝ) + 1) / 2 < r
    have h : (1 : ℝ) < r := by exact_mod_cast hr1
    linarith
  have hrad : (t : ℝ≥0∞) < (r : ℝ≥0∞) := by
    exact_mod_cast htr
  have huniform := (hp.tendstoUniformlyOn hrad).mono
    (Metric.closedBall_subset_ball h1t)
  have hterm (j : ℕ) :
      iteratedDeriv j (deriv h) 0 / (j.factorial : ℂ) =
        (j + 1 : ℂ) * actualTaylorCoeff h (j + 1) :=
    actualTaylorCoeff_deriv h j
  simpa [FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.coeff_ofScalars, hterm,
    smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using huniform

/-- Finite Taylor derivative polynomials are read exactly by disk monomial
orthogonality. The coefficient is zero until its mode enters the partial sum. -/
theorem unitDisk_finite_derivative_moment
    (c : ℕ → ℂ) (p M : ℕ) :
    (Real.pi : ℂ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ∑ j ∈ Finset.range M,
          ((j + 1 : ℂ) * c j) * (z ^ p * conj z ^ j) ∂volume) =
      if p < M then c p else 0 := by
  have hint (j : ℕ) : IntegrableOn
      (fun z : ℂ => ((j + 1 : ℂ) * c j) * (z ^ p * conj z ^ j))
      (Metric.ball (0 : ℂ) 1) := by
    have hcont : Continuous
        (fun z : ℂ => ((j + 1 : ℂ) * c j) * (z ^ p * conj z ^ j)) := by
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  rw [integral_finsetSum (Finset.range M) (fun j hj => hint j), Finset.mul_sum]
  simp_rw [integral_const_mul]
  have hterm (j : ℕ) :
      (Real.pi : ℂ)⁻¹ *
        (((j + 1 : ℂ) * c j) *
          (∫ z in Metric.ball (0 : ℂ) 1, z ^ p * conj z ^ j ∂volume)) =
        if p = j then c j else 0 := by
    calc
      _ = ((j + 1 : ℂ) * c j) *
          ((Real.pi : ℂ)⁻¹ *
            (∫ z in Metric.ball (0 : ℂ) 1, z ^ p * conj z ^ j ∂volume)) := by ring
      _ = ((j + 1 : ℂ) * c j) *
          (if p = j then (p + 1 : ℂ)⁻¹ else 0) := by
            rw [unitDisk_monomial_integral]
      _ = if p = j then c j else 0 := by
            by_cases hpj : p = j
            · subst j
              simp only [ite_true]
              have hp0 : (p + 1 : ℂ) ≠ 0 := by
                exact_mod_cast (by omega : p + 1 ≠ 0)
              field_simp
            · simp [hpj]
  simp_rw [hterm]
  by_cases hp : p < M
  · simp [hp]
  · simp [hp]

/-- The normalized disk pairing reads the next actual Taylor coefficient
of a function analytic across the unit circle. -/
theorem analytic_deriv_disk_moment
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) (p : ℕ) :
    (Real.pi : ℂ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        z ^ p * deriv h (conj z) ∂volume) =
      actualTaylorCoeff h (p + 1) := by
  let D : Set ℂ := Metric.ball 0 1
  let c : ℕ → ℂ := fun j => actualTaylorCoeff h (j + 1)
  let S : ℕ → ℂ → ℂ := fun M z =>
    ∑ j ∈ Finset.range M, ((j + 1 : ℂ) * c j) * (z ^ p * conj z ^ j)
  let Q : ℂ → ℂ := fun z => z ^ p * deriv h (conj z)
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hvol : volume D ≠ ∞ := by
    rw [Complex.volume_ball]
    finiteness
  have hderCont : ContinuousOn (deriv h) (Metric.closedBall (0 : ℂ) 1) := by
    have hsub : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball 0 R :=
      Metric.closedBall_subset_ball hR
    exact hh.deriv.continuousOn.mono hsub
  have hconj : Continuous (fun z : ℂ => conj z) := by fun_prop
  have hconjMaps : Set.MapsTo (fun z : ℂ => conj z)
      (Metric.closedBall (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right, ← Complex.star_def,
      norm_star] using hz
  obtain ⟨B, hB⟩ :=
    (((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
      hderCont).isBounded.exists_norm_le)
  have hderBound : ∀ u ∈ Metric.closedBall (0 : ℂ) 1, ‖deriv h u‖ ≤ B := by
    intro u hu
    exact hB _ (Set.mem_image_of_mem _ hu)
  have hBnonneg : 0 ≤ B := by
    exact (norm_nonneg (deriv h 0)).trans (hderBound 0 (by simp))
  have hu := analytic_deriv_uniform_closedUnitDisk h hR hh
  have hevent : ∀ᶠ M in atTop,
      ∀ u ∈ Metric.closedBall (0 : ℂ) 1,
        dist (deriv h u)
          (∑ j ∈ Finset.range M,
            ((j + 1 : ℂ) * c j) * u ^ j) < 1 := by
    simpa only [c] using
      (Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)
  have hpoint : ∀ᵐ z ∂(volume.restrict D),
      Tendsto (fun M => S M z) atTop (𝓝 (Q z)) := by
    filter_upwards [ae_restrict_mem hD] with z hz
    have hzcl : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.ball_subset_closedBall hz
    have hzconj := hconjMaps hzcl
    have ht := hu.tendsto_at hzconj
    have ht' : Tendsto
        (fun M => z ^ p *
          (∑ j ∈ Finset.range M,
            ((j + 1 : ℂ) * actualTaylorCoeff h (j + 1)) * (conj z) ^ j))
        atTop (𝓝 (z ^ p * deriv h (conj z))) :=
      tendsto_const_nhds.mul ht
    convert ht' using 1
    · funext M
      dsimp [S, c]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
  have hmeas : ∀ᶠ M in atTop,
      AEStronglyMeasurable (S M) (volume.restrict D) := by
    filter_upwards [] with M
    have hcont : Continuous (S M) := by
      dsimp [S]
      fun_prop
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᶠ M in atTop,
      ∀ᵐ z ∂(volume.restrict D), ‖S M z‖ ≤ B + 1 := by
    filter_upwards [hevent] with M hM
    filter_upwards [ae_restrict_mem hD] with z hz
    have hzcl : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.ball_subset_closedBall hz
    have hzconj := hconjMaps hzcl
    have hnormz : ‖z ^ p‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg z) (by simpa only [Metric.mem_closedBall, dist_zero_right] using hzcl)
    have hpartial : ‖∑ j ∈ Finset.range M,
        ((j + 1 : ℂ) * c j) * (conj z) ^ j‖ ≤ B + 1 := by
      have hd := hM (conj z) hzconj
      have htri : ‖∑ j ∈ Finset.range M,
          ((j + 1 : ℂ) * c j) * (conj z) ^ j‖ ≤
          ‖deriv h (conj z)‖ +
            dist (deriv h (conj z))
              (∑ j ∈ Finset.range M,
                ((j + 1 : ℂ) * c j) * (conj z) ^ j) := by
        calc
          _ = ‖deriv h (conj z) +
              ((∑ j ∈ Finset.range M,
                ((j + 1 : ℂ) * c j) * (conj z) ^ j) - deriv h (conj z))‖ := by
                congr 1
                ring
          _ ≤ ‖deriv h (conj z)‖ +
              ‖(∑ j ∈ Finset.range M,
                ((j + 1 : ℂ) * c j) * (conj z) ^ j) - deriv h (conj z)‖ :=
              norm_add_le _ _
          _ = _ := by rw [dist_eq_norm, norm_sub_rev]
      linarith [hderBound (conj z) hzconj]
    have hS : S M z = z ^ p * (∑ j ∈ Finset.range M,
        ((j + 1 : ℂ) * c j) * (conj z) ^ j) := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hS, norm_mul]
    exact (mul_le_mul hnormz hpartial (norm_nonneg _) (by norm_num)).trans
      (by simp)
  have hconst : Integrable (fun _ : ℂ => B + 1) (volume.restrict D) :=
    integrableOn_const hvol
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℂ => B + 1) hmeas hbound hconst hpoint
  have hfinite (M : ℕ) (hM : p < M) :
      (Real.pi : ℂ)⁻¹ * (∫ z in D, S M z ∂volume) = c p := by
    simpa [S, D, c, hM] using unitDisk_finite_derivative_moment c p M
  have hconstant : Tendsto
      (fun M : ℕ => (Real.pi : ℂ)⁻¹ *
        (∫ z in D, S M z ∂volume)) atTop (𝓝 (c p)) := by
    apply tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop p] with M hM
    exact (hfinite M hM).symm
  have hlim' : Tendsto
      (fun M : ℕ => (Real.pi : ℂ)⁻¹ *
        (∫ z in D, S M z ∂volume)) atTop
      (𝓝 ((Real.pi : ℂ)⁻¹ * (∫ z in D, Q z ∂volume))) :=
    tendsto_const_nhds.mul hlim
  have hsame := tendsto_nhds_unique hconstant hlim'
  simpa [Q, D, c] using hsame.symm

end SpringerLean
