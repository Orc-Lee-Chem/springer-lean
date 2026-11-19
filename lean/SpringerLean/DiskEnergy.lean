import SpringerLean.RegularLimit

open MeasureTheory Filter
open scoped ComplexConjugate ENNReal Topology

namespace SpringerLean

/-- Finite anti-analytic polynomial on the disk. -/
noncomputable def finiteAntiPolynomial (c : ℕ → ℂ) (M : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range M, c j * (conj z) ^ j

/-- Finite disk Parseval, in complex form. -/
theorem finiteAntiPolynomial_complex_energy (c : ℕ → ℂ) (M : ℕ) :
    (Real.pi : ℂ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        finiteAntiPolynomial c M z * star (finiteAntiPolynomial c M z) ∂volume) =
      ∑ j ∈ Finset.range M, (c j * star (c j)) / (j + 1 : ℂ) := by
  let D : Set ℂ := Metric.ball 0 1
  have hpoint (z : ℂ) :
      finiteAntiPolynomial c M z * star (finiteAntiPolynomial c M z) =
        ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M,
          (c j * star (c k)) * ((conj z) ^ j * z ^ k) := by
    unfold finiteAntiPolynomial
    simp_rw [star_sum, star_mul, star_pow, Complex.star_def]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    congr 1
    ext j
    congr 1
    ext k
    simp only [Complex.conj_conj]
    ring
  have hint (j k : ℕ) : IntegrableOn
      (fun z : ℂ => (c j * star (c k)) * ((conj z) ^ j * z ^ k)) D := by
    have hcont : Continuous
        (fun z : ℂ => (c j * star (c k)) * ((conj z) ^ j * z ^ k)) := by
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  have houterInt (j : ℕ) : IntegrableOn
      (fun z : ℂ => ∑ k ∈ Finset.range M,
        (c j * star (c k)) * ((conj z) ^ j * z ^ k)) D := by
    have hfun : (∑ k ∈ Finset.range M,
        (fun z : ℂ => (c j * star (c k)) * ((conj z) ^ j * z ^ k))) =
        (fun z : ℂ => ∑ k ∈ Finset.range M,
          (c j * star (c k)) * ((conj z) ^ j * z ^ k)) := by
      funext z
      simp only [Finset.sum_apply]
    change Integrable (fun z : ℂ => ∑ k ∈ Finset.range M,
      (c j * star (c k)) * ((conj z) ^ j * z ^ k)) (volume.restrict D)
    rw [← hfun]
    exact integrable_finsetSum' (Finset.range M) (fun k hk => hint j k)
  calc
    (Real.pi : ℂ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          finiteAntiPolynomial c M z * star (finiteAntiPolynomial c M z) ∂volume) =
        (Real.pi : ℂ)⁻¹ *
          (∫ z in D, ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M,
            (c j * star (c k)) * ((conj z) ^ j * z ^ k) ∂volume) := by
          congr 1
          apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
          intro z hz
          exact hpoint z
    _ = ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M,
          (c j * star (c k)) *
            (if j = k then (j + 1 : ℂ)⁻¹ else 0) := by
          have houter :
              (∫ z in D, ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M,
                (c j * star (c k)) * ((conj z) ^ j * z ^ k) ∂volume) =
              ∑ j ∈ Finset.range M,
                (∫ z in D, ∑ k ∈ Finset.range M,
                  (c j * star (c k)) * ((conj z) ^ j * z ^ k) ∂volume) := by
            simpa only [Finset.sum_apply] using
              (integral_finsetSum (Finset.range M)
                (f := fun j z => ∑ k ∈ Finset.range M,
                  (c j * star (c k)) * ((conj z) ^ j * z ^ k))
                (fun j hj => houterInt j))
          have hinner (j : ℕ) :
              (∫ z in D, ∑ k ∈ Finset.range M,
                (c j * star (c k)) * ((conj z) ^ j * z ^ k) ∂volume) =
              ∑ k ∈ Finset.range M,
                (∫ z in D,
                  (c j * star (c k)) * ((conj z) ^ j * z ^ k) ∂volume) := by
            simpa only [Finset.sum_apply] using
              (integral_finsetSum (Finset.range M)
                (f := fun k z => (c j * star (c k)) * ((conj z) ^ j * z ^ k))
                (fun k hk => hint j k))
          rw [houter]
          simp_rw [hinner]
          simp_rw [integral_const_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          calc
            (Real.pi : ℂ)⁻¹ *
                ((c j * star (c k)) *
                  (∫ z in D, (conj z) ^ j * z ^ k ∂volume)) =
                (c j * star (c k)) *
                  ((Real.pi : ℂ)⁻¹ *
                    (∫ z in D, z ^ k * (conj z) ^ j ∂volume)) := by
                    have hswap :
                        (∫ z in D, (conj z) ^ j * z ^ k ∂volume) =
                          (∫ z in D, z ^ k * (conj z) ^ j ∂volume) := by
                      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
                      intro z hz
                      ring
                    rw [hswap]
                    ring
            _ = (c j * star (c k)) *
                (if j = k then (j + 1 : ℂ)⁻¹ else 0) := by
                  rw [unitDisk_monomial_integral k j]
                  by_cases hjk : j = k
                  · subst k
                    simp
                  · simp [hjk, Ne.symm hjk]
    _ = ∑ j ∈ Finset.range M, (c j * star (c j)) / (j + 1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [hj, div_eq_mul_inv]

/-- Finite disk Parseval for the squared complex modulus. -/
theorem finiteAntiPolynomial_energy (c : ℕ → ℂ) (M : ℕ) :
    (Real.pi)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖finiteAntiPolynomial c M z‖ ^ 2 ∂volume) =
      ∑ j ∈ Finset.range M, ‖c j‖ ^ 2 / (j + 1 : ℝ) := by
  apply Complex.ofReal_injective
  calc
    (((Real.pi)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖finiteAntiPolynomial c M z‖ ^ 2 ∂volume) : ℝ) : ℂ) =
        (Real.pi : ℂ)⁻¹ *
          (∫ z in Metric.ball (0 : ℂ) 1,
            finiteAntiPolynomial c M z * star (finiteAntiPolynomial c M z) ∂volume) := by
          push_cast
          rw [← integral_complex_ofReal]
          congr 1
          apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
          intro z hz
          change ((‖finiteAntiPolynomial c M z‖ ^ 2 : ℝ) : ℂ) =
            finiteAntiPolynomial c M z * conj (finiteAntiPolynomial c M z)
          rw [Complex.mul_conj']
          norm_cast
    _ = ∑ j ∈ Finset.range M,
          (c j * star (c j)) / (j + 1 : ℂ) :=
      finiteAntiPolynomial_complex_energy c M
    _ = ((∑ j ∈ Finset.range M, ‖c j‖ ^ 2 / (j + 1 : ℝ) : ℝ) : ℂ) := by
          push_cast
          apply Finset.sum_congr rfl
          intro j hj
          rw [Complex.star_def, Complex.mul_conj']

/-- Parseval for the derivative of any analytic function extending across
the unit circle. The coefficient series is proved convergent by the identity. -/
theorem analytic_deriv_disk_energy
    (h : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 R)) :
    HasSum
      (fun j : ℕ =>
        ‖(j + 1 : ℂ) * actualTaylorCoeff h (j + 1)‖ ^ 2 / (j + 1 : ℝ))
      ((Real.pi)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖deriv h (conj z)‖ ^ 2 ∂volume)) := by
  let D : Set ℂ := Metric.ball 0 1
  let c : ℕ → ℂ := fun j => (j + 1 : ℂ) * actualTaylorCoeff h (j + 1)
  let P : ℕ → ℂ → ℝ := fun M z => ‖finiteAntiPolynomial c M z‖ ^ 2
  let Q : ℂ → ℝ := fun z => ‖deriv h (conj z)‖ ^ 2
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hvol : volume D ≠ ∞ := by
    rw [Complex.volume_ball]
    finiteness
  have hderCont : ContinuousOn (deriv h) (Metric.closedBall (0 : ℂ) 1) :=
    hh.deriv.continuousOn.mono (Metric.closedBall_subset_ball hR)
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
  have hBnonneg : 0 ≤ B :=
    (norm_nonneg (deriv h 0)).trans (hderBound 0 (by simp))
  have hu := analytic_deriv_uniform_closedUnitDisk h hR hh
  have hpoint : ∀ᵐ z ∂(volume.restrict D),
      Tendsto (fun M => P M z) Filter.atTop (𝓝 (Q z)) := by
    filter_upwards [ae_restrict_mem hD] with z hz
    have hzcl : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.ball_subset_closedBall hz
    have ht := hu.tendsto_at (hconjMaps hzcl)
    have ht' := (continuous_norm.pow 2).tendsto _ |>.comp ht
    simpa [Function.comp_def, Pi.pow_apply, P, Q, finiteAntiPolynomial, c] using ht'
  have hevent : ∀ᶠ M in Filter.atTop,
      ∀ u ∈ Metric.closedBall (0 : ℂ) 1,
        dist (deriv h u)
          (∑ j ∈ Finset.range M, c j * u ^ j) < 1 := by
    simpa only [c] using
      (Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)
  have hmeas : ∀ᶠ M in Filter.atTop,
      AEStronglyMeasurable (P M) (volume.restrict D) := by
    filter_upwards [] with M
    have hcont : Continuous (P M) := by
      dsimp [P, finiteAntiPolynomial]
      fun_prop
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᶠ M in Filter.atTop,
      ∀ᵐ z ∂(volume.restrict D), ‖P M z‖ ≤ (B + 1) ^ 2 := by
    filter_upwards [hevent] with M hM
    filter_upwards [ae_restrict_mem hD] with z hz
    have hzcl : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.ball_subset_closedBall hz
    have hzconj := hconjMaps hzcl
    have hd := hM (conj z) hzconj
    have hP : ‖finiteAntiPolynomial c M z‖ ≤ B + 1 := by
      calc
        ‖finiteAntiPolynomial c M z‖ ≤
            ‖deriv h (conj z)‖ +
              dist (deriv h (conj z)) (finiteAntiPolynomial c M z) := by
                rw [dist_eq_norm]
                have htri := norm_add_le (deriv h (conj z))
                  (finiteAntiPolynomial c M z - deriv h (conj z))
                rw [show deriv h (conj z) +
                  (finiteAntiPolynomial c M z - deriv h (conj z)) =
                    finiteAntiPolynomial c M z by ring] at htri
                simpa only [norm_sub_rev] using htri
        _ ≤ B + 1 := by
          have hd' : dist (deriv h (conj z))
              (finiteAntiPolynomial c M z) < 1 := by
            simpa only [finiteAntiPolynomial, c] using hd
          linarith [hderBound (conj z) hzconj]
    dsimp [P]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hP 2
  have hconst : Integrable (fun _ : ℂ => (B + 1) ^ 2)
      (volume.restrict D) := integrableOn_const hvol
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℂ => (B + 1) ^ 2) hmeas hbound hconst hpoint
  have hlim' : Filter.Tendsto
      (fun M : ℕ => (Real.pi)⁻¹ *
        (∫ z in D, P M z ∂volume)) Filter.atTop
      (𝓝 ((Real.pi)⁻¹ * (∫ z in D, Q z ∂volume))) :=
    tendsto_const_nhds.mul hlim
  have hnonneg (j : ℕ) :
      0 ≤ ‖(j + 1 : ℂ) * actualTaylorCoeff h (j + 1)‖ ^ 2 /
        (j + 1 : ℝ) := by positivity
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).mpr
  convert hlim' using 1
  · funext M
    exact (finiteAntiPolynomial_energy c M).symm

/-- The regularized derivative energy is the weighted coefficient series of
the same actual dilate; each coefficient has the verified `s^(j+1)` scale. -/
theorem regularForwardGerm_deriv_energy_hasSum
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasSum
      (fun j : ℕ => (j + 1 : ℝ) *
        ‖exteriorForwardCoeff (rescaleExterior s F) (j + 1)‖ ^ 2)
      ((Real.pi)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2 ∂volume)) := by
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hga := regularForwardGerm_analyticOnNhd F hc hs0
  have hs := analytic_deriv_disk_energy (regularForwardGerm s F) hR hga
  have hterm (j : ℕ) :
      ‖(j + 1 : ℂ) * actualTaylorCoeff (regularForwardGerm s F) (j + 1)‖ ^ 2 /
        (j + 1 : ℝ) =
      (j + 1 : ℝ) *
        ‖exteriorForwardCoeff (rescaleExterior s F) (j + 1)‖ ^ 2 := by
    rw [regularForwardGerm_eq_actual s hs0 F, actualTaylorCoeff_forward]
    rw [norm_mul]
    have hn : ‖(j + 1 : ℂ)‖ = (j + 1 : ℝ) := by
      norm_cast
    rw [hn]
    have hj : (j + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  simpa only [hterm] using hs

end SpringerLean
