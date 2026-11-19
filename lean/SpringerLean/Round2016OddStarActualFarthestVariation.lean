import SpringerLean.Round2015OddStarFarthestMeasureTransfer

open MeasureTheory Set

namespace SpringerLean
open scoped Topology

theorem oddStarSeedBoundaryProbability_integral_measurable
    (t : ℝ) (ht : |t| < 1) (φ : ℂ → ℝ) (hφ : Measurable φ) :
    (∫ v, φ v ∂oddStarSeedBoundaryProbability t) =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          φ (oddStarSeed t (Complex.exp ((θ : ℂ) * Complex.I)))) := by
  let g : ℝ → ℝ := fun θ =>
    φ (oddStarSeed t (Complex.polarCoord.symm (1, θ)))
  have hgperiod : Function.Periodic g (2 * Real.pi) :=
    oddStarSeed_boundary_test_periodic t φ
  have hshift :
      (∫ θ in Ioo (-Real.pi) Real.pi, g θ) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
    have hset :
        (∫ θ in Ioo (-Real.pi) Real.pi, g θ) =
          ∫ θ in -Real.pi..Real.pi, g θ := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        integral_Ioc_eq_integral_Ioo]
    rw [hset]
    convert hgperiod.intervalIntegral_add_eq (-Real.pi) 0 using 1 <;> ring_nf
  have hmap :
      (∫ v, φ v ∂oddStarSeedBoundaryProbability t) =
        (2 * Real.pi)⁻¹ *
          (∫ θ in Ioo (-Real.pi) Real.pi, g θ) := by
    unfold oddStarSeedBoundaryProbability oddStarAngularProbability
    rw [integral_map
      (oddStarSeed_angle_continuous t ht).measurable.aemeasurable
      hφ.aestronglyMeasurable]
    rw [integral_smul_measure]
    simp only [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (by positivity :
      0 < 2 * Real.pi)))]
    simp only [smul_eq_mul]
    rfl
  rw [hmap, hshift]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [g, Complex.polarCoord_symm_apply]
  rw [Complex.exp_mul_I]
  simp

theorem oddStarSeed_boundary_integral_rotate_angle
    (t : ℝ) (ht : |t| < 1) (φ : ℂ → ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      φ (oddStarSeed t (oddStarAlpha t *
        Complex.exp ((θ : ℂ) * Complex.I)))) =
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      φ (oddStarSeed t (Complex.exp ((θ : ℂ) * Complex.I)))) := by
  obtain ⟨a, ha⟩ := (Complex.norm_eq_one_iff (oddStarAlpha t)).mp
    (oddStarAlpha_norm_eq_one t ht)
  let g : ℝ → ℝ := fun θ =>
    φ (oddStarSeed t (Complex.exp ((θ : ℂ) * Complex.I)))
  have hgperiod : Function.Periodic g (2 * Real.pi) := by
    intro θ
    have h : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
      simpa only [Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_ofNat] using (Complex.exp_mul_I_periodic (θ : ℂ))
    exact congrArg (fun z => φ (oddStarSeed t z)) h
  have hshift (θ : ℝ) :
      oddStarAlpha t * Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp (((θ + a : ℝ) : ℂ) * Complex.I) := by
    rw [← ha, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      φ (oddStarSeed t (oddStarAlpha t *
        Complex.exp ((θ : ℂ) * Complex.I)))) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, g (θ + a) := by
          apply intervalIntegral.integral_congr
          intro θ _
          exact congrArg (fun z => φ (oddStarSeed t z)) (hshift θ)
    _ = ∫ θ in a..2 * Real.pi + a, g θ := by
      simpa using (intervalIntegral.integral_comp_add_right (f := g)
        (a := 0) (b := 2 * Real.pi) a)
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
      convert hgperiod.intervalIntegral_add_eq a 0 using 1 <;> ring

theorem oddStarFarthestLog_seed_reparametrized
    (m : ℕ) (hm : 3 ≤ m) (t : ℝ) (ht : |t| < 1)
    (hfactor : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      oddStarBoundaryFactor
        (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m t)
        ((oddStarSeed t (oddStarAlpha t *
          Complex.exp ((θ : ℂ) * Complex.I))) ^ ((m : ℂ)⁻¹)))) =
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m t)
        (oddStarMovingBoundaryPoint m
          (oddStarBoundaryRadius m θ) θ t))) := by
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hpow := oddStarMovingBoundaryPoint_pow_eq_seed
    m hm t θ (hfactor θ (by simpa only [Set.uIcc_of_le (by positivity :
      (0 : ℝ) ≤ 2 * Real.pi)] using hθ))
  have hfiber := oddStarFarthestDistance_factors_through_power
    m (by omega) t ht
      (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t)
  rw [hpow] at hfiber
  exact congrArg Real.log hfiber.symm

theorem oddStarActualBoundaryProbability_farthestLog_angular_transfer
    (m : ℕ) (hm : 3 ≤ m) :
    ∃ U : Set ℝ, U ∈ 𝓝 (0 : ℝ) ∧
      ∀ t ∈ U,
        (∫ z : ℂ,
          Real.log (continuumFarthestDistance
            (oddStarPerturbationOmitted m t) z)
          ∂oddStarActualBoundaryProbability m t) =
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..2 * Real.pi,
            Real.log (continuumFarthestDistance
              (oddStarPerturbationOmitted m t)
              (oddStarMovingBoundaryPoint m
                (oddStarBoundaryRadius m θ) θ t))) := by
  obtain ⟨U, hU, hreg⟩ := oddStarVariation_uniform_regular_domain m hm
  let V : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hV : V ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds isOpen_Ioo
    norm_num [V]
  refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
  intro t ht
  have ht1 : |t| < 1 := by simpa [V, abs_lt] using ht.2
  let φ : ℂ → ℝ := fun v =>
    Real.log (continuumFarthestDistance
      (oddStarPerturbationOmitted m t) (v ^ ((m : ℂ)⁻¹)))
  have hφ : Measurable φ :=
    oddStarFarthestLog_principalRoot_measurable m (by omega) t ht1
  have hfactor (θ : ℝ)
      (hθ : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
      oddStarBoundaryFactor
        (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0 :=
    Complex.slitPlane_ne_zero (hreg t ht.1 θ hθ).2.1
  calc
    (∫ z : ℂ,
      Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m t) z)
      ∂oddStarActualBoundaryProbability m t) =
        ∫ v : ℂ, φ v ∂oddStarSeedBoundaryProbability t :=
          oddStarActualBoundaryProbability_farthestLog_seed_transfer
            m (by omega) t ht1
    _ = (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..2 * Real.pi,
            φ (oddStarSeed t (Complex.exp ((θ : ℂ) * Complex.I)))) :=
          oddStarSeedBoundaryProbability_integral_measurable t ht1 φ hφ
    _ = (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..2 * Real.pi,
            φ (oddStarSeed t (oddStarAlpha t *
              Complex.exp ((θ : ℂ) * Complex.I)))) := by
          congr 1
          exact (oddStarSeed_boundary_integral_rotate_angle t ht1 φ).symm
    _ = (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..2 * Real.pi,
            Real.log (continuumFarthestDistance
              (oddStarPerturbationOmitted m t)
              (oddStarMovingBoundaryPoint m
                (oddStarBoundaryRadius m θ) θ t))) := by
          congr 1
          exact oddStarFarthestLog_seed_reparametrized m hm t ht1 hfactor

theorem oddStarActualBoundaryProbability_exists_strict_farthestLog
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ t : ℝ, 0 < t ∧ |t| < 1 ∧
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          oddStarOppositeTipLogDistance m θ 0) <
      (∫ z : ℂ,
        Real.log (continuumFarthestDistance
          (oddStarPerturbationOmitted m t) z)
        ∂oddStarActualBoundaryProbability m t) := by
  obtain ⟨U, hU, hfar⟩ :=
    oddStarOppositeTipLogDistance_integral_le_farthestLog m hm hodd
  obtain ⟨V, hV, htransfer⟩ :=
    oddStarActualBoundaryProbability_farthestLog_angular_transfer m hm
  let W : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hW : W ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds isOpen_Ioo
    norm_num [W]
  obtain ⟨t, ht, htpos, hinc⟩ :=
    oddStarOppositeTipLogDistance_integral_strict_increase_near_zero
      m hm (U ∩ V ∩ W)
      (Filter.inter_mem (Filter.inter_mem hU hV) hW)
  have ht1 : |t| < 1 := by simpa [W, abs_lt] using ht.2
  have hfar' := hfar t ht.1.1
  have htransfer' := htransfer t ht.1.2
  have hscale : 0 < (2 * Real.pi)⁻¹ := by positivity
  refine ⟨t, htpos, ht1, ?_⟩
  rw [htransfer']
  exact (mul_lt_mul_of_pos_left hinc hscale).trans_le
    (mul_le_mul_of_nonneg_left hfar' hscale.le)

end SpringerLean
