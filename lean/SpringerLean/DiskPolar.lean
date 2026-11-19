import SpringerLean.RescaleGerm
import SpringerLean.PolarArea

open MeasureTheory

namespace SpringerLean

/-- The open unit disk in the positive-radius polar chart. -/
theorem unitDisk_polar_preimage :
    Complex.polarCoord.target ∩
      (fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹'
        Metric.ball (0 : ℂ) 1 =
      Set.Ioo 0 1 ×ˢ Set.Ioo (-Real.pi) Real.pi := by
  ext p
  constructor
  · rintro ⟨hp, hd⟩
    have hp0 : 0 < p.1 := by
      change p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi at hp
      exact hp.1
    have hpn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      simpa [abs_of_pos hp0] using Complex.norm_polarCoord_symm p
    have hd1 : p.1 < 1 := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, hpn] using hd
    exact ⟨⟨hp0, hd1⟩, hp.2⟩
  · rintro ⟨hr, hθ⟩
    have hp : p ∈ Complex.polarCoord.target := ⟨hr.1, hθ⟩
    have hpn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      simpa [abs_of_pos hr.1] using Complex.norm_polarCoord_symm p
    refine ⟨hp, ?_⟩
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, hpn] using hr.2

/-- Complex-valued integration over the unit disk in polar coordinates.
Continuity is enough for the compact-domain integrability needed by Fubini. -/
theorem unitDisk_integral_polar (f : ℂ → ℂ) (hf : Continuous f) :
    (∫ z in Metric.ball (0 : ℂ) 1, f z ∂volume) =
      ∫ ρ in Set.Ioo (0 : ℝ) 1,
        ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (ρ : ℂ) * f (Complex.polarCoord.symm (ρ, θ)) ∂volume ∂volume := by
  let D : Set ℂ := Metric.ball 0 1
  let φ : ℝ × ℝ → ℂ := fun p => Complex.polarCoord.symm p
  let q : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * f (φ p)
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hφcont : Continuous φ := by
    have heq : φ = fun p : ℝ × ℝ =>
        (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [heq]
    fun_prop
  have hφmeas : Measurable φ := hφcont.measurable
  have hpre : MeasurableSet (φ ⁻¹' D) := hD.preimage hφmeas
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hsubset : Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-Real.pi) Real.pi := by
    rintro p ⟨hr, hθ⟩
    exact ⟨⟨hr.1.le, hr.2.le⟩, ⟨hθ.1.le, hθ.2.le⟩⟩
  have hint : IntegrableOn q
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    (hqcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hsubset
  have hindicator (p : ℝ × ℝ) :
      p.1 • D.indicator f (φ p) = (φ ⁻¹' D).indicator (fun p => p.1 • f (φ p)) p := by
    by_cases hp : φ p ∈ D
    · simp [Set.indicator_of_mem, hp]
    · simp [Set.indicator_of_notMem, hp]
  calc
    (∫ z in Metric.ball (0 : ℂ) 1, f z ∂volume) =
        ∫ z, D.indicator f z ∂volume := by
          exact (integral_indicator hD).symm
    _ = ∫ p in Complex.polarCoord.target,
          p.1 • D.indicator f (φ p) ∂volume := by
          exact (Complex.integral_comp_polarCoord_symm (D.indicator f)).symm
    _ = ∫ p in Complex.polarCoord.target,
          (φ ⁻¹' D).indicator q p ∂volume := by
          apply setIntegral_congr_fun (by
            rw [Complex.polarCoord_target]
            exact measurableSet_Ioi.prod measurableSet_Ioo)
          intro p hp
          exact hindicator p
    _ = ∫ p in Complex.polarCoord.target ∩ φ ⁻¹' D,
          q p ∂volume := by
          exact setIntegral_indicator hpre
    _ = ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi,
          q p ∂volume := by
          rw [unitDisk_polar_preimage]
    _ = ∫ ρ in Set.Ioo (0 : ℝ) 1,
          ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            (ρ : ℂ) * f (Complex.polarCoord.symm (ρ, θ)) ∂volume ∂volume := by
          rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
          simpa only [q, φ] using setIntegral_prod q hint

end SpringerLean
