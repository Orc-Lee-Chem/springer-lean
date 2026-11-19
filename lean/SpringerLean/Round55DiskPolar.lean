import SpringerLean.DiskPolar
import SpringerLean.Round54SecondMoment

open MeasureTheory

namespace SpringerLean

/-- Tonelli's polar formula for an arbitrary measurable nonnegative
integrand on the open complex unit disk. -/
theorem unitDisk_lintegral_polar
    (g : ℂ → ENNReal) (hg : Measurable g) :
    (∫⁻ z in Metric.ball (0 : ℂ) 1, g z ∂volume) =
      ∫⁻ ρ in Set.Ioo (0 : ℝ) 1,
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal ρ * g (Complex.polarCoord.symm (ρ, θ)) ∂volume
        ∂volume := by
  let φ : ℝ × ℝ → ℂ := fun p => Complex.polarCoord.symm p
  let D : Set ℂ := Metric.ball 0 1
  let f : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal p.1 * g (φ p)
  have hφcont : Continuous φ := by
    have heq : φ = fun p : ℝ × ℝ =>
        (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [heq]
    fun_prop
  have hφ : Measurable φ := hφcont.measurable
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hpre : MeasurableSet (φ ⁻¹' D) := hD.preimage hφ
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hindicator (p : ℝ × ℝ) :
      ENNReal.ofReal p.1 * D.indicator g (φ p) =
        (φ ⁻¹' D).indicator f p := by
    by_cases hp : φ p ∈ D
    · simp [Set.indicator_of_mem, hp, f]
    · simp [Set.indicator_of_notMem, hp, f]
  calc
    (∫⁻ z in D, g z ∂volume) =
        ∫⁻ z, D.indicator g z ∂volume := by
          exact (lintegral_indicator hD g).symm
    _ = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 * D.indicator g (φ p) ∂volume := by
          rw [Complex.polarCoord_target]
          simpa [φ, smul_eq_mul] using
            (Complex.lintegral_comp_polarCoord_symm (D.indicator g)).symm
    _ = ∫⁻ p in Complex.polarCoord.target,
          (φ ⁻¹' D).indicator f p ∂volume := by
          apply setLIntegral_congr_fun
            (by rw [Complex.polarCoord_target]
                exact measurableSet_Ioi.prod measurableSet_Ioo)
          intro p hp
          exact hindicator p
    _ = ∫⁻ p in Complex.polarCoord.target ∩ φ ⁻¹' D,
          f p ∂volume := by
          simpa only [Set.inter_comm] using
            (setLIntegral_indicator
              (t := Complex.polarCoord.target) hpre f)
    _ = ∫⁻ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi,
          f p ∂volume := by
          rw [unitDisk_polar_preimage]
    _ = ∫⁻ ρ in Set.Ioo (0 : ℝ) 1,
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal ρ * g (Complex.polarCoord.symm (ρ, θ)) ∂volume
          ∂volume := by
          rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
          simpa only [f, φ] using
            (setLIntegral_prod f hf.aemeasurable)

/-- The actual harmonic filling's nonnegative second moment has a genuine
polar Tonelli representation, without assuming any boundary trace. -/
theorem actualHarmonic_sq_lintegral_polar
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (‖actualHarmonic F z‖ ^ 2) ∂volume) =
      ∫⁻ ρ in Set.Ioo (0 : ℝ) 1,
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal ρ *
            ENNReal.ofReal
              (‖actualHarmonic F (Complex.polarCoord.symm (ρ, θ))‖ ^ 2)
          ∂volume ∂volume := by
  let D : Set ℂ := Metric.ball 0 1
  classical
  let q : ℂ → ℝ := fun z => ‖actualHarmonic F z‖ ^ 2
  let qExt : ℂ → ℝ := D.piecewise q (fun _ => 0)
  let g : ℂ → ENNReal := fun z => ENNReal.ofReal (qExt z)
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hqcont : ContinuousOn q D :=
    (actualHarmonic_continuousOn_unitBall F hc).norm.pow 2
  have hqmeas : Measurable qExt :=
    ContinuousOn.measurable_piecewise hqcont continuousOn_const hD
  have hg : Measurable g := ENNReal.measurable_ofReal.comp hqmeas
  have hpoint (z : ℂ) (hz : z ∈ D) :
      g z = ENNReal.ofReal (‖actualHarmonic F z‖ ^ 2) := by
    simp [g, qExt, q, Set.piecewise, hz]
  have hpolar (ρ θ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) :
      Complex.polarCoord.symm (ρ, θ) ∈ D := by
    simpa only [D, Metric.mem_ball, dist_zero_right,
      Complex.norm_polarCoord_symm, abs_of_pos hρ.1] using hρ.2
  calc
    (∫⁻ z in D, ENNReal.ofReal (‖actualHarmonic F z‖ ^ 2) ∂volume) =
      ∫⁻ z in D, g z ∂volume := by
        apply setLIntegral_congr_fun hD
        intro z hz
        exact (hpoint z hz).symm
    _ = ∫⁻ ρ in Set.Ioo (0 : ℝ) 1,
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal ρ *
              g (Complex.polarCoord.symm (ρ, θ)) ∂volume ∂volume :=
          unitDisk_lintegral_polar g hg
    _ = ∫⁻ ρ in Set.Ioo (0 : ℝ) 1,
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal ρ *
              ENNReal.ofReal
                (‖actualHarmonic F (Complex.polarCoord.symm (ρ, θ))‖ ^ 2)
            ∂volume ∂volume := by
          apply setLIntegral_congr_fun measurableSet_Ioo
          intro ρ hρ
          apply setLIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          change ENNReal.ofReal ρ * g (Complex.polarCoord.symm (ρ, θ)) = _
          rw [hpoint _ (hpolar ρ θ hρ)]
end SpringerLean
