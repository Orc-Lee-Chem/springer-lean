import SpringerLean.PolarAnnulus

open MeasureTheory

namespace SpringerLean

/-- Tonelli's polar-coordinate formula on an open annulus, expressed without
any regularity or boundary assumptions on the integrand beyond measurability. -/
theorem exteriorAnnulus_lintegral_polar
    {r R : ℝ} (hr : 0 < r) (g : ℂ → ENNReal) (hg : Measurable g) :
    (∫⁻ z in exteriorAnnulus r R, g z ∂volume) =
      ∫⁻ ρ in Set.Ioo r R,
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal ρ * g (Complex.polarCoord.symm (ρ, θ)) ∂volume
        ∂volume := by
  let φ : ℝ × ℝ → ℂ := fun p => Complex.polarCoord.symm p
  let A : Set ℂ := exteriorAnnulus r R
  let f : ℝ × ℝ → ENNReal :=
    fun p => ENNReal.ofReal p.1 * g (φ p)
  have hφcont : Continuous φ := by
    have hφeq : φ = fun p : ℝ × ℝ =>
        (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [hφeq]
    fun_prop
  have hφmeas : Measurable φ := hφcont.measurable
  have hA : MeasurableSet A := (exteriorAnnulus_isOpen r R).measurableSet
  have hpre : MeasurableSet (φ ⁻¹' A) := hA.preimage hφmeas
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hindicator (p : ℝ × ℝ) :
      ENNReal.ofReal p.1 * A.indicator g (φ p) =
        (φ ⁻¹' A).indicator f p := by
    by_cases hp : φ p ∈ A
    · simp [Set.indicator_of_mem, hp, f]
    · simp [Set.indicator_of_notMem, hp, f]
  calc
    (∫⁻ z in exteriorAnnulus r R, g z ∂volume) =
        ∫⁻ z, A.indicator g z ∂volume := by
          exact (lintegral_indicator hA g).symm
    _ = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 * A.indicator g (φ p) ∂volume := by
          rw [Complex.polarCoord_target]
          simpa [φ, smul_eq_mul] using
            (Complex.lintegral_comp_polarCoord_symm (A.indicator g)).symm
    _ = ∫⁻ p in Complex.polarCoord.target,
          (φ ⁻¹' A).indicator f p ∂volume := by
          apply setLIntegral_congr_fun
            (by rw [Complex.polarCoord_target]
                exact measurableSet_Ioi.prod measurableSet_Ioo)
          intro p hp
          exact hindicator p
    _ = ∫⁻ p in Complex.polarCoord.target ∩ φ ⁻¹' A,
          f p ∂volume := by
          simpa only [Set.inter_comm] using
            (setLIntegral_indicator
              (t := Complex.polarCoord.target) hpre f)
    _ = ∫⁻ p in Set.Ioo r R ×ˢ Set.Ioo (-Real.pi) Real.pi,
          f p ∂volume := by
          rw [exteriorAnnulus_polar_preimage_inter hr]
    _ = ∫⁻ ρ in Set.Ioo r R,
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal ρ * g (Complex.polarCoord.symm (ρ, θ)) ∂volume
          ∂volume := by
          rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
          simpa only [f, φ] using
            (setLIntegral_prod f hf.aemeasurable)

/-- The image-area Jacobian integral equals a polar integral of the actual
derivative on the same annulus. The derivative is extended by zero outside
the annulus solely for the global measurability interface. -/
theorem exteriorAnnulus_deriv_sq_lintegral_polar
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r R : ℝ} (hr : 1 < r) :
    (∫⁻ z in exteriorAnnulus r R,
      ENNReal.ofReal (‖deriv F z‖ ^ 2) ∂volume) =
      ∫⁻ ρ in Set.Ioo r R,
        ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal ρ *
            ENNReal.ofReal
              (‖deriv F (exteriorCirclePoint ρ
                (θ : AddCircle (2 * Real.pi)))‖ ^ 2) ∂volume
        ∂volume := by
  classical
  let A : Set ℂ := exteriorAnnulus r R
  let q : ℂ → ℝ := fun z => ‖deriv F z‖ ^ 2
  let q₀ : ℂ → ℝ := A.piecewise q (fun _ => 0)
  let g : ℂ → ENNReal := fun z => ENNReal.ofReal (q₀ z)
  have hA : MeasurableSet A := (exteriorAnnulus_isOpen r R).measurableSet
  have hderiv : ContinuousOn (deriv F) A :=
    ((hc.1.analyticOnNhd exteriorDisk_isOpen).deriv).continuousOn.mono
      (exteriorAnnulus_subset_exteriorDisk hr)
  have hq : ContinuousOn q A := hderiv.norm.pow 2
  have hq₀ : Measurable q₀ :=
    hq.measurable_piecewise continuous_const.continuousOn hA
  have hg : Measurable g := ENNReal.measurable_ofReal.comp hq₀
  have hpolar := exteriorAnnulus_lintegral_polar
    (r := r) (R := R) (by linarith : 0 < r) g hg
  calc
    (∫⁻ z in exteriorAnnulus r R,
        ENNReal.ofReal (‖deriv F z‖ ^ 2) ∂volume) =
        (∫⁻ z in exteriorAnnulus r R, g z ∂volume) := by
          apply setLIntegral_congr_fun hA
          intro z hz
          change ENNReal.ofReal (q z) =
            ENNReal.ofReal (A.piecewise q (fun _ => 0) z)
          rw [Set.piecewise_eq_of_mem A q (fun _ => 0) hz]
    _ = ∫⁻ ρ in Set.Ioo r R,
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal ρ * g (Complex.polarCoord.symm (ρ, θ)) ∂volume
          ∂volume := hpolar
    _ = ∫⁻ ρ in Set.Ioo r R,
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal ρ *
              ENNReal.ofReal
                (‖deriv F (exteriorCirclePoint ρ
                  (θ : AddCircle (2 * Real.pi)))‖ ^ 2) ∂volume
          ∂volume := by
          apply setLIntegral_congr_fun measurableSet_Ioo
          intro ρ hρ
          apply setLIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          have hptarget : (ρ, θ) ∈ Complex.polarCoord.target := by
            change (ρ, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi
            exact ⟨lt_trans (by linarith : 0 < r) hρ.1, hθ⟩
          have hmem : Complex.polarCoord.symm (ρ, θ) ∈ A :=
            (exteriorAnnulus_polar_iff r R (ρ, θ) hptarget).mpr hρ
          change ENNReal.ofReal ρ * g (Complex.polarCoord.symm (ρ, θ)) =
            ENNReal.ofReal ρ * ENNReal.ofReal
              (‖deriv F (exteriorCirclePoint ρ
                (θ : AddCircle (2 * Real.pi)))‖ ^ 2)
          rw [show g (Complex.polarCoord.symm (ρ, θ)) =
            ENNReal.ofReal (‖deriv F (Complex.polarCoord.symm (ρ, θ))‖ ^ 2) by
              change ENNReal.ofReal
                (A.piecewise q (fun _ => 0) (Complex.polarCoord.symm (ρ, θ))) =
                ENNReal.ofReal (q (Complex.polarCoord.symm (ρ, θ)))
              rw [Set.piecewise_eq_of_mem A q (fun _ => 0) hmem]]
          rw [exteriorCirclePoint_eq_polarCoord_symm]

end SpringerLean
