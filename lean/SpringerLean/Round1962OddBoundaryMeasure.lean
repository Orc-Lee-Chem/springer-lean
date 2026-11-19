import SpringerLean.Round1961OddStarActualPushforward
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

open MeasureTheory Set

namespace SpringerLean

/-- Angular Lebesgue measure on one centered turn of the circle. -/
noncomputable def oddStarAngularMeasure : Measure ℝ :=
  volume.restrict (Ioo (-Real.pi) Real.pi)

/-- The distribution of the actual a.e. radial boundary values of the
centered exterior map, without choosing a separate abstract trace. -/
noncomputable def oddStarActualBoundaryMeasure (m : ℕ) (t : ℝ) : Measure ℂ :=
  oddStarAngularMeasure.map
    (actualExteriorRadialTrace (oddStarPerturbation m t))

/-- The boundary distribution of the rational seed. -/
noncomputable def oddStarSeedBoundaryMeasure (t : ℝ) : Measure ℂ :=
  oddStarAngularMeasure.map
    (fun θ => oddStarSeed t (Complex.polarCoord.symm (1, θ)))

theorem oddStarSeed_angle_continuous (t : ℝ) (ht : |t| < 1) :
    Continuous (fun θ : ℝ =>
      oddStarSeed t (Complex.polarCoord.symm (1, θ))) := by
  have hpolar : Continuous (fun θ : ℝ =>
      Complex.polarCoord.symm (1, θ)) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  apply (oddStarSeed_continuousOn_circle t ht).comp_continuous hpolar
  intro θ
  simp [oddStarSeedUnitCircle]

/-- The m-th power pushes the actual angular boundary measure of the
star perturbation to the seed boundary measure. This is an equality of
finite Borel measures, not merely of selected moments. -/
theorem oddStarPerturbation_actual_boundary_measure_map_pow
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    (oddStarActualBoundaryMeasure m t).map (fun z : ℂ => z ^ m) =
      oddStarSeedBoundaryMeasure t := by
  let μ : Measure ℝ := oddStarAngularMeasure
  let f : ℝ → ℂ := actualExteriorRadialTrace (oddStarPerturbation m t)
  let g : ℝ → ℂ := fun θ => oddStarSeed t (Complex.polarCoord.symm (1, θ))
  haveI : IsFiniteMeasure μ := by
    dsimp [μ, oddStarAngularMeasure]
    infer_instance
  have hf : AEMeasurable f μ := by
    exact (actualExteriorRadialTrace_aestronglyMeasurable
      (oddStarPerturbation m t)
      (oddStarPerturbation_centeredExteriorUnivalent m hm t ht)).aemeasurable
  have hg : Measurable g := (oddStarSeed_angle_continuous t ht).measurable
  have hpow : Measurable (fun z : ℂ => z ^ m) := by fun_prop
  have hmap : (μ.map f).map (fun z : ℂ => z ^ m) =
      μ.map (fun θ => (f θ) ^ m) := by
    exact AEMeasurable.map_map_of_aemeasurable hpow.aemeasurable hf
  change (μ.map f).map (fun z : ℂ => z ^ m) = μ.map g
  rw [hmap]
  haveI : IsFiniteMeasure (μ.map (fun θ => (f θ) ^ m)) :=
    Measure.isFiniteMeasure_map μ _
  haveI : IsFiniteMeasure (μ.map g) := Measure.isFiniteMeasure_map μ _
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  have hf_pow : AEMeasurable (fun θ => (f θ) ^ m) μ :=
    hpow.aemeasurable.comp_aemeasurable hf
  rw [integral_map hf_pow φ.continuous.aestronglyMeasurable,
      integral_map hg.aemeasurable φ.continuous.aestronglyMeasurable]
  exact oddStarPerturbation_actual_radial_power_pushforward
    m hm t ht φ φ.continuous

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_actual_boundary_measure_map_pow
