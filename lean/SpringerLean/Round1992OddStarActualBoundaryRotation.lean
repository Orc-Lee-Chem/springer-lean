import SpringerLean.Round1991OddStarOuterLawLimit

open MeasureTheory Filter Set
open scoped Topology

namespace SpringerLean

/-- The actual a.e. radial boundary probability of the odd-star map is
invariant under every m-th-root rotation.  This is obtained from exact
smooth-circle invariance and bounded-continuous-test convergence. -/
theorem oddStarActualBoundaryProbability_map_rotation
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (δ : ℝ)
    (hη : (Complex.polarCoord.symm (1, δ) : ℂ) ^ m = 1) :
    (oddStarActualBoundaryProbability m t).map
      (fun u : ℂ => Complex.polarCoord.symm (1, δ) * u) =
        oddStarActualBoundaryProbability m t := by
  let η : ℂ := Complex.polarCoord.symm (1, δ)
  let ν : Measure ℂ := oddStarActualBoundaryProbability m t
  haveI : IsFiniteMeasure ν := by
    dsimp [ν, oddStarActualBoundaryProbability]
    exact Measure.isFiniteMeasure_map oddStarAngularProbability _
  haveI : IsFiniteMeasure (ν.map (fun u : ℂ => η * u)) :=
    Measure.isFiniteMeasure_map ν _
  have hrot : Measurable (fun u : ℂ => η * u) := by fun_prop
  change ν.map (fun u : ℂ => η * u) = ν
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map hrot.aemeasurable φ.continuous.aestronglyMeasurable]
  let ψ : BoundedContinuousFunction ℂ ℝ :=
    φ.compContinuous ⟨(fun u : ℂ => η * u), by fun_prop⟩
  have hψ (u : ℂ) : ψ u = φ (η * u) := rfl
  have hlimψ := oddStarOuterCircleProbability_integral_tendsto_actual
    m hm t ht ψ
  have hlimφ := oddStarOuterCircleProbability_integral_tendsto_actual
    m hm t ht φ
  have hnear : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      0 < s ∧ s < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
    exact hs
  have heq : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      (∫ u, ψ u ∂oddStarOuterCircleProbability m t s) =
        ∫ u, φ u ∂oddStarOuterCircleProbability m t s := by
    filter_upwards [hnear] with s hs
    rw [show (∫ u, ψ u ∂oddStarOuterCircleProbability m t s) =
        ∫ u, φ (η * u) ∂oddStarOuterCircleProbability m t s by
          apply integral_congr_ae
          filter_upwards with u
          exact hψ u]
    rw [← integral_map hrot.aemeasurable
      φ.continuous.aestronglyMeasurable]
    exact congrArg (fun ρ : Measure ℂ => ∫ u, φ u ∂ρ)
      (oddStarOuterCircleProbability_map_rotation
        m hm t ht s hs δ hη)
  have hsame := tendsto_nhds_unique (hlimψ.congr' heq) hlimφ
  simpa [ν, ψ, BoundedContinuousFunction.compContinuous_apply] using hsame

end SpringerLean

#print axioms SpringerLean.oddStarActualBoundaryProbability_map_rotation
