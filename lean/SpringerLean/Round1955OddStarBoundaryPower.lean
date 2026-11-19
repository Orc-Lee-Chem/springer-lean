import SpringerLean.Round1954SeedContinuum
import SpringerLean.Round1847ActualExteriorTrace

open MeasureTheory Filter Set
open scoped Topology

namespace SpringerLean

/-- The actual a.e. radial trace of the odd-star exterior map obeys
the power identity on the unit circle. The seed side uses its ordinary
continuous boundary value, without assigning it a centered trace. -/
theorem oddStarPerturbation_actual_radialTrace_pow
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      (actualExteriorRadialTrace (oddStarPerturbation m t) θ) ^ m =
        oddStarSeed t ((Complex.polarCoord.symm (1, θ)) ^ m) := by
  let F := oddStarPerturbation m t
  have hc := oddStarPerturbation_centeredExteriorUnivalent m hm t ht
  filter_upwards [actualExteriorRadialTrace_ae_tendsto F hc] with θ htrace
  let ζ : ℂ := Complex.polarCoord.symm (1, θ)
  let z : ℝ → ℂ := fun r => Complex.polarCoord.symm (r⁻¹, θ)
  have hζnorm : ‖ζ‖ = 1 := by
    simp [ζ, Complex.norm_polarCoord_symm]
  have hζmnorm : ‖ζ ^ m‖ = 1 := by
    rw [norm_pow, hζnorm, one_pow]
  have hζcircle : ζ ^ m ∈ oddStarSeedUnitCircle := by
    simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using hζmnorm
  have hden := oddStarSeed_denominator_ne_zero_on_circle t ht hζcircle
  have hGcont : ContinuousAt (oddStarSeed t) (ζ ^ m) := by
    unfold oddStarSeed
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hden
  have hzin : Tendsto z (𝓝[<] (1 : ℝ)) (𝓝 ζ) := by
    have hp : Continuous (fun r : ℝ => Complex.polarCoord.symm (r, θ)) := by
      simp_rw [Complex.polarCoord_symm_apply]
      fun_prop
    have hi : ContinuousAt (fun r : ℝ => r⁻¹) 1 :=
      continuousAt_id.inv₀ (by norm_num)
    simpa only [z, ζ, Function.comp_def, inv_one] using
      (hp.continuousAt.comp hi).tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have hseed : Tendsto (fun r => oddStarSeed t ((z r) ^ m))
      (𝓝[<] (1 : ℝ)) (𝓝 (oddStarSeed t (ζ ^ m))) :=
    hGcont.tendsto.comp (hzin.pow m)
  have heq : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      (F (z r)) ^ m = oddStarSeed t ((z r) ^ m) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    have hzext : z r ∈ exteriorDisk := by
      change 1 < ‖Complex.polarCoord.symm (r⁻¹, θ)‖
      rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.mpr hr.1)]
      exact (one_lt_inv₀ hr.1).2 hr.2
    exact oddStarPerturbation_pow_eq_seed m (by omega) t ht (z r) hzext
  have hFpow : Tendsto (fun r => (F (z r)) ^ m)
      (𝓝[<] (1 : ℝ))
      (𝓝 ((actualExteriorRadialTrace F θ) ^ m)) :=
    htrace.pow m
  have hseed' := hseed.congr' (heq.mono fun r hr => hr.symm)
  exact tendsto_nhds_unique hFpow hseed'

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_actual_radialTrace_pow
