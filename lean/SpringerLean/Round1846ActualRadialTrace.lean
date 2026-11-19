import SpringerLean.Round1844RadialPrimitiveLimit
import SpringerLean.Round1845PolarRadialIntegrability
import Mathlib.Analysis.Complex.RealDeriv

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- A canonical representative of the actual correction's conjugate-angle
radial trace.  The integral also defines it on the exceptional null set. -/
noncomputable def exteriorForwardConjugateRadialTrace
    (F : ℂ → ℂ) (θ : ℝ) : ℂ :=
  exteriorForwardGerm F (conj (Complex.polarCoord.symm (1 / 2, θ))) +
    ∫ r in (1 / 2 : ℝ)..1,
      deriv (exteriorForwardGerm F) (conj (Complex.polarCoord.symm (r, θ))) *
        conj (Complex.polarCoord.symm (1, θ))

/-- Full radial convergence for the original forward germ.  In
particular, no extraction of a radius subsequence is used. -/
theorem exteriorForwardGerm_ae_conjugate_radial_limit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      Tendsto
        (fun r : ℝ => exteriorForwardGerm F
          (conj (Complex.polarCoord.symm (r, θ))))
        (𝓝[<] (1 : ℝ)) (𝓝 (exteriorForwardConjugateRadialTrace F θ)) := by
  filter_upwards [exteriorForwardGerm_deriv_ae_radial_integrable F hc] with θ hθ
  let ζ := conj (Complex.polarCoord.symm (1, θ))
  have hlinear (r : ℝ) :
      conj (Complex.polarCoord.symm (r, θ)) = (r : ℂ) * ζ := by
    simp [ζ, Complex.polarCoord_symm_apply, map_mul]
  apply tendsto_left_endpoint_of_integrable_deriv (by norm_num : (1 / 2 : ℝ) < 1)
  · intro r hr
    have hz : conj (Complex.polarCoord.symm (r, θ)) ∈ Metric.ball (0 : ℂ) 1 := by
      have hr0 : 0 < r := by linarith [hr.1]
      simpa only [Metric.mem_ball, dist_zero_right, ← Complex.star_def,
        norm_star, Complex.norm_polarCoord_symm, abs_of_pos hr0] using hr.2
    have hg := (exteriorForwardGerm_analyticOnNhd_unitBall F hc _ hz).differentiableAt
    rw [hlinear] at hg
    have hd := hg.hasDerivAt.comp (r : ℂ)
      ((hasDerivAt_id (r : ℂ)).mul_const ζ)
    simpa only [Function.comp_def, id_eq, hlinear, Complex.ofReal_one, one_mul]
      using hd.comp_ofReal
  · exact hθ.mul_const ζ

end SpringerLean

#print axioms SpringerLean.exteriorForwardGerm_ae_conjugate_radial_limit
