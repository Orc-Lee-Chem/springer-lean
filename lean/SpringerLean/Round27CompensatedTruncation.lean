import SpringerLean.Round27ActualIntegratedSubmean

open MeasureTheory Set

namespace SpringerLean

/-- Exact finite-truncation algebra for the compensated vertical potential.
The two whole-line integrals of `g` and `G` are never formed separately.
Only their integrable difference is integrated on the whole line. -/
theorem compensated_integral_finite_complements
    (g G : ℝ → ℝ) (S E I : Set ℝ)
    (hS : MeasurableSet S) (hE : MeasurableSet E)
    (hI : MeasurableSet I) (hES : E ⊆ S) (hIS : I ⊆ S)
    (hd : Integrable (fun t => g t - G t))
    (hgS : IntegrableOn g S) (hGS : IntegrableOn G S) :
    (∫ t : ℝ, g t - G t) + (∫ t in I, G t) - (∫ t in E, g t) =
      (∫ t in S \ E, g t) - (∫ t in S \ I, G t) +
        (∫ t in Sᶜ, g t - G t) := by
  have hsplit := integral_add_compl hS hd
  have hsub : (∫ t in S, g t - G t) =
      (∫ t in S, g t) - (∫ t in S, G t) :=
    integral_sub hgS hGS
  have hsdiffg := setIntegral_sdiff hE hgS hES
  have hsdiffG := setIntegral_sdiff hI hGS hIS
  rw [← hsplit, hsub, hsdiffg, hsdiffG]
  ring

end SpringerLean