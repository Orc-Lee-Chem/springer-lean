import SpringerLean.Round636OmittedCollarUniform
import SpringerLean.Rescale

namespace SpringerLean
set_option Elab.async false

/-- The actual value on the regularized unit circle belongs to the actual
omitted set. Injectivity is used on the larger source |z| > s. -/
theorem rescaleExterior_unitCircle_mem_omitted
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    rescaleExterior s F ζ ∈ exteriorOmitted (rescaleExterior s F) := by
  rintro ⟨v,hv,hvG⟩
  have hvS : v ∈ exteriorAbove s := lt_trans hs1 hv
  have hζS : ζ ∈ exteriorAbove s := by
    change s < ‖ζ‖
    rwa [hζ]
  have hvζ : v = ζ := rescaleExterior_injOn hs0 hc.2.1 hvS hζS hvG
  change 1 < ‖v‖ at hv
  rw [hvζ,hζ] at hv
  exact (lt_irrefl _) hv

end SpringerLean
