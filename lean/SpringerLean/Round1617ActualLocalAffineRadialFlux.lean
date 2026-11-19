import SpringerLean.Round1616LocalAffineMultiplier

open Filter
open scoped Topology

namespace SpringerLean

/-- Actual radial flux for a multiplier locally equal to a chosen affine
cell. The endpoint certificate supplies that cell's slope separately. -/
theorem actualHarmonic_phaseFluxR_of_local_affine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) (f : ℝ → ℝ)
    (v slope : ℝ)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hloc : f =ᶠ[𝓝 (actualHarmonicMultiplierTime F k z)]
      fun s => v+slope*(s-actualHarmonicMultiplierTime F k z)) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let t := actualHarmonicMultiplierTime F k
    let phi : ℂ → ℝ := fun w => f (t w)
    let u := U z/y z
    let yr := (fderiv ℝ y z) (z/‖z‖)
    let Ur := (fderiv ℝ U z) (z/‖z‖)
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.re)/‖w‖) z) (1:ℂ) +
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.im)/‖w‖) z) Complex.I =
      ((y z/‖z‖)*phi z - (phi z+t z*slope)*yr -
        (k:ℝ)*slope)*u^2 + 2*phi z*u*Ur := by
  obtain ⟨hf, hderiv⟩ := deriv_of_eventually_affine f
    (actualHarmonicMultiplierTime F k z) v slope hloc
  have h := actualHarmonic_phaseFluxR_of_outer_multiplier
    F hc k beta f hz hz0 hH hf
  dsimp only at h ⊢
  rw [hderiv] at h
  exact h

end SpringerLean

#print axioms SpringerLean.actualHarmonic_phaseFluxR_of_local_affine
