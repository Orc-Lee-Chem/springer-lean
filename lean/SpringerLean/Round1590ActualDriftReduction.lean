import SpringerLean.Round1589PhaseDriftAlgebra

namespace SpringerLean
open scoped ComplexConjugate
noncomputable section

/-- Cartesian Laplacian of the actual phase field. This definition uses
second real Frechet derivatives and has no division by the filling. -/
def actualHarmonicPhaseLaplacian
    (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ) : ℝ :=
  let U := actualHarmonicPhaseField F k beta
  (fderiv ℝ (fun w => (fderiv ℝ U w) (1:ℂ)) z) (1:ℂ) +
  (fderiv ℝ (fun w => (fderiv ℝ U w) Complex.I) z) Complex.I

private theorem im_mul_I (w : ℂ) : (w*Complex.I).im = w.re := by
  simp [Complex.mul_im]

/-- Once the actual Laplacian is identified, the no-division drift PDE
follows from the first-derivative theorem and polynomial algebra. The
Laplacian identification is an explicit premise here, not an axiom. -/
theorem actualHarmonicPhase_drift_of_laplacian_formula
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (hlap : actualHarmonicPhaseLaplacian F k beta z =
      4*(k:ℝ)*((k:ℝ)-1)*
        (beta*(actualHarmonic F z)^(k-2)*
          deriv (exteriorForwardGerm F) (conj z)).im) :
    Complex.normSq (actualHarmonic F z) *
        actualHarmonicPhaseLaplacian F k beta z +
      4*(k:ℝ)*((k:ℝ)-1)*actualHarmonicPhaseField F k beta z =
    4*((k:ℝ)-1) *
      ((actualHarmonic F z).re *
        (fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1:ℂ) +
       (actualHarmonic F z).im *
        (fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I) := by
  let H := actualHarmonic F z
  let c := deriv (exteriorForwardGerm F) (conj z)
  obtain ⟨hx,hy⟩ :=
    actualHarmonicPhaseField_gradient_coordinates F hc k beta hz
  have hphase : actualHarmonicPhaseField F k beta z = (beta*H^k).im := rfl
  have hx' : (fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1:ℂ) =
      (k:ℝ)*(beta*H^(k-1)*(1+c)).im := by
    rw [hx]
    simp [H, c, mul_assoc, Complex.mul_im]
  have hy' : (fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I =
      (k:ℝ)*(beta*H^(k-1)*(Complex.I*(1-c))).im := by
    rw [hy]
    have hi : (beta*H^(k-1)*(Complex.I*(1-c))).im =
        (beta*H^(k-1)*(1-c)).re := by
      rw [show beta*H^(k-1)*(Complex.I*(1-c)) =
        (beta*H^(k-1)*(1-c))*Complex.I by ring]
      exact im_mul_I _
    rw [hi]
    simp [H, c, mul_assoc, Complex.mul_re]
  rw [hlap, hphase, hx', hy']
  exact phase_drift_power_algebra k hk H beta c

end
end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_drift_of_laplacian_formula
