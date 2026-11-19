import SpringerLean.Round32VerticalMoments
import SpringerLean.Round28AuxClosed

open MeasureTheory Set Metric

namespace SpringerLean

/-- The actual auxiliary remains circle integrable on every small circle
strictly inside the upper half-plane. -/
theorem regularVerticalAuxiliary_circleIntegrable_positive
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρh : ρ < h) :
    CircleIntegrable
      (fun z : ℂ => regularVerticalAuxiliary F s ξ z.re z.im)
      ((a : ℂ) + (h : ℂ) * Complex.I) ρ := by
  let c : ℂ := (a : ℂ) + (h : ℂ) * Complex.I
  have hSphere (z : ℂ) (hz : z ∈ sphere c ρ) : 0 ≤ z.im := by
    have hrad : ‖z - c‖ = ρ := by
      simpa only [mem_sphere, dist_eq_norm, abs_of_nonneg hρ] using hz
    have him := Complex.abs_im_le_norm (z - c)
    have hzIm : (z - c).im = z.im - h := by simp [c]
    rw [hzIm, hrad] at him
    have hlow := (abs_le.mp him).1
    linarith
  have hcont : ContinuousOn
      (fun z : ℂ => regularVerticalAuxiliary F s ξ z.re z.im)
      (sphere c ρ) :=
    (regularVerticalAuxiliary_continuousOn_upperHalfPlane
      F hc hs0 hs1 ξ hξ).comp
        (by fun_prop : ContinuousOn (fun z : ℂ => (z.re, z.im)) (sphere c ρ))
        (fun z hz => hSphere z hz)
  exact hcont.circleIntegrable hρ

/-- A positive quadratic height perturbation makes every valid local
circle submean strict. -/
theorem regularVerticalAuxiliary_perturbed_strict_circle_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (a h ρ lam κ : ℝ) (hh : 0 < h) (hρ : 0 < ρ) (hρh : ρ < h)
    (hκ : 0 < κ)
    (hsub : regularVerticalAuxiliary F s ξ a h ≤
      Real.circleAverage
        (fun z : ℂ => regularVerticalAuxiliary F s ξ z.re z.im)
        ((a : ℂ) + (h : ℂ) * Complex.I) ρ) :
    regularVerticalAuxiliary F s ξ a h + lam * h + κ * h^2 <
      Real.circleAverage
        (fun z : ℂ =>
          regularVerticalAuxiliary F s ξ z.re z.im +
            lam * z.im + κ * z.im^2)
        ((a : ℂ) + (h : ℂ) * Complex.I) ρ := by
  let c : ℂ := (a : ℂ) + (h : ℂ) * Complex.I
  have hU := regularVerticalAuxiliary_circleIntegrable_positive
    F hc hs0 hs1 ξ hξ a h ρ hρ.le hρh
  have hlin : CircleIntegrable (fun z : ℂ => lam * z.im) c ρ :=
    ((by fun_prop : Continuous (fun z : ℂ => lam * z.im)).continuousOn).circleIntegrable hρ.le
  have hsq : CircleIntegrable (fun z : ℂ => κ * z.im^2) c ρ :=
    ((by fun_prop : Continuous (fun z : ℂ => κ * z.im^2)).continuousOn).circleIntegrable hρ.le
  have hci : CircleIntegrable
      (fun z : ℂ => regularVerticalAuxiliary F s ξ z.re z.im + lam * z.im)
      c ρ := hU.add hlin
  have hmeanlin :
      Real.circleAverage (fun z : ℂ => lam * z.im) c ρ = lam * h := by
    have hfun : (fun z : ℂ => lam * z.im) = lam • (fun z : ℂ => z.im) := by
      funext z
      rfl
    rw [hfun, Real.circleAverage_smul, circleAverage_im]
    simp [c, smul_eq_mul]
  have hmeansq :
      Real.circleAverage (fun z : ℂ => κ * z.im^2) c ρ =
        κ * (h^2 + ρ^2/2) := by
    have hfun : (fun z : ℂ => κ * z.im^2) = κ • (fun z : ℂ => z.im^2) := by
      funext z
      rfl
    rw [hfun, Real.circleAverage_smul, circleAverage_im_sq]
    simp [c, smul_eq_mul]
  have hmean :
      Real.circleAverage
        (fun z : ℂ => regularVerticalAuxiliary F s ξ z.re z.im +
          lam * z.im + κ * z.im^2) c ρ =
      Real.circleAverage
        (fun z : ℂ => regularVerticalAuxiliary F s ξ z.re z.im) c ρ +
          lam*h + κ*(h^2+ρ^2/2) := by
    rw [Real.circleAverage_fun_add hci hsq,
      Real.circleAverage_fun_add hU hlin, hmeanlin, hmeansq]
  rw [show c = (a : ℂ) + (h : ℂ) * Complex.I from rfl] at hmean
  rw [hmean]
  have hplus : 0 < κ * (ρ^2 / 2) := by positivity
  nlinarith

end SpringerLean