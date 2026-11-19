import SpringerLean.Round14JensenSimple

open Filter Metric
open scoped Topology

namespace SpringerLean

/-- Near the reciprocal of an actual exterior preimage, the regularized
potential factor is the reciprocal-coordinate exterior-map difference. -/
theorem regularBoundaryPotential_image_eventuallyEq_reciprocal
    (F : ℂ → ℂ) {s : ℝ} (hs0 : 0 < s)
    {v : ℂ} (hv : v ∈ exteriorDisk) :
    regularBoundaryPotential s F (rescaleExterior s F v) =ᶠ[𝓝 v⁻¹]
      (fun u : ℂ => u * (rescaleExterior s F u⁻¹ - rescaleExterior s F v)) := by
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    norm_num [exteriorDisk] at hv
  filter_upwards [eventually_ne_nhds (inv_ne_zero hv0)] with u hu
  exact regularBoundaryPotential_punctured F hs0 _ hu

/-- Exact derivative identity at the reciprocal preimage. The factor is
`-v`, including its sign; no derivative-nonzero hypothesis is used. -/
theorem regularBoundaryPotential_image_deriv_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : v ∈ exteriorDisk) :
    deriv (regularBoundaryPotential s F (rescaleExterior s F v)) v⁻¹ =
      -v * deriv (rescaleExterior s F) v := by
  let G := rescaleExterior s F
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    norm_num [exteriorDisk] at hv
  have hvext : v ∈ exteriorAbove s := by
    change s < ‖v‖
    exact lt_trans hs1 hv
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : HasDerivAt G (deriv G v) v :=
    (rescaleExterior_analyticAt hs0 hF hvext).differentiableAt.hasDerivAt
  have hInv : HasDerivAt (fun u : ℂ => u⁻¹) (-((v⁻¹) ^ 2)⁻¹) v⁻¹ :=
    hasDerivAt_inv (inv_ne_zero hv0)
  have hComp : HasDerivAt
      (fun u : ℂ => G u⁻¹ - G v)
      (deriv G v * (-((v⁻¹) ^ 2)⁻¹)) v⁻¹ := by
    have hG' : HasDerivAt G (deriv G v) (v⁻¹)⁻¹ := by simpa using hG
    simpa only [Function.comp_def] using (hG'.comp v⁻¹ hInv).sub_const (G v)
  have hProd : HasDerivAt
      (fun u : ℂ => u * (G u⁻¹ - G v))
      (1 * (G (v⁻¹)⁻¹ - G v) + v⁻¹ *
        (deriv G v * (-((v⁻¹) ^ 2)⁻¹))) v⁻¹ := by
    have hfEq : (id * fun u : ℂ => G u⁻¹ - G v) =
        (fun u : ℂ => u * (G u⁻¹ - G v)) := by
      funext u
      rfl
    simpa only [hfEq, id_eq] using (hasDerivAt_id v⁻¹).mul hComp
  have hEq := regularBoundaryPotential_image_eventuallyEq_reciprocal F hs0 hv
  have hDeriv :
      deriv (regularBoundaryPotential s F (G v)) v⁻¹ =
      1 * (G (v⁻¹)⁻¹ - G v) + v⁻¹ *
        (deriv G v * (-((v⁻¹) ^ 2)⁻¹)) := by
    calc
      _ = deriv (fun u : ℂ => u * (G u⁻¹ - G v)) v⁻¹ :=
        hEq.deriv_eq
      _ = _ := hProd.deriv
  rw [hDeriv]
  simp only [inv_inv, sub_self, mul_zero, zero_add]
  field_simp [hv0]
  ring

/-- The remaining simple-zero premise is exactly the noncritical-point
property of the actual rescaled exterior map. -/
theorem regularBoundaryPotential_image_deriv_ne_zero_iff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : v ∈ exteriorDisk) :
    deriv (regularBoundaryPotential s F (rescaleExterior s F v)) v⁻¹ ≠ 0 ↔
      deriv (rescaleExterior s F) v ≠ 0 := by
  rw [regularBoundaryPotential_image_deriv_eq F hc hs0 hs1 hv]
  have hv0 : v ≠ 0 := exterior_ne_zero hv
  simp [hv0]

/-- The image-value potential with only the explicit noncritical-point
premise left. This is a development lemma, not the final unconditional result. -/
theorem regularExterior_image_boundary_log_potential_of_rescale_deriv_ne_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : v ∈ exteriorDisk)
    (hder : deriv (rescaleExterior s F) v ≠ 0) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - rescaleExterior s F v‖)
      0 1 = Real.log ‖v‖ := by
  exact regularExterior_image_boundary_log_potential_of_simple_zero
    F hc hs0 hs1 hv
    ((regularBoundaryPotential_image_deriv_ne_zero_iff F hc hs0 hs1 hv).2 hder)

end SpringerLean
