import SpringerLean.Round1513SelectedPointwiseCaps
import SpringerLean.Round550RotateExterior

open Set
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The full omitted-hull cap is invariant when both the map and the
projection direction are rotated by the same unit complex number. -/
theorem rotateExterior_projection_hull_cap
    (F : ℂ → ℂ) (ω ξ : ℂ) (hω : ‖ω‖=1) (R : ℝ)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ R) :
    ∀ w ∈ convexHull ℝ (exteriorOmitted (rotateExterior ω F)),
      (conj (ω⁻¹*ξ)*w).re ≤ R := by
  have hω0 : ω ≠ 0 := by intro he; simp [he] at hω
  let T : ℂ →ₗ[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ ω).toLinearMap
  have himage : T '' exteriorOmitted (rotateExterior ω F) = exteriorOmitted F := by
    ext q
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (rotateExterior_omitted_iff F ω hω v).mp hv
    · intro hq
      refine ⟨ω⁻¹*q,(rotateExterior_omitted_iff F ω hω _).mpr ?_,?_⟩
      · simpa [mul_assoc,hω0] using hq
      · simp [T,mul_assoc,hω0]
  intro w hw
  have htw : T w ∈ convexHull ℝ (exteriorOmitted F) := by
    rw [←himage,←T.image_convexHull]
    exact ⟨w,hw,rfl⟩
  have hp := hcap (T w) htw
  change (conj ξ*(ω*w)).re ≤ R at hp
  have heq : conj (ω⁻¹*ξ)*w = conj ξ*(ω*w) := by
    rw [map_mul,Complex.inv_eq_conj hω, Complex.conj_conj]
    ring
  rw [heq]
  exact hp

/-- At every source angle, rearrangement bounds the actual filling by
the same centered flattened profile at the corresponding radius. -/
theorem actualHarmonic_flattened_pointwise_cap_any_angle
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    (ω : ℂ) (hω : ‖ω‖=1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (conj ξ*actualHarmonic F (ω*(r:ℂ))).re ≤
      flattenedCosinePoissonAtReal h r := by
  let G := rotateExterior ω F
  have hcG : CenteredExteriorUnivalent G :=
    rotateExterior_centeredExteriorUnivalent F hc ω hω
  let η := ω⁻¹*ξ
  have hη : ‖η‖=1 := by simp [η,norm_mul,hω,hξ]
  have hcapG : ∀ w ∈ convexHull ℝ (exteriorOmitted G),
      (conj η*w).re ≤ 2*Real.sin h/h :=
    rotateExterior_projection_hull_cap F ω ξ hω _ hcap
  have hp := actualHarmonic_flattened_pointwise_cap
    G hcG η hη h hh0 hhpi hcapG hr0 hr1
  rw [rotateExterior_actualHarmonic F ω hω] at hp
  change (conj η*(ω⁻¹*actualHarmonic F (ω*(r:ℂ)))).re ≤
    flattenedCosinePoissonAtReal h r at hp
  have heq (z : ℂ) : conj η*(ω⁻¹*z) = conj ξ*z := by
    dsimp [η]
    have hconj : conj (ω⁻¹)=ω := by
      rw [Complex.inv_eq_conj hω,Complex.conj_conj]
    rw [map_mul,hconj]
    have hmul : ω*ω⁻¹ = 1 := mul_inv_cancel₀ (by intro he; simp [he] at hω)
    calc
      (ω*conj ξ)*(ω⁻¹*z) = conj ξ*((ω*ω⁻¹)*z) := by ring
      _ = conj ξ*z := by rw [hmul,one_mul]
  rw [heq] at hp
  exact hp

/-- The same peak bound is available directly at every nonzero point
of the actual inner source disk. -/
theorem actualHarmonic_flattened_peak_cap
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    (z : ℂ) (hz0 : 0 < ‖z‖) (hz1 : ‖z‖ < 1) :
    (conj ξ*actualHarmonic F z).re ≤
      flattenedCosinePoissonAtReal h ‖z‖ := by
  let ω : ℂ := z/(‖z‖:ℂ)
  have hz0' : (‖z‖:ℂ) ≠ 0 := by exact_mod_cast hz0.ne'
  have hz : z ≠ 0 := by
    intro he
    simp [he] at hz0
  have hω : ‖ω‖=1 := by
    dsimp [ω]
    simp [hz]
  have hwz : ω*(‖z‖:ℂ)=z := by
    dsimp [ω]
    exact div_mul_cancel₀ z hz0'
  simpa only [hwz] using
    actualHarmonic_flattened_pointwise_cap_any_angle
      F hc ξ hξ h hh0 hhpi hcap ω hω hz0 hz1

end SpringerLean

#print axioms SpringerLean.rotateExterior_projection_hull_cap
#print axioms SpringerLean.actualHarmonic_flattened_pointwise_cap_any_angle
#print axioms SpringerLean.actualHarmonic_flattened_peak_cap
