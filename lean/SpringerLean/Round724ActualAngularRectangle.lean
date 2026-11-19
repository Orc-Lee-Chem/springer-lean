import SpringerLean.Round719ActualAngularMajorant
import SpringerLean.Round722ActualTopRightTrace
import SpringerLean.Round723ComplexRectangle
import SpringerLean.Round706AngularTopEndpointBounds

open MeasureTheory Set

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- All FOUR edge errors are discharged for the SAME actual regularized
map.  This finite rectangle comparison is not yet its zero-error limit. -/
theorem regularExterior_logarithmicTop_le_majorant_add_rectangle_error
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (c : ℂ), ‖c‖ = 1 →
      ∀ a b d : ℝ, a ≤ b → b < 0 → 0 < d → d < Real.pi-d →
      ∀ z ∈ complexClosedRectangle a b d (Real.pi-d),
        logarithmicActualTopValue (rescaleExterior s F) c z ≤ angularSineMajorant c z+
          (4*Real.pi*Real.exp a+4*d+(1-Real.exp b)*(4+2*Real.pi*L)) := by
  obtain ⟨L, hL0, hright⟩ := regularExterior_actualAngularTopValue_le_sine_add_radial_error
    F hc hs0 hs1
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  refine ⟨L, hL0, ?_⟩
  intro c hcn a b d hab hb hd hdp
  let K := complexClosedRectangle a b d (Real.pi-d)
  let M : ℝ := 4*Real.pi*Real.exp a+4*d+(1-Real.exp b)*(4+2*Real.pi*L)
  have hKsub : K ⊆ {z : ℂ | z.re < 0 ∧ 0 < z.im ∧ z.im < Real.pi} := by
    intro z hz
    exact ⟨hz.1.2.trans_lt hb, hd.trans_le hz.2.1, by linarith [hz.2.2]⟩
  have heb : Real.exp b < 1 := Real.exp_lt_one_iff.mpr hb
  have hparts : 0 ≤ 4*Real.pi*Real.exp a ∧ 0 ≤ 4*d ∧
      0 ≤ (1-Real.exp b)*(4+2*Real.pi*L) := by
    constructor
    · positivity
    · exact ⟨by positivity, mul_nonneg (by linarith) (by positivity)⟩
  have hMleft : 4*Real.pi*Real.exp a ≤ M := by dsimp [M]; linarith [hparts.2.1, hparts.2.2]
  have hMhor : 4*d ≤ M := by dsimp [M]; linarith [hparts.1, hparts.2.2]
  have hMright : (1-Real.exp b)*(4+2*Real.pi*L) ≤ M := by
    dsimp [M]; linarith [hparts.1, hparts.2.1]
  apply logarithmicActualTopValue_le_majorant_on_compact (rescaleExterior s F) hcG c K
    (complexClosedRectangle_isCompact a b d (Real.pi-d)) hKsub M
  intro z hz
  obtain ⟨hzK, he⟩ := complexClosedRectangle_frontier_edges hz
  have hzS := hKsub hzK
  have her : Real.exp z.re < 1 := Real.exp_lt_one_iff.mpr hzS.1
  have hsine : 0 ≤ Real.sin z.im := Real.sin_nonneg_of_mem_Icc ⟨hzS.2.1.le, hzS.2.2.le⟩
  have hmodel : 0 ≤ angularSineMajorant c z := by
    rw [angularSineMajorant_coordinates]
    positivity
  have hcoarse : logarithmicActualTopValue (rescaleExterior s F) c z ≤
      4*Real.exp z.re*z.im := by
    have hv := (le_abs_self (actualAngularTopValue (rescaleExterior s F) c
      (Real.exp z.re) z.im)).trans (actualAngularTopValue_abs_le
        (rescaleExterior s F) hcG c (Real.exp_pos _).le her hzS.2.1 hzS.2.2)
    simpa only [logarithmicActualTopValue, hcn, mul_one] using hv
  rcases he with hleft | hrightEdge | hlower | hupper
  · have hv : logarithmicActualTopValue (rescaleExterior s F) c z ≤
        4*Real.pi*Real.exp a := by
      rw [hleft] at hcoarse
      have hh := mul_le_mul_of_nonneg_left hzS.2.2.le
        (by positivity : 0 ≤ 4*Real.exp a)
      nlinarith
    linarith
  · have hv := hright c hcn (Real.exp z.re) (Real.exp_pos _).le her
      z.im hzS.2.1 hzS.2.2
    have hm : angularSineMajorant c z = 4*Real.exp b*Real.sin z.im := by
      rw [angularSineMajorant_coordinates, hcn, hrightEdge]
      ring
    change logarithmicActualTopValue (rescaleExterior s F) c z ≤
      4*Real.sin z.im+2*z.im*L*(1-Real.exp z.re) at hv
    rw [hrightEdge] at hv
    have hw : 4*Real.sin z.im+2*z.im*L ≤ 4+2*Real.pi*L := by
      have hb1 := Real.sin_le_one z.im
      have hb2 := mul_le_mul_of_nonneg_right hzS.2.2.le (by positivity : 0 ≤ 2*L)
      nlinarith
    have hscale := mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ 1-Real.exp b)
    rw [hm]
    nlinarith
  · rw [hlower] at hcoarse
    have hv : logarithmicActualTopValue (rescaleExterior s F) c z ≤ 4*d := by
      have hh := mul_le_mul_of_nonneg_right her.le (by positivity : 0 ≤ 4*d)
      nlinarith
    linarith
  · have hv := actualAngularTopValue_le_complement_mass
      (rescaleExterior s F) hcG c (Real.exp_pos z.re).le her hzS.2.1 hzS.2.2
    change logarithmicActualTopValue (rescaleExterior s F) c z ≤
      4*‖c‖*Real.exp z.re*(Real.pi-z.im) at hv
    rw [hcn, hupper] at hv
    have hh := mul_le_mul_of_nonneg_right her.le (by positivity : 0 ≤ 4*d)
    nlinarith

end SpringerLean

#print axioms SpringerLean.regularExterior_logarithmicTop_le_majorant_add_rectangle_error
