import SpringerLean.Round691AngularTopDual

open MeasureTheory Set

namespace SpringerLean
set_option Elab.async false

/-- A one-sided mass stability estimate using a dual optimizer at h'.
No measurable choice of a family of maximizing sets is needed. -/
theorem actualAngularTopValue_sub_le_height_gap
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h h' : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hh'0 : 0 < h') (hh'pi : h' < Real.pi) :
    actualAngularTopValue F c r h-actualAngularTopValue F c r h' ≤
      4*‖c‖*r*|h-h'| := by
  obtain ⟨ell, hbound, hval⟩ :=
    actualAngularTopValue_exists_bounded_threshold F hc c hr0 hr1 hh'0 hh'pi
  have hu := actualAngularTopValue_le_threshold F hc c hr0 hr1 hh0 hhpi ell
  have hfirst : actualAngularTopValue F c r h-actualAngularTopValue F c r h' ≤
      2*(h-h')*ell := by linarith
  calc
    actualAngularTopValue F c r h-actualAngularTopValue F c r h' ≤
        2*(h-h')*ell := hfirst
    _ ≤ 2*|(h-h')*ell| := by
      nlinarith [le_abs_self ((h-h')*ell)]
    _ = (2*|h-h'|)*|ell| := by rw [abs_mul]; ring
    _ ≤ (2*|h-h'|)*(‖c‖*(2*r)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 4*‖c‖*r*|h-h'| := by ring

/-- Actual top-mass values are Lipschitz in the mass parameter on0<h<pi.
This closes the height part of continuity; joint radial continuity and
the local star-function submean still have separate proof obligations. -/
theorem actualAngularTopValue_height_lipschitz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h h' : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hh'0 : 0 < h') (hh'pi : h' < Real.pi) :
    |actualAngularTopValue F c r h-actualAngularTopValue F c r h'| ≤
      4*‖c‖*r*|h-h'| := by
  have hf := actualAngularTopValue_sub_le_height_gap F hc c hr0 hr1 hh0 hhpi hh'0 hh'pi
  have hb := actualAngularTopValue_sub_le_height_gap F hc c hr0 hr1 hh'0 hh'pi hh0 hhpi
  rw [abs_sub_comm h' h] at hb
  exact abs_le.mpr ⟨by linarith, hf⟩

end SpringerLean
