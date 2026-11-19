import SpringerLean.Round1377AngleMapIdentity
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter

namespace SpringerLean

theorem coarseAnglePhi_differentiableAt
    {v : ℝ} (hv0 : 0 ≤ v) (hvβ : v ≤ coarseAngleBeta) :
    DifferentiableAt ℝ coarseAnglePhi v := by
  have hu := coarseAngleArgument_range hv0 hvβ
  have he := coarseAngleDeficit_range hv0 hvβ
  have hs : 0 < 1 + 5 * coarseAngleDeficit v := by linarith
  have harg : DifferentiableAt ℝ coarseAngleArgument v := by
    unfold coarseAngleArgument coarseAngleDeficit
    fun_prop (disch := positivity)
  unfold coarseAnglePhi
  exact ((Real.differentiableAt_arcsin.2
    ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp v harg).const_mul 2

theorem coarseAnglePhi_deriv_identity
    {v : ℝ} (hv0 : 0 < v) (hvβ : v < coarseAngleBeta) :
    Real.sin (coarseAnglePhi v) * deriv coarseAnglePhi v =
      (1 + 10 * coarseAngleDeficit v) * Real.sin v := by
  have hdiff := coarseAnglePhi_differentiableAt (le_of_lt hv0) (le_of_lt hvβ)
  have hlocal : ∀ᶠ w in nhds v,
      2 - 2 * Real.cos (coarseAnglePhi w) =
        coarseAngleDeficit w + 5 * coarseAngleDeficit w ^ 2 := by
    filter_upwards [Ioo_mem_nhds hv0 hvβ] with w hw
    exact coarseAnglePhi_deficit hw.1.le hw.2.le
  have hleft : HasDerivAt (fun w : ℝ => 2 - 2 * Real.cos (coarseAnglePhi w))
      (2 * Real.sin (coarseAnglePhi v) * deriv coarseAnglePhi v) v := by
    have hbase := ((Real.hasDerivAt_cos (coarseAnglePhi v)).comp v hdiff.hasDerivAt).const_mul (-2) |>.const_add 2
    convert hbase using 1
    · funext x; dsimp; ring
    · ring
  have hright : HasDerivAt (fun w : ℝ =>
      coarseAngleDeficit w + 5 * coarseAngleDeficit w ^ 2)
      (2 * Real.sin v * (1 + 10 * coarseAngleDeficit v)) v := by
    have he : HasDerivAt coarseAngleDeficit (2 * Real.sin v) v := by
      unfold coarseAngleDeficit
      convert (Real.hasDerivAt_cos v).const_mul (-2) |>.const_add 2 using 1 <;> ring
    convert he.add ((he.pow 2).const_mul 5) using 1 <;> ring
  have hEq := hleft.congr_of_eventuallyEq (by
    filter_upwards [hlocal] with w hw
    exact hw.symm)
  have hder := hEq.unique hright
  nlinarith

theorem coarseAnglePhi_deriv_bounds
    {v : ℝ} (hv0 : 0 < v) (hvβ : v < coarseAngleBeta) :
    0 ≤ deriv coarseAnglePhi v ∧
      deriv coarseAnglePhi v ≤ 1 + 10 * coarseAngleDeficit v := by
  have hφ := coarseAnglePhi_range (le_of_lt hv0) (le_of_lt hvβ)
  have hφv := coarseAnglePhi_ge_input (le_of_lt hv0) (le_of_lt hvβ)
  have hφhalf := coarseAnglePhi_le_pi_half (le_of_lt hv0) (le_of_lt hvβ)
  have hsinv : 0 < Real.sin v := Real.sin_pos_of_pos_of_lt_pi hv0 (by linarith [coarseAngleBeta_range.2, Real.pi_pos])
  have hsinφ : 0 < Real.sin (coarseAnglePhi v) := Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hv0 hφv) (by linarith [hφhalf, Real.pi_pos])
  have hsinle : Real.sin v ≤ Real.sin (coarseAnglePhi v) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hv0, Real.pi_pos]) hφhalf hφv
  have he := (coarseAngleDeficit_range (le_of_lt hv0) (le_of_lt hvβ)).1
  have hid := coarseAnglePhi_deriv_identity hv0 hvβ
  constructor
  · have : 0 ≤ Real.sin (coarseAnglePhi v) * deriv coarseAnglePhi v := by nlinarith
    exact nonneg_of_mul_nonneg_right this hsinφ
  · have hnonneg : 0 ≤ deriv coarseAnglePhi v := by
      have : 0 ≤ Real.sin (coarseAnglePhi v) * deriv coarseAnglePhi v := by nlinarith
      exact nonneg_of_mul_nonneg_right this hsinφ
    nlinarith [mul_nonneg (show 0 ≤ 1 + 10 * coarseAngleDeficit v by linarith) (sub_nonneg.mpr hsinle)]

theorem coarseAnglePhi_deriv_continuousOn :
    ContinuousOn (deriv coarseAnglePhi) (Set.Icc 0 coarseAngleBeta) := by
  intro v hv
  have hu := coarseAngleArgument_range hv.1 hv.2
  have he := coarseAngleDeficit_range hv.1 hv.2
  have hs : 0 < 1 + 5 * coarseAngleDeficit v := by linarith
  have harg : ContDiffAt ℝ 1 coarseAngleArgument v := by
    unfold coarseAngleArgument coarseAngleDeficit
    fun_prop (disch := positivity)
  have hphi : ContDiffAt ℝ 1 coarseAnglePhi v := by
    unfold coarseAnglePhi
    exact contDiffAt_const.mul ((Real.contDiffAt_arcsin (by linarith [hu.1])
      (by linarith [hu.2])).comp v harg)
  exact (hphi.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

end SpringerLean

#print axioms SpringerLean.coarseAnglePhi_deriv_bounds
