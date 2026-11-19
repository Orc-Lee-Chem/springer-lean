import SpringerLean.Round2047PolynomialExteriorLogPotential
import SpringerLean.Round2048AngularLogKernel

open Metric Set Real Polynomial Filter

namespace SpringerLean

private theorem exterior_circle_scaled_log_potential
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (x : ℂ) (r s : ℝ) (hr : 1 < r) (hs : 0 < s) :
    circleAverage (fun z => Real.log ‖F z / (s : ℂ) - x‖) 0 r =
      circleAverage (fun z => Real.log ‖F z - (s : ℂ) * x‖) 0 r - Real.log s := by
  classical
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsphere : sphere (0 : ℂ) |r| ⊆ exteriorDisk := by
    intro z hz
    change 1 < ‖z‖
    have hnorm : ‖z‖ = r := by
      simpa only [mem_sphere, dist_zero_right, abs_of_pos hr0] using hz
    rwa [hnorm]
  have hA : AnalyticOnNhd ℂ (fun z => F z - (s : ℂ) * x) (sphere 0 |r|) := by
    intro z hz
    exact (hF.1.analyticAt (exteriorDisk_isOpen.mem_nhds (hsphere hz))).sub analyticAt_const
  rw [← circleAverage_const (Real.log s) 0 r,
    ← circleAverage_fun_sub hA.meromorphicOn.circleIntegrable_log_norm
      (circleIntegrable_const _ _ _)]
  let y : ℂ := (s : ℂ) * x
  let excluded := if y ∈ F '' exteriorDisk then exteriorInverse F y else 0
  apply circleAverage_congr_codiscreteWithin _ hr0.ne'
  filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |r|),
    compl_singleton_mem_codiscreteWithin excluded] with z hz hne
  have hzero : F z - (s : ℂ) * x ≠ 0 := by
    intro heq
    have hzy : F z = y := sub_eq_zero.mp heq
    have hy : y ∈ F '' exteriorDisk := ⟨z, hsphere hz, hzy⟩
    have heq' := hF.2.1 (hsphere hz) (Function.invFunOn_mem hy)
      (hzy.trans (Function.invFunOn_eq hy).symm)
    apply hne
    simpa [excluded, hy, exteriorInverse] using heq'
  have hdiv : F z / (s : ℂ) - x = (F z - (s : ℂ) * x) / (s : ℂ) := by
    field_simp [hs0]
  simp only [hdiv, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  exact Real.log_div (norm_ne_zero_iff.mpr hzero) hs.ne'

private theorem circleAverage_scaled_exterior_log_swap
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (r s : ℝ) (hr : 1 < r) (hs : 0 < s) :
    circleAverage
      (fun x => circleAverage (fun z => Real.log ‖F z / (s : ℂ) - x‖) 0 r) 0 1 =
      circleAverage (fun z => Real.posLog (‖F z‖ / s)) 0 r := by
  let g : ℝ → ℂ := fun θ => F (circleMap 0 r θ) / (s : ℂ)
  have hmem (θ : ℝ) : circleMap 0 r θ ∈ exteriorDisk := by
    change 1 < ‖circleMap 0 r θ‖
    simpa [norm_circleMap_zero, abs_of_pos (lt_trans zero_lt_one hr)] using hr
  have hg : Continuous g := by
    apply Continuous.div_const
    exact hF.1.continuousOn.comp_continuous (continuous_circleMap _ _) hmem
  have h := angular_integral_circle_log_potential g hg
  calc
    _ = (2 * π)⁻¹ * ((2 * π)⁻¹ *
        (∫ α in 0..2 * π, ∫ β in 0..2 * π, Real.log ‖g β - circleMap 0 1 α‖)) := by
      simp only [circleAverage_def, smul_eq_mul, g, intervalIntegral.integral_const_mul]
    _ = (2 * π)⁻¹ * (∫ β in 0..2 * π, Real.posLog ‖g β‖) := by
      rw [h]
      simp [← mul_assoc]
    _ = _ := by
      simp only [circleAverage_def, smul_eq_mul, g, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs]

/-- The multiplicity-counted root distribution of a monic polynomial
is dominated by the actual smooth exterior-circle distribution for
every logarithmic radial hinge. -/
theorem polynomial_root_posLog_mean_le_exterior_circle
    (Q : ℂ[X]) (hQ : Q.Monic) (hdeg : 0 < Q.natDegree)
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hidentity : ∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (s : ℝ) (hs : 0 < s) :
    (Q.roots.map (fun z : ℂ => Real.posLog (‖z‖ / s))).sum /
      (Q.natDegree : ℝ) ≤
      circleAverage (fun z => Real.posLog (‖F z‖ / s)) 0 r⁻¹ := by
  let n : ℝ := Q.natDegree
  have hn : 0 < n := by dsimp [n]; exact_mod_cast hdeg
  have hrinv : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  let u : ℂ → ℝ := fun x => Real.log ‖Q.eval ((s : ℂ) * x)‖ / n - Real.log s
  let v : ℂ → ℝ := fun x =>
    Real.log (max (r⁻¹ ^ Q.natDegree) ‖Q.eval ((s : ℂ) * x)‖) / n - Real.log s
  have hv : Continuous v := by
    unfold v
    have hh : Continuous (fun x : ℂ =>
        max (r⁻¹ ^ Q.natDegree) ‖Q.eval ((s : ℂ) * x)‖) := by fun_prop
    exact (hh.log (by
      intro x
      exact (lt_of_lt_of_le (pow_pos (inv_pos.mpr hr) _) (le_max_left _ _)).ne')).div_const n |>.sub
        continuous_const
  have hi : CircleIntegrable (fun x : ℂ => Real.log ‖Q.eval ((s : ℂ) * x)‖) 0 1 := by
    have ha : AnalyticOnNhd ℂ (fun x : ℂ => Q.eval ((s : ℂ) * x)) (sphere 0 1) := by
      intro x _
      exact (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) Q _ (mem_univ _)).comp
        (by fun_prop)
    exact (show MeromorphicOn (fun x : ℂ => Q.eval ((s : ℂ) * x)) (sphere 0 |(1 : ℝ)|) from
      by simpa only [abs_one] using ha.meromorphicOn).circleIntegrable_log_norm
  have hconst : CircleIntegrable (fun _ : ℂ => Real.log s) 0 1 :=
    circleIntegrable_const _ (0 : ℂ) (1 : ℝ)
  have hu : CircleIntegrable u 0 1 := (hi.div_const n).sub hconst
  have hvformula (x : ℂ) : v x =
      circleAverage (fun z => Real.log ‖F z / (s : ℂ) - x‖) 0 r⁻¹ := by
    rw [exterior_circle_scaled_log_potential F hF x r⁻¹ s hrinv hs,
      polynomial_exterior_circle_log_potential_continuous_formula Q hdeg F hF hidentity r hr hr1]
  have huv (x : ℂ) : u x ≤ v x := by
    rw [hvformula, exterior_circle_scaled_log_potential F hF x r⁻¹ s hrinv hs,
      polynomial_exterior_circle_log_potential Q hdeg F hF hidentity r hr hr1]
    exact sub_le_sub_right (le_max_right _ _) _
  have hc := circleAverage_mono hu hv.continuousOn.circleIntegrable' (fun x _ => huv x)
  have hleft : circleAverage u 0 1 =
      (Q.roots.map (fun z : ℂ => Real.posLog (‖z‖ / s))).sum / n := by
    have hpol := monic_polynomial_circleAverage_log_norm_eq_sum Q hQ s hs
    rw [circleAverage_eq_circleAverage_zero_one] at hpol
    unfold u
    simp only [add_zero] at hpol
    rw [circleAverage_fun_sub
      (show CircleIntegrable (fun x => Real.log ‖Q.eval ((s : ℂ) * x)‖ / n) 0 1 from
        hi.div_const n) hconst,
      circleAverage_const]
    have hadd : circleAverage (fun x => Real.log ‖Q.eval ((s : ℂ) * x)‖ / n) 0 1 =
        n⁻¹ * circleAverage (fun x => Real.log ‖Q.eval ((s : ℂ) * x)‖) 0 1 := by
      simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
        (circleAverage_fun_smul (a := n⁻¹)
          (f := fun x => Real.log ‖Q.eval ((s : ℂ) * x)‖) (c := 0) (R := 1))
    rw [hadd, hpol]
    change n⁻¹ * (n * Real.log s + _) - Real.log s = _
    field_simp [hn.ne']
    ring
  have hright : circleAverage v 0 1 =
      circleAverage (fun z => Real.posLog (‖F z‖ / s)) 0 r⁻¹ := by
    exact (congrArg (fun f : ℂ → ℝ => circleAverage f 0 1) (funext hvformula)).trans
      (circleAverage_scaled_exterior_log_swap F hF r⁻¹ s hrinv hs)
  simpa only [hleft, hright] using hc

end SpringerLean
