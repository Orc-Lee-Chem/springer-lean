import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set Filter
open scoped Topology

namespace SpringerLean

/-- The difference of exponentials divided by the positive scale. -/
noncomputable def gaussianLogKernel (a b t : ℝ) : ℝ :=
  t⁻¹ * (Real.exp (-a*t) - Real.exp (-b*t))

theorem gaussianLogKernel_nonneg {a b t : ℝ} (hab : a ≤ b) (ht : 0 < t) :
    0 ≤ gaussianLogKernel a b t := by
  apply mul_nonneg (inv_pos.mpr ht).le
  apply sub_nonneg.mpr
  exact Real.exp_le_exp.mpr (by nlinarith)

private theorem gaussianLogKernel_le {a b t : ℝ} (hab : a ≤ b) (ht : 0 < t) :
    gaussianLogKernel a b t ≤ (b-a) * Real.exp (-a*t) := by
  have hsplit : Real.exp (-b*t) = Real.exp (-a*t) * Real.exp (-(b-a)*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he : 1 - Real.exp (-(b-a)*t) ≤ (b-a)*t := by
    linarith [Real.add_one_le_exp (-(b-a)*t)]
  have hmul := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a*t)).le
  unfold gaussianLogKernel
  rw [hsplit, inv_mul_eq_div, div_le_iff₀ ht]
  nlinarith

private theorem gaussianLogKernel_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (gaussianLogKernel a b) (Ioi 0) := by
  apply Integrable.mono'
    ((integrableOn_exp_mul_Ioi (a := -a) (neg_neg_of_pos ha) 0).const_mul (b-a))
    (by unfold gaussianLogKernel; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianLogKernel_nonneg hab ht)]
  exact gaussianLogKernel_le hab ht

/-- Frullani's identity with the constant reference distance. -/
theorem integral_gaussianLogKernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in Ioi (0 : ℝ), gaussianLogKernel a b t) = Real.log (b/a) := by
  let f : ℝ → ℝ := fun t => Real.exp (-t)
  have hf : Continuous f := by unfold f; fun_prop
  have hloc : LocallyIntegrableOn f (Ioi 0) volume :=
    hf.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hL : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [f] using hf.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have h := Frullani.integral_Ioi_eq hloc ha (ha.trans_le hab) hL
    Real.tendsto_exp_neg_atTop_nhds_zero
  have heq : (fun t => t⁻¹ • (f (a*t) - f (b*t))) = gaussianLogKernel a b := by
    funext t
    simp [f, gaussianLogKernel, neg_mul, smul_eq_mul]
  rw [heq] at h
  simpa only [smul_eq_mul, sub_zero, mul_one] using h (gaussianLogKernel_integrable ha hab)

theorem lintegral_gaussianLogKernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (gaussianLogKernel a b t)) =
      ENNReal.ofReal (Real.log (b/a)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianLogKernel_integrable ha hab)
    ((ae_restrict_mem measurableSet_Ioi).mono (fun _ ht => gaussianLogKernel_nonneg hab ht)),
    integral_gaussianLogKernel ha hab]

/-- At zero squared distance the extended kernel integral is infinite. -/
theorem lintegral_gaussianLogKernel_at_diagonal {b : ℝ} (hb : 0 < b) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (gaussianLogKernel 0 b t)) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro c
  let a := b / Real.exp (c : ℝ)
  have ha : 0 < a := div_pos hb (Real.exp_pos _)
  have hab : a ≤ b :=
    div_le_self hb.le (by simpa using (Real.exp_le_exp.mpr c.coe_nonneg : Real.exp 0 ≤ _))
  have hquot : b / a = Real.exp (c : ℝ) := by
    dsimp [a]
    field_simp [hb.ne', (Real.exp_pos (c : ℝ)).ne']
  have he := lintegral_gaussianLogKernel ha hab
  rw [hquot, Real.log_exp, ENNReal.ofReal_coe_nnreal] at he
  rw [← he]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr ht).le
  apply sub_le_sub_right
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (neg_le_neg ha.le) (show 0 < t from ht).le)

end SpringerLean
