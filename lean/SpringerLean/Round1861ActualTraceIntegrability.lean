import SpringerLean.Round1860ActualRealMomentLimit
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter Set
open scoped Topology

namespace SpringerLean

theorem actualExteriorRadialTrace_ae_norm_le_two
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      ‖actualExteriorRadialTrace F θ‖ ≤ 2 := by
  filter_upwards [actualExteriorRadialTrace_ae_tendsto F hc] with θ hθ
  have hrhs : Tendsto (fun r : ℝ => r + r⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 (2 : ℝ)) := by
    have hi : Tendsto (fun r : ℝ => r) (𝓝[<] (1 : ℝ)) (𝓝 1) := nhdsWithin_le_nhds
    simpa only [inv_one, one_add_one_eq_two] using
      hi.add (hi.inv₀ (by norm_num : (1 : ℝ) ≠ 0))
  apply le_of_tendsto_of_tendsto hθ.norm hrhs
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  exact exterior_polar_norm_le_radius_add_inv F hc hr.1 hr.2 θ

theorem actualExteriorRadialTrace_aestronglyMeasurable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    AEStronglyMeasurable (actualExteriorRadialTrace F)
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hr (n : ℕ) : 0 < r n ∧ r n < 1 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hsmall : 1 / ((n : ℝ) + 2) < 1 := by
      apply (div_lt_one (by positivity)).2
      linarith
    dsimp only [r]
    constructor <;> linarith
  have hi : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hh := hbase.comp (tendsto_add_atTop_nat 2)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using hh
  have hseq : Tendsto r atTop (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hi
    · exact Eventually.of_forall (fun n => (hr n).2)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun θ : ℝ => F (Complex.polarCoord.symm ((r n)⁻¹, θ)))
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    have hp : Continuous (fun θ : ℝ => Complex.polarCoord.symm ((r n)⁻¹, θ)) := by
      simp_rw [Complex.polarCoord_symm_apply]
      fun_prop
    apply (hc.1.continuousOn.comp_continuous hp _).aestronglyMeasurable
    intro θ
    change 1 < ‖Complex.polarCoord.symm ((r n)⁻¹, θ)‖
    rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.2 (hr n).1)]
    exact (one_lt_inv₀ (hr n).1).2 (hr n).2
  apply aestronglyMeasurable_of_tendsto_ae atTop hmeas
  filter_upwards [actualExteriorRadialTrace_ae_tendsto F hc] with θ hθ
  exact hθ.comp hseq

theorem actualBoundaryRadialMoment_integrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (p : ℝ) (hp : 0 ≤ p) :
    IntegrableOn (fun θ : ℝ => ‖actualExteriorRadialTrace F θ‖ ^ p)
      (Ioo (-Real.pi) Real.pi) := by
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo]
    finiteness)
  have hmeas := (Real.continuous_rpow_const hp).comp_aestronglyMeasurable
    (actualExteriorRadialTrace_aestronglyMeasurable F hc).norm
  apply (integrable_const ((2 : ℝ) ^ p)).mono' hmeas
  filter_upwards [actualExteriorRadialTrace_ae_norm_le_two F hc] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow (norm_nonneg _) hθ hp

end SpringerLean

#print axioms SpringerLean.actualExteriorRadialTrace_ae_norm_le_two
#print axioms SpringerLean.actualExteriorRadialTrace_aestronglyMeasurable
#print axioms SpringerLean.actualBoundaryRadialMoment_integrable
