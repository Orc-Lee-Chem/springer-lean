import SpringerLean.Round607MidpointPositiveArea
import SpringerLean.Round609InversionArea
import SpringerLean.Round12Compact
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace SpringerLean
set_option Elab.async false

theorem unitDisk_integral_conj (f : ℂ → ℝ) :
    (∫ z in Metric.ball (0 : ℂ) 1, f (conj z)) =
      ∫ z in Metric.ball (0 : ℂ) 1, f z := by
  let e : ℂ ≃ₗᵢ[ℝ] ℂ := RCLike.conjLIE
  have hpre : e ⁻¹' Metric.ball (0 : ℂ) 1 = Metric.ball (0 : ℂ) 1 := by
    ext z
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, e.norm_map]
  have he := e.measurePreserving.setIntegral_preimage_emb
    e.toMeasurableEquiv.measurableEmbedding f (Metric.ball (0 : ℂ) 1)
  rw [hpre] at he
  simpa only [e, RCLike.conjLIE_apply] using he

theorem unitDisk_integrable_conj_iff (f : ℂ → ℝ) :
    IntegrableOn (fun z : ℂ => f (conj z)) (Metric.ball (0 : ℂ) 1) ↔
      IntegrableOn f (Metric.ball (0 : ℂ) 1) := by
  let e : ℂ ≃ₗᵢ[ℝ] ℂ := RCLike.conjLIE
  have hpre : e ⁻¹' Metric.ball (0 : ℂ) 1 = Metric.ball (0 : ℂ) 1 := by
    ext z
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, e.norm_map]
  have he := e.measurePreserving.integrableOn_comp_preimage
    e.toMeasurableEquiv.measurableEmbedding (f := f) (s := Metric.ball (0 : ℂ) 1)
  rw [hpre] at he
  simpa only [e, Function.comp_def, RCLike.conjLIE_apply] using he

private theorem inv_mem_exterior_of_mem_disk {u : ℂ}
    (hu : u ∈ Metric.ball (0 : ℂ) 1) (hu0 : u ≠ 0) : u⁻¹ ∈ exteriorDisk := by
  have hu1 : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  change 1 < ‖u⁻¹‖
  rw [norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr hu1

private theorem inv_mem_disk_of_mem_exterior {z : ℂ} (hz : z ∈ exteriorDisk) :
    z⁻¹ ∈ Metric.ball (0 : ℂ) 1 := by
  have hz1 : 1 < ‖z‖ := hz
  have hn := one_div_lt_one_div_of_lt zero_lt_one hz1
  simpa only [Metric.mem_ball, dist_zero_right, norm_inv, one_div, inv_one] using hn

theorem exteriorReciprocalGerm_injOn_unitBall
    (V : ℂ → ℂ) (hV : CenteredExteriorUnivalent V)
    (hnz : ∀ z ∈ exteriorDisk, V z ≠ 0) :
    Set.InjOn (exteriorReciprocalGerm V) (Metric.ball (0 : ℂ) 1) := by
  intro u hu v hv he
  by_cases hu0 : u = 0
  · subst u
    by_contra hne
    have hv0 : v ≠ 0 := Ne.symm hne
    have hve := inv_mem_exterior_of_mem_disk hv hv0
    rw [exteriorReciprocalGerm_eq_inv V hv0 (hnz v⁻¹ hve)] at he
    have h0 : (V v⁻¹)⁻¹ = 0 := by simpa [exteriorReciprocalGerm] using he.symm
    exact inv_ne_zero (hnz v⁻¹ hve) h0
  by_cases hv0 : v = 0
  · subst v
    have hue := inv_mem_exterior_of_mem_disk hu hu0
    rw [exteriorReciprocalGerm_eq_inv V hu0 (hnz u⁻¹ hue)] at he
    have h0 : (V u⁻¹)⁻¹ = 0 := by simpa [exteriorReciprocalGerm] using he
    exact False.elim (inv_ne_zero (hnz u⁻¹ hue) h0)
  have hue := inv_mem_exterior_of_mem_disk hu hu0
  have hve := inv_mem_exterior_of_mem_disk hv hv0
  rw [exteriorReciprocalGerm_eq_inv V hu0 (hnz u⁻¹ hue),
    exteriorReciprocalGerm_eq_inv V hv0 (hnz v⁻¹ hve)] at he
  exact inv_injective (hV.2.1 hue hve (inv_injective he))

theorem exteriorReciprocalGerm_unitBall_image
    (V : ℂ → ℂ) (hnz : ∀ z ∈ exteriorDisk, V z ≠ 0) :
    exteriorReciprocalGerm V '' Metric.ball (0 : ℂ) 1 =
      insert 0 ((fun w : ℂ => w⁻¹) '' (V '' exteriorDisk)) := by
  ext w
  constructor
  · rintro ⟨u,hu,rfl⟩
    by_cases hu0 : u = 0
    · simp [hu0, exteriorReciprocalGerm]
    have hue := inv_mem_exterior_of_mem_disk hu hu0
    apply Set.mem_insert_of_mem
    exact ⟨V u⁻¹, ⟨u⁻¹,hue,rfl⟩,
      (exteriorReciprocalGerm_eq_inv V hu0 (hnz u⁻¹ hue)).symm⟩
  · rintro (hw | hw)
    · subst w
      exact ⟨0,by simp,by simp [exteriorReciprocalGerm]⟩
    · obtain ⟨v,⟨z,hz,hVz⟩,hvw⟩ := hw
      refine ⟨z⁻¹, inv_mem_disk_of_mem_exterior hz, ?_⟩
      rw [exteriorReciprocalGerm_eq_inv V (inv_ne_zero (exterior_ne_zero hz))
        (by simpa only [inv_inv] using hnz z hz), inv_inv, hVz]
      exact hvw

theorem exteriorReciprocalGerm_lintegral_eq_inverse_image
    (V : ℂ → ℂ) (hV : CenteredExteriorUnivalent V)
    (hnz : ∀ z ∈ exteriorDisk, V z ≠ 0) :
    (∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (‖deriv (exteriorReciprocalGerm V) z‖ ^ 2)) =
      ∫⁻ w in V '' exteriorDisk, ENNReal.ofReal (‖w‖⁻¹ ^ 4) := by
  have hRa := exteriorReciprocalGerm_analyticOnNhd_unitBall V hV hnz
  have he := complex_injective_image_volume_eq_deriv_lintegral
    (exteriorReciprocalGerm V) (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball.measurableSet
    (fun z hz => (hRa z hz).differentiableAt) (exteriorReciprocalGerm_injOn_unitBall V hV hnz)
  have hS : MeasurableSet (V '' exteriorDisk) := by
    have hc := (exteriorOmitted_isCompact V hV).isClosed.measurableSet.compl
    simpa only [exteriorOmitted, compl_compl] using hc
  have hzero : (0 : ℂ) ∉ V '' exteriorDisk := by
    rintro ⟨z,hz,he⟩
    exact hnz z hz he
  rw [he, exteriorReciprocalGerm_unitBall_image V hnz]
  have hm : volume (insert 0 ((fun w : ℂ => w⁻¹) '' (V '' exteriorDisk))) =
      volume ((fun w : ℂ => w⁻¹) '' (V '' exteriorDisk)) := by
    apply measure_congr
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    simp [hz]
  rw [hm]
  exact (inversion_image_volume_eq_lintegral _ hS hzero).symm

end SpringerLean
