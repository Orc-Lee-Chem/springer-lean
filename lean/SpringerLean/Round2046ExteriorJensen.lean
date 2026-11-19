import SpringerLean.Round1847ActualExteriorTrace
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.OpenMapping

open Metric Set Real Filter
open scoped Topology

namespace SpringerLean

noncomputable def exteriorJensenFunction (F : ℂ → ℂ) (x u : ℂ) : ℂ :=
  1 + u * (exteriorForwardGerm F u - x)

theorem exteriorJensenFunction_analytic
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (x : ℂ) :
    AnalyticOnNhd ℂ (exteriorJensenFunction F x) (ball 0 1) := by
  intro u hu
  unfold exteriorJensenFunction
  have h := exteriorForwardGerm_analyticOnNhd_unitBall F hF u hu
  fun_prop

theorem exteriorJensenFunction_punctured (F : ℂ → ℂ) (x u : ℂ)
    (hu : u ≠ 0) :
    exteriorJensenFunction F x u = u * (F u⁻¹ - x) := by
  unfold exteriorJensenFunction
  rw [exteriorForwardGerm_punctured F hu]
  field_simp [hu]
  ring

theorem exteriorJensenFunction_simple_zero
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (x u : ℂ) (hu : u ∈ ball 0 1)
    (hz : exteriorJensenFunction F x u = 0) :
    analyticOrderAt (exteriorJensenFunction F x) u = 1 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp [exteriorJensenFunction] at hz
  have hnorm : ‖u‖ < 1 := by simpa using hu
  have hinv : u⁻¹ ∈ exteriorDisk := by
    change 1 < ‖u⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr hnorm
  have hx : F u⁻¹ - x = 0 := by
    rw [exteriorJensenFunction_punctured F x u hu0] at hz
    exact (mul_eq_zero.mp hz).resolve_left hu0
  have hD := deriv_ne_zero_of_differentiableOn_injOn
    exteriorDisk_isOpen hF.1 hF.2.1 hinv
  have hdiff := hF.1.differentiableAt (exteriorDisk_isOpen.mem_nhds hinv)
  have hinvD := (hasDerivAt_id u).inv hu0
  have hcomp := hdiff.hasDerivAt.comp u hinvD
  have hprod := (hasDerivAt_id u).mul (hcomp.sub_const x)
  have hDeriv : HasDerivAt (exteriorJensenFunction F x)
      (u * (deriv F u⁻¹ * (-(1 : ℂ) / u ^ 2))) u := by
    have heq : exteriorJensenFunction F x =ᶠ[𝓝 u]
        (id * fun v => (F ∘ Inv.inv) v - x) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds
        (show u ∈ ({0} : Set ℂ)ᶜ from hu0)] with v hv
      exact exteriorJensenFunction_punctured F x v hv
    have hprod' := hprod.congr_of_eventuallyEq heq
    simpa [Function.comp_def, hx, mul_comm, mul_left_comm, mul_assoc] using hprod'
  apply (exteriorJensenFunction_analytic F hF x u hu).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
  rw [hDeriv.deriv]
  exact mul_ne_zero hu0 (mul_ne_zero hD (div_ne_zero (by norm_num) (pow_ne_zero _ hu0)))

theorem exteriorJensenFunction_zero_iff (F : ℂ → ℂ) (x u : ℂ) :
    exteriorJensenFunction F x u = 0 ↔ u ≠ 0 ∧ F u⁻¹ = x := by
  by_cases hu : u = 0
  · simp [hu, exteriorJensenFunction]
  · rw [exteriorJensenFunction_punctured F x u hu]
    simp [mul_eq_zero, hu, sub_eq_zero]

theorem exteriorJensenFunction_circleAverage_outside
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (x : ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (w : ℂ) (hw : w ∈ exteriorDisk) (hx : F w = x) :
    circleAverage (fun u => Real.log ‖exteriorJensenFunction F x u‖) 0 r =
      Real.log (max 1 (r * ‖w‖)) := by
  have ha := exteriorJensenFunction_analytic F hF x
  have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 1 :=
    closedBall_subset_ball (by simpa [abs_of_pos hr] using hr1)
  have hJ := (ha.mono hsub).circleAverage_log_norm hr.ne'
    (by simp [exteriorJensenFunction])
  simp only [exteriorJensenFunction, zero_mul, add_zero, norm_one, Real.log_one, add_zero] at hJ
  change circleAverage (fun u => Real.log ‖exteriorJensenFunction F x u‖) 0 r = _ at hJ
  rw [hJ]
  have hdz (u : ℂ) (hne : u ≠ w⁻¹) :
      MeromorphicOn.divisor (exteriorJensenFunction F x) (closedBall 0 |r|) u = 0 := by
    by_cases hu : u ∈ closedBall (0 : ℂ) |r|
    · have hnz : exteriorJensenFunction F x u ≠ 0 := by
        intro hz
        obtain ⟨hu0, hueq⟩ := (exteriorJensenFunction_zero_iff F x u).mp hz
        have hunorm : ‖u‖ < 1 := by simpa using hsub hu
        have huinv : u⁻¹ ∈ exteriorDisk := by
          change 1 < ‖u⁻¹‖
          rw [norm_inv]
          exact (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr hunorm
        have heq : u⁻¹ = w := hF.2.1 huinv hw (hueq.trans hx.symm)
        exact hne (by simpa using congrArg Inv.inv heq)
      rw [MeromorphicOn.divisor_apply (ha.mono hsub).meromorphicOn hu,
        (ha u (hsub hu)).meromorphicOrderAt_eq,
        (ha u (hsub hu)).analyticOrderAt_eq_zero.mpr hnz]
      simp
    · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
  rw [finsum_eq_single _ w⁻¹ (fun u hu => by rw [hdz u hu]; simp)]
  have hnormw : 0 < ‖w‖ := norm_pos_iff.mpr (exterior_ne_zero hw)
  have hlog : r * ‖(0 : ℂ) - w⁻¹‖⁻¹ = r * ‖w‖ := by simp
  rw [hlog]
  by_cases hm : w⁻¹ ∈ closedBall (0 : ℂ) |r|
  · have hzero : exteriorJensenFunction F x w⁻¹ = 0 :=
      (exteriorJensenFunction_zero_iff F x w⁻¹).mpr
        ⟨inv_ne_zero (exterior_ne_zero hw), by simpa using hx⟩
    rw [MeromorphicOn.divisor_apply (ha.mono hsub).meromorphicOn hm,
      (ha w⁻¹ (hsub hm)).meromorphicOrderAt_eq,
      exteriorJensenFunction_simple_zero F hF x _ (hsub hm) hzero]
    have hrw : 1 ≤ r * ‖w‖ := by
      have h := (mem_closedBall.mp hm)
      rw [dist_zero_right, norm_inv, abs_of_pos hr] at h
      have hm' := mul_le_mul_of_nonneg_right h hnormw.le
      simpa [hnormw.ne'] using hm'
    simp [max_eq_right hrw]
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hm]
    have hrw : r * ‖w‖ ≤ 1 := by
      have h : r < ‖w‖⁻¹ := by
        simpa [mem_closedBall, dist_zero_right, norm_inv, abs_of_pos hr] using hm
      have hm' := mul_le_mul_of_nonneg_right h.le hnormw.le
      simpa [hnormw.ne'] using hm'
    simp [max_eq_left hrw]

theorem exteriorJensenFunction_circleAverage_omitted
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (x : ℂ) (hx : x ∉ F '' exteriorDisk)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    circleAverage (fun u => Real.log ‖exteriorJensenFunction F x u‖) 0 r = 0 := by
  have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 1 :=
    closedBall_subset_ball (by simpa [abs_of_pos hr] using hr1)
  have hnonzero (u : ℂ) (hu : u ∈ closedBall (0 : ℂ) |r|) :
      exteriorJensenFunction F x u ≠ 0 := by
    intro hz
    obtain ⟨hu0, hueq⟩ := (exteriorJensenFunction_zero_iff F x u).mp hz
    have hnorm : ‖u‖ < 1 := by simpa using hsub hu
    have huinv : u⁻¹ ∈ exteriorDisk := by
      change 1 < ‖u⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr hnorm
    exact hx ⟨u⁻¹, huinv, hueq⟩
  rw [AnalyticOnNhd.circleAverage_log_norm_of_ne_zero
    ((exteriorJensenFunction_analytic F hF x).mono hsub) hnonzero]
  simp [exteriorJensenFunction]

/-- Standard circle inversion with its corresponding reciprocal radius. -/
theorem circleAverage_inverse_radius (f : ℂ → ℝ) (r : ℝ) :
    circleAverage (fun z => f z⁻¹) 0 r = circleAverage f 0 r⁻¹ := by
  calc
    _ = circleAverage (fun z : ℂ => f ((r * z)⁻¹)) 0 1 := by
      simpa only [add_zero] using
        (circleAverage_eq_circleAverage_zero_one
          (f := fun z : ℂ => f z⁻¹) (c := 0) (R := r))
    _ = circleAverage (fun z : ℂ => f ((r⁻¹ : ℝ) * z)) 0 1 := by
      simpa only [mul_inv_rev, Complex.ofReal_inv, mul_comm] using
        (circleAverage_zero_one_congr_inv (f := fun z : ℂ => f ((r⁻¹ : ℝ) * z)))
    _ = _ := by
      simpa only [add_zero] using
        (circleAverage_eq_circleAverage_zero_one (f := f) (c := 0) (R := r⁻¹)).symm

/-- Jensen's reciprocal formula converted back to the actual exterior
circle. The single possible zero on that circle is excluded before
using the logarithm of a product. -/
theorem exterior_circle_log_potential_eq_jensen
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (x : ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    circleAverage (fun z => Real.log ‖F z - x‖) 0 r⁻¹ =
      circleAverage (fun u => Real.log ‖exteriorJensenFunction F x u‖) 0 r - Real.log r := by
  classical
  rw [← circleAverage_inverse_radius (fun z => Real.log ‖F z - x‖) r]
  have hsub : sphere (0 : ℂ) |r| ⊆ ball 0 1 :=
    sphere_subset_closedBall.trans
      (closedBall_subset_ball (by simpa [abs_of_pos hr] using hr1))
  have hint : CircleIntegrable
      (fun u => Real.log ‖exteriorJensenFunction F x u‖) 0 r :=
    ((exteriorJensenFunction_analytic F hF x).mono hsub).meromorphicOn.circleIntegrable_log_norm
  rw [← circleAverage_const (Real.log r) 0 r,
    ← circleAverage_fun_sub hint (circleIntegrable_const _ _ _)]
  let excluded : ℂ := if x ∈ F '' exteriorDisk then (exteriorInverse F x)⁻¹ else 0
  apply circleAverage_congr_codiscreteWithin _ hr.ne'
  filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |r|),
    compl_singleton_mem_codiscreteWithin excluded] with u hu hne
  have hnorm : ‖u‖ = r := by
    simpa [mem_sphere, dist_zero_right, abs_of_pos hr] using hu
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (hnorm.trans_ne hr.ne')
  have hinv : u⁻¹ ∈ exteriorDisk := by
    change 1 < ‖u⁻¹‖
    rw [norm_inv, hnorm]
    exact (one_lt_inv₀ hr).mpr hr1
  have hFx : F u⁻¹ - x ≠ 0 := by
    intro heq
    have himage : x ∈ F '' exteriorDisk := ⟨_, hinv, sub_eq_zero.mp heq⟩
    have hmem : exteriorInverse F x ∈ exteriorDisk := Function.invFunOn_mem himage
    have hval : F (exteriorInverse F x) = x := Function.invFunOn_eq himage
    have hmatch := hF.2.1 hinv hmem ((sub_eq_zero.mp heq).trans hval.symm)
    apply hne
    simpa [excluded, himage] using congrArg Inv.inv hmatch
  rw [exteriorJensenFunction_punctured F x u hu0, norm_mul, hnorm,
    Real.log_mul hr.ne' (norm_ne_zero_iff.mpr hFx)]
  ring

theorem exterior_circle_log_potential_of_omitted
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (x : ℂ) (hx : x ∉ F '' exteriorDisk)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    circleAverage (fun z => Real.log ‖F z - x‖) 0 r⁻¹ = -Real.log r := by
  rw [exterior_circle_log_potential_eq_jensen F hF x r hr hr1,
    exteriorJensenFunction_circleAverage_omitted F hF x hx r hr hr1, zero_sub]

theorem exterior_circle_log_potential_at_image
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (w : ℂ) (hw : w ∈ exteriorDisk)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    circleAverage (fun z => Real.log ‖F z - F w‖) 0 r⁻¹ =
      Real.log (max r⁻¹ ‖w‖) := by
  rw [exterior_circle_log_potential_eq_jensen F hF (F w) r hr hr1,
    exteriorJensenFunction_circleAverage_outside F hF (F w) r hr hr1 w hw rfl,
    ← Real.log_div (by positivity : max 1 (r * ‖w‖) ≠ 0) hr.ne']
  congr 1
  rw [div_eq_mul_inv, max_mul_of_nonneg _ _ (inv_nonneg.mpr hr.le), one_mul]
  congr 1
  field_simp [hr.ne']

end SpringerLean
