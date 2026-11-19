import SpringerLean.Round1869SlitRadialTrace
import SpringerLean.Round1860ActualRealMomentLimit

open MeasureTheory Filter Set
open scoped Topology

namespace SpringerLean

theorem actualBoundaryRadialMoment_congr
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hG : CenteredExteriorUnivalent G)
    (hEq : Set.EqOn F G exteriorDisk) (p : ℝ) (hp : 0 ≤ p) :
    actualBoundaryRadialMoment F p = actualBoundaryRadialMoment G p := by
  apply tendsto_nhds_unique (actualBoundaryRadialMoment_circle_tendsto F hF p hp)
  apply (actualBoundaryRadialMoment_circle_tendsto G hG p hp).congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hn : ‖z‖ = r⁻¹ := by
    simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos (inv_pos.2 hr.1)] using hz
  have hzin : z ∈ exteriorDisk := by
    change 1 < ‖z‖
    rw [hn]
    exact (one_lt_inv₀ hr.1).2 hr.2
  change ‖G z‖ ^ p = ‖F z‖ ^ p
  rw [hEq hzin]

theorem slitMap_square_scaled (b z : ℂ) (hb : b ≠ 0) :
    slitMap (b ^ 2) (b * z) = b * slitMap 1 z := by
  by_cases hz : z = 0
  · simp [slitMap, hz]
  · simp only [slitMap]
    field_simp
    <;> ring

theorem slitMap_circle_moment_phase (α R p : ℝ) :
    Real.circleAverage
        (fun z : ℂ => ‖slitMap (Complex.exp (((2 * α : ℝ) : ℂ) * Complex.I)) z‖ ^ p) 0 R =
      Real.circleAverage (fun z : ℂ => ‖slitMap 1 z‖ ^ p) 0 R := by
  let b := Complex.exp ((α : ℂ) * Complex.I)
  have hb : b ≠ 0 := Complex.exp_ne_zero _
  have hbnorm : ‖b‖ = 1 := by simp [b, Complex.norm_exp]
  have hsq : Complex.exp (((2 * α : ℝ) : ℂ) * Complex.I) = b ^ 2 := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [Real.circleAverage_eq_integral_add α, Real.circleAverage_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have hcircle : circleMap 0 R (θ + α) = b * circleMap 0 R θ := by
    simp only [circleMap_zero, Complex.ofReal_add, add_mul, Complex.exp_add, b]
    ring
  change ‖slitMap (Complex.exp (((2 * α : ℝ) : ℂ) * Complex.I))
    (circleMap 0 R (θ + α))‖ ^ p = ‖slitMap 1 (circleMap 0 R θ)‖ ^ p
  rw [hcircle, hsq, slitMap_square_scaled _ _ hb, norm_mul, hbnorm, one_mul]

theorem actualBoundaryRadialMoment_slitMap
    (a : ℂ) (ha : ‖a‖ = 1) (p : ℝ) (hp : 0 < p) :
    actualBoundaryRadialMoment (slitMap a) p = slitRadialMomentConstant p := by
  let α := Complex.arg a / 2
  have heq : a = Complex.exp (((2 * α : ℝ) : ℂ) * Complex.I) := by
    have hh := Complex.norm_mul_exp_arg_mul_I a
    rw [ha, Complex.ofReal_one, one_mul] at hh
    have he : 2 * α = Complex.arg a := by dsimp [α]; ring
    rw [he]
    exact hh.symm
  have hcircle (r : ℝ) : Real.circleAverage (fun z : ℂ => ‖slitMap a z‖ ^ p) 0 r⁻¹ =
      Real.circleAverage (fun z : ℂ => ‖slitMap 1 z‖ ^ p) 0 r⁻¹ := by
    rw [heq]
    exact slitMap_circle_moment_phase α r⁻¹ p
  have hA := actualBoundaryRadialMoment_circle_tendsto (slitMap a)
    (slitMap_centeredExteriorUnivalent a ha) p hp.le
  have h1 := actualBoundaryRadialMoment_circle_tendsto (slitMap 1)
    (slitMap_centeredExteriorUnivalent 1 (by norm_num)) p hp.le
  have hmoment : actualBoundaryRadialMoment (slitMap a) p =
      actualBoundaryRadialMoment (slitMap 1) p :=
    tendsto_nhds_unique hA (h1.congr' (Eventually.of_forall (fun r => (hcircle r).symm)))
  rw [hmoment]
  exact actualBoundaryRadialMoment_slitMap_one p hp

theorem actualBoundaryRadialMoment_eq_of_eqOn_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (a : ℂ) (ha : ‖a‖ = 1) (hEq : Set.EqOn F (slitMap a) exteriorDisk)
    (p : ℝ) (hp : 0 < p) :
    actualBoundaryRadialMoment F p = slitRadialMomentConstant p := by
  rw [actualBoundaryRadialMoment_congr F (slitMap a) hc
    (slitMap_centeredExteriorUnivalent a ha) hEq p hp.le]
  exact actualBoundaryRadialMoment_slitMap a ha p hp

end SpringerLean

#print axioms SpringerLean.actualBoundaryRadialMoment_slitMap
#print axioms SpringerLean.actualBoundaryRadialMoment_eq_of_eqOn_slit
