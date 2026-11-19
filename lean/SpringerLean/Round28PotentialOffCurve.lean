import SpringerLean.Round27AngularTail

open MeasureTheory Set Metric
open scoped Topology

namespace SpringerLean

/-- A logarithmic circle potential of a continuous curve is continuous at
points outside that curve. This is a local dominated-convergence statement,
with the lower distance supplied by compactness of the curve. -/
theorem boundary_log_potential_continuousAt_off_curve
    (b : ℂ → ℂ) (hb : ContinuousOn b (sphere (0 : ℂ) 1))
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖b ζ‖ ≤ M)
    (z : ℂ) (hz : z ∉ b '' sphere (0 : ℂ) 1) :
    ContinuousAt
      (fun w : ℂ => Real.circleAverage
        (fun ζ : ℂ => Real.log ‖w - b ζ‖) 0 1) z := by
  let K : Set ℂ := b '' sphere (0 : ℂ) 1
  have hK : IsCompact K := (isCompact_sphere (0 : ℂ) 1).image_of_continuousOn hb
  have hopen : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hz)
  let S : Set ℂ := ball z (δ / 2)
  have hS : S ∈ 𝓝 z := by
    dsimp [S]
    exact Metric.ball_mem_nhds z (by positivity)
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc 0 (2 * Real.pi)
  have hbangle : Continuous (fun θ : ℝ => b (circleMap 0 1 θ)) := by
    exact hb.comp_continuous (continuous_circleMap 0 1)
      (fun θ => by simpa using circleMap_mem_sphere' (0 : ℂ) 1 θ)
  let B : ℝ := max |Real.log (δ / 2)|
    |Real.log (‖z‖ + M + δ + 1)|
  have hRpos : 0 < ‖z‖ + M + δ + 1 := by positivity
  have hδ2 : 0 < δ / 2 := by positivity
  have hdistz (θ : ℝ) : δ ≤ ‖z - b (circleMap 0 1 θ)‖ := by
    have hζ : b (circleMap 0 1 θ) ∈ K :=
      ⟨circleMap 0 1 θ, by simpa using circleMap_mem_sphere' (0 : ℂ) 1 θ, rfl⟩
    by_contra hn
    have hball : b (circleMap 0 1 θ) ∈ ball z δ := by
      change dist (b (circleMap 0 1 θ)) z < δ
      simpa [dist_eq_norm, norm_sub_rev] using (lt_of_not_ge hn)
    exact (hδball hball) hζ
  have hdist (x : ℂ) (hx : x ∈ S) (θ : ℝ) :
      δ / 2 ≤ ‖x - b (circleMap 0 1 θ)‖ ∧
      ‖x - b (circleMap 0 1 θ)‖ ≤ ‖z‖ + M + δ + 1 := by
    have hxz : ‖x - z‖ < δ / 2 := by
      simpa [S, mem_ball, dist_eq_norm] using hx
    have hlowtri : ‖z - b (circleMap 0 1 θ)‖ ≤
        ‖x - z‖ + ‖x - b (circleMap 0 1 θ)‖ := by
      calc
        ‖z - b (circleMap 0 1 θ)‖ =
          ‖(z - x) + (x - b (circleMap 0 1 θ))‖ := by congr 1; abel
        _ ≤ ‖z - x‖ + ‖x - b (circleMap 0 1 θ)‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev]
    have hupptri : ‖x - b (circleMap 0 1 θ)‖ ≤
        ‖x - z‖ + ‖z‖ + ‖b (circleMap 0 1 θ)‖ := by
      calc
        ‖x - b (circleMap 0 1 θ)‖ =
          ‖(x - z) + (z - b (circleMap 0 1 θ))‖ := by congr 1; abel
        _ ≤ ‖x - z‖ + ‖z - b (circleMap 0 1 θ)‖ := norm_add_le _ _
        _ ≤ ‖x - z‖ + (‖z‖ + ‖b (circleMap 0 1 θ)‖) := by
          gcongr
          exact norm_sub_le z _
        _ = _ := by ring
    have hbM : ‖b (circleMap 0 1 θ)‖ ≤ M :=
      hM _ (by simpa using circleMap_mem_sphere' (0 : ℂ) 1 θ)
    constructor <;> linarith [hdistz θ]
  have hlogbound (x : ℂ) (hx : x ∈ S) (θ : ℝ) :
      |Real.log ‖x - b (circleMap 0 1 θ)‖| ≤ B := by
    obtain ⟨hlo, hhi⟩ := hdist x hx θ
    have hloglo := Real.log_le_log hδ2 hlo
    have hloghi := Real.log_le_log (lt_of_lt_of_le hδ2 hlo) hhi
    dsimp [B]
    have hl : |Real.log (δ / 2)| ≤ max |Real.log (δ / 2)|
        |Real.log (‖z‖ + M + δ + 1)| := le_max_left _ _
    have hr : |Real.log (‖z‖ + M + δ + 1)| ≤ max |Real.log (δ / 2)|
        |Real.log (‖z‖ + M + δ + 1)| := le_max_right _ _
    apply abs_le.mpr
    constructor
    · have haux := neg_abs_le (Real.log (δ / 2))
      linarith
    · have haux := le_abs_self (Real.log (‖z‖ + M + δ + 1))
      linarith
  have hFmeas : ∀ x ∈ S, AEStronglyMeasurable
      (fun θ : ℝ => Real.log ‖x - b (circleMap 0 1 θ)‖) μ := by
    intro x hx
    exact ((measurable_const.sub hbangle.measurable).norm.log).aestronglyMeasurable
  have hFbound : ∀ x ∈ S, ∀ᵐ θ : ℝ ∂μ,
      ‖Real.log ‖x - b (circleMap 0 1 θ)‖‖ ≤ B := by
    intro x hx
    exact Filter.Eventually.of_forall (fun θ => by
      simpa [Real.norm_eq_abs] using hlogbound x hx θ)
  have hFcont : ∀ᵐ θ : ℝ ∂μ,
      ContinuousOn (fun x : ℂ => Real.log ‖x - b (circleMap 0 1 θ)‖) S := by
    apply Filter.Eventually.of_forall
    intro θ
    apply ((continuous_id.sub continuous_const).norm.continuousOn).log
    intro x hx
    have hpos := (hdist x hx θ).1
    exact ne_of_gt (lt_of_lt_of_le hδ2 hpos)
  have hIntCont : ContinuousOn
      (fun x : ℂ => ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        Real.log ‖x - b (circleMap 0 1 θ)‖) S :=
    continuousOn_of_dominated hFmeas hFbound (integrable_const B) hFcont
  have hAvgCont : ContinuousAt
      (fun x : ℂ => (2 * Real.pi)⁻¹ *
        ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
          Real.log ‖x - b (circleMap 0 1 θ)‖) z :=
    continuousAt_const.mul (hIntCont.continuousAt hS)
  convert hAvgCont using 1
  funext x
  exact circleAverage_eq_angle_Ioc_general
    (fun ζ : ℂ => Real.log ‖x - b ζ‖) 0 1

end SpringerLean