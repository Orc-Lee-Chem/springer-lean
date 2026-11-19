import SpringerLean.Round33ActualArcBound
import SpringerLean.Round13PoissonFill

open MeasureTheory Metric Set
open scoped ComplexConjugate

namespace SpringerLean

/-- First Fourier mode of the normalized Poisson kernel on the unit circle. -/
theorem poissonKernel_comparator_first_mode
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    Real.circleAverage
      (fun ζ : ℂ => poissonKernel 0 z ζ * (2 * ζ.re)) 0 1 =
        2 * z.re := by
  have hnot : z ∉ sphere (0 : ℂ) 1 := by
    intro hzs
    have hlt : ‖z‖ < 1 := by
      simpa only [mem_ball, dist_zero_right] using hz
    have heq : ‖z‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hzs
    linarith
  have hkernel : ContinuousOn (poissonKernel 0 z) (sphere (0 : ℂ) 1) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    simpa only [abs_one] using
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_herglotzRieszKernel_sphere
          (c := (0 : ℂ)) (w := z) (R := (1 : ℝ))
          (by simpa only [abs_one] using hnot)))
  have hci : CircleIntegrable
      (fun ζ : ℂ => (poissonKernel 0 z ζ) • ζ) 0 1 :=
    (hkernel.smul continuousOn_id).circleIntegrable (by norm_num)
  have hmean : Real.circleAverage
      (fun ζ : ℂ => (poissonKernel 0 z ζ) • ζ) 0 1 = z := by
    have h := ((differentiable_id : Differentiable ℂ (fun ζ : ℂ => ζ)).diffContOnCl
      (s := ball (0 : ℂ) 1)).circleAverage_poissonKernel_smul hz
    exact h
  have hmeanRight : Real.circleAverage
      (fun ζ : ℂ => ((poissonKernel 0 z ζ : ℝ) : ℂ) * ζ) 0 1 = z := by
    simpa only [Complex.real_smul] using hmean
  have hre := Complex.reCLM.circleAverage_comp_comm hci
  have hre' : Real.circleAverage
      (fun ζ : ℂ => poissonKernel 0 z ζ * ζ.re) 0 1 = z.re := by
    simpa [Function.comp_def, Complex.reCLM_apply, hmeanRight, smul_eq_mul] using hre
  have hfun : (fun ζ : ℂ => poissonKernel 0 z ζ * (2 * ζ.re)) =
      (2:ℝ) • (fun ζ : ℂ => poissonKernel 0 z ζ * ζ.re) := by
    funext ζ
    simp [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, Real.circleAverage_smul, hre']
  simp [smul_eq_mul]

/-- Centered observation: the comparison Poisson integral is exactly 2r. -/
theorem poissonKernel_comparator_centered
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage
      (fun ζ : ℂ => poissonKernel 0 (r : ℂ) ζ * (2 * ζ.re)) 0 1 =
        2 * r := by
  have hz : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    simp only [mem_ball, dist_zero_right]
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  simpa only [Complex.ofReal_re] using poissonKernel_comparator_first_mode hz

/-- The Poisson kernel has the expected rational cosine form at real radius. -/
theorem poissonKernel_centered_cosine_formula
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) =
      (1-r^2)/(1+r^2-2*r*Real.cos θ) := by
  have hnorm : ‖circleMap 0 1 θ - (r : ℂ)‖^2 =
      1+r^2-2*r*Real.cos θ := by
    calc
      ‖circleMap 0 1 θ - (r : ℂ)‖^2 =
          Complex.normSq (circleMap 0 1 θ - (r : ℂ)) :=
            (Complex.normSq_eq_norm_sq _).symm
      _ = Complex.normSq (circleMap 0 1 θ) +
          Complex.normSq (r : ℂ) -
          2 * ((circleMap 0 1 θ) * conj (r : ℂ)).re :=
            Complex.normSq_sub _ _
      _ = 1+r^2-2*r*Real.cos θ := by
        simp [Complex.normSq_eq_norm_sq, norm_circleMap_zero,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
          circleMap_zero_re]
        ring
  rw [poissonKernel_def]
  simp only [sub_zero, zero_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0, norm_circleMap_zero, abs_one, one_pow]
  rw [hnorm]
/-- At a fixed interior radius the Poisson kernel's level order is exactly
the cosine level order, including all angular endpoints. -/
theorem poissonKernel_centered_le_iff_cosine_le
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (q θ : ℝ) :
    poissonKernel 0 (r : ℂ) (circleMap 0 1 q) ≤
      poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) ↔
        Real.cos q ≤ Real.cos θ := by
  have hnum : 0 < 1-r^2 := by nlinarith
  have hden (u : ℝ) : 0 < 1+r^2-2*r*Real.cos u := by
    have hc := Real.cos_le_one u
    have hs : 0 < (1-r)^2 := sq_pos_of_pos (sub_pos.mpr hr1)
    nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr hc)]
  rw [poissonKernel_centered_cosine_formula hr0.le hr1,
    poissonKernel_centered_cosine_formula hr0.le hr1,
    div_le_div_iff₀ (hden q) (hden θ)]
  constructor
  · intro h
    have hd : 1+r^2-2*r*Real.cos θ ≤ 1+r^2-2*r*Real.cos q :=
      (mul_le_mul_iff_of_pos_left hnum).mp h
    have hm : (2*r)*Real.cos q ≤ (2*r)*Real.cos θ := by nlinarith
    exact (mul_le_mul_iff_of_pos_left (by positivity : 0 < 2*r)).mp hm
  · intro h
    have hm := (mul_le_mul_iff_of_pos_left (by positivity : 0 < 2*r)).mpr h
    have hd : 1+r^2-2*r*Real.cos θ ≤ 1+r^2-2*r*Real.cos q := by
      nlinarith
    exact (mul_le_mul_iff_of_pos_left hnum).mpr hd
/-- Every nontrivial superlevel set of the actual centered Poisson kernel is
the same centered arc used in the Round33 quantile inequality. -/
theorem poissonKernel_centered_superlevel_inter_turn_eq_arc
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hqpi : q ≤ Real.pi) :
    (Ioc (0:ℝ) (2 * Real.pi) ∩
      {θ : ℝ |
        poissonKernel 0 (r : ℂ) (circleMap 0 1 q) ≤
          poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)}) =
        centeredAngularArc q := by
  calc
    (Ioc (0:ℝ) (2 * Real.pi) ∩
      {θ : ℝ |
        poissonKernel 0 (r : ℂ) (circleMap 0 1 q) ≤
          poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)}) =
      (Ioc (0:ℝ) (2 * Real.pi) ∩
        {θ : ℝ | 2 * Real.cos q ≤ 2 * (circleMap 0 1 θ).re}) := by
          ext θ
          simp only [mem_inter_iff, mem_setOf_eq, circleMap_zero_re,
            poissonKernel_centered_le_iff_cosine_le hr0 hr1]
          constructor <;> intro h <;> constructor
          · exact h.1
          · nlinarith [h.2]
          · exact h.1
          · nlinarith [h.2]
    _ = centeredAngularArc q :=
      comparator_superlevel_inter_turn_eq_centeredAngularArc q hq0 hqpi

/-- The actual Poisson superlevel set has raw angular length 2q. -/
theorem poissonKernel_centered_superlevel_raw_mass
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hqpi : q < Real.pi) :
    (volume.restrict (Ioc (0:ℝ) (2 * Real.pi))).real
      {θ : ℝ |
        poissonKernel 0 (r : ℂ) (circleMap 0 1 q) ≤
          poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)} =
      2 * q := by
  let A : Set ℝ :=
    {θ : ℝ | poissonKernel 0 (r : ℂ) (circleMap 0 1 q) ≤
      poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)}
  have hAm : MeasurableSet A := by
    have heq : A = {θ : ℝ | Real.cos q ≤ Real.cos θ} := by
      ext θ
      exact poissonKernel_centered_le_iff_cosine_le hr0 hr1 q θ
    rw [heq]
    exact measurableSet_Ici.preimage Real.continuous_cos.measurable
  change ((volume.restrict (Ioc (0:ℝ) (2 * Real.pi))) A).toReal = 2 * q
  rw [Measure.restrict_apply hAm, inter_comm,
    poissonKernel_centered_superlevel_inter_turn_eq_arc hr0 hr1 q hq0 hqpi.le,
    centeredAngularArc_volume q hq0 hqpi]
  exact ENNReal.toReal_ofReal (by positivity)

/-- Sharp actual boundary projection bound on every proper centered Poisson
superlevel set; the interval has the unnormalized angular measure 2q. -/
theorem regularExterior_projected_poisson_superlevel_le_sine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hqpi : q < Real.pi) :
    (∫ θ in {θ : ℝ |
        poissonKernel 0 (r : ℂ) (circleMap 0 1 q) ≤
          poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)},
        (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re
        ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) ≤
      4 * Real.sin q := by
  let A : Set ℝ :=
    {θ : ℝ | poissonKernel 0 (r : ℂ) (circleMap 0 1 q) ≤
      poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)}
  have hA : MeasurableSet A := by
    have heq : A = {θ : ℝ | Real.cos q ≤ Real.cos θ} := by
      ext θ
      exact poissonKernel_centered_le_iff_cosine_le hr0 hr1 q θ
    rw [heq]
    exact measurableSet_Ici.preimage Real.continuous_cos.measurable
  exact regularExterior_projected_set_le_sine_of_raw_mass
    F hc hs0 hs1 ξ hξ q hq0 hqpi A hA
    (poissonKernel_centered_superlevel_raw_mass hr0 hr1 q hq0 hqpi)
end SpringerLean