import SpringerLean.Round22BoundarySlope

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate Classical ENNReal

namespace SpringerLean

/-- The actual regularized logarithmic boundary potential is measurable
on the whole plane. It is continuous on the enlarged open image and zero
on its complement. -/
theorem regularExterior_boundary_potential_measurable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Measurable (fun w : ℂ => Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1) := by
  let G := rescaleExterior s F
  let S := G '' exteriorAbove s
  let P : ℂ → ℝ := fun w => Real.circleAverage
    (fun ζ : ℂ => Real.log ‖G ζ - w‖) 0 1
  have hSopen : IsOpen S := rescaleExterior_enlarged_image_isOpen F hc hs0
  have hPcont : ContinuousOn P S :=
    regularExterior_boundary_log_potential_continuousOn_enlarged_image
      F hc hs0 hs1
  have hmeas : Measurable (S.piecewise P (fun _ => 0)) :=
    hPcont.measurable_piecewise continuousOn_const hSopen.measurableSet
  have heq : S.piecewise P (fun _ => 0) = P := by
    funext w
    by_cases hw : w ∈ S
    · simp [Set.piecewise, hw]
    · have hwomit : w ∈ exteriorOmitted G := by
        intro himage
        obtain ⟨v, hv, rfl⟩ := himage
        apply hw
        refine ⟨v, ?_, rfl⟩
        exact lt_trans hs1 hv
      have hzero := regularExterior_omitted_boundary_log_potential_zero_all
        F hc hs0 hs1 hwomit
      change P w = 0 at hzero
      simp [Set.piecewise, hw, hzero]
  simpa only [heq] using hmeas

/-- Measurability is preserved by the actual unit rotation used in the
vertical potential problem. -/
theorem regularExterior_rotated_potential_measurable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    Measurable (regularExteriorRotatedPotential F s ξ) := by
  have hmul : Measurable (fun z : ℂ => ξ * z) := measurable_const.mul measurable_id
  have h := (regularExterior_boundary_potential_measurable
    F hc hs0 hs1).comp hmul
  convert h using 1
  funext z
  exact regularExterior_rotated_potential_eq F s ξ hξ z

/-- A linear-growth upper bound for the actual regularized potential.
Its lower bound is the previously proved Jensen nonnegativity. -/
theorem regularExterior_boundary_potential_linear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ,
      Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖)
        0 1 ≤ ‖w‖ + C + 1 := by
  obtain ⟨C, hC0, hC⟩ := rescaleExterior_sub_id_bounded F hc hs0 hs1
  refine ⟨C, hC0, ?_⟩
  intro w
  let G := rescaleExterior s F
  let S := G '' exteriorAbove s
  by_cases hw : w ∈ S
  · obtain ⟨v, hv, rfl⟩ := hw
    have hval := regularExterior_enlarged_image_boundary_log_potential
      F hc hs0 hs1 hv
    rw [hval]
    by_cases hv1 : ‖v‖ ≤ 1
    · have hlog : Real.log ‖v‖ ≤ 0 :=
        Real.log_nonpos (norm_nonneg _) hv1
      rw [max_eq_right hlog]
      nlinarith [norm_nonneg (G v)]
    · have hvE : v ∈ exteriorDisk := lt_of_not_ge hv1
      have hdist := hC v hvE
      have hnorm : ‖v‖ ≤ ‖G v‖ + ‖G v - v‖ := by
        calc
          ‖v‖ = ‖G v - (G v - v)‖ := by congr 1; abel
          _ ≤ ‖G v‖ + ‖G v - v‖ := norm_sub_le _ _
      have hlog : 0 ≤ Real.log ‖v‖ := Real.log_nonneg (le_of_lt (lt_of_not_ge hv1))
      rw [max_eq_left hlog]
      have hlogle := Real.log_le_self (norm_nonneg v)
      linarith
  · have hwomit : w ∈ exteriorOmitted G := by
      intro himage
      obtain ⟨v, hv, rfl⟩ := himage
      apply hw
      exact ⟨v, lt_trans hs1 hv, rfl⟩
    have hzero := regularExterior_omitted_boundary_log_potential_zero_all
      F hc hs0 hs1 hwomit
    rw [hzero]
    nlinarith [norm_nonneg w]

/-- Every actual bounded feasible cost is genuinely integrable. This
removes the default-value ambiguity of ordinary Lean integrals from the
BLP auxiliary function. -/
theorem regularExterior_vertical_cost_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ)
    (E : Set ℝ) (hE : E ∈ verticalFeasible h) :
    IntegrableOn
      (fun t : ℝ => regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) E := by
  obtain ⟨hEmeas, hEb, hEvol⟩ := hE
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hEb
  obtain ⟨C, hC0, hC⟩ :=
    regularExterior_boundary_potential_linear_bound F hc hs0 hs1
  let f : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  have hline : Measurable (fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hfmeas : Measurable f :=
    (regularExterior_rotated_potential_measurable F hc hs0 hs1 ξ hξ).comp hline
  have hfinite : volume E < ∞ := by
    rw [hEvol]
    finiteness
  apply IntegrableOn.of_bound hfinite hfmeas.aestronglyMeasurable
    (|a| + B + C + 1)
  apply (ae_restrict_iff' hEmeas).2
  filter_upwards [] with t ht
  have hnonneg : 0 ≤ f t :=
    regularExterior_rotated_boundary_potential_nonneg F hc hs0 hs1 ξ hξ _
  have hrot := regularExterior_rotated_potential_eq F s ξ hξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  have hupper := hC (ξ * ((a : ℂ) + (t : ℂ) * Complex.I))
  rw [← hrot, norm_mul, hξ, one_mul] at hupper
  have hlinebound : ‖(a : ℂ) + (t : ℂ) * Complex.I‖ ≤ |a| + |t| := by
    calc
      ‖(a : ℂ) + (t : ℂ) * Complex.I‖ ≤
          ‖(a : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |a| + |t| := by simp
  have htB : |t| ≤ B := by simpa [Real.norm_eq_abs] using hB t ht
  change ‖f t‖ ≤ |a| + B + C + 1
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  linarith

/-- The actual regularized unit-circle curve has a finite uniform norm
bound derived from analyticity across that circle. -/
theorem regularExterior_boundary_curve_norm_bounded
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ sphere (0 : ℂ) 1,
      ‖rescaleExterior s F ζ‖ ≤ M := by
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : ContinuousOn (rescaleExterior s F) (sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hζ
    have hz : ζ ∈ exteriorAbove s := by
      change s < ‖ζ‖
      rw [hnorm]
      exact hs1
    exact (rescaleExterior_analyticAt hs0 hF hz).continuousAt.continuousWithinAt
  have hb : Bornology.IsBounded
      (rescaleExterior s F '' sphere (0 : ℂ) 1) :=
    ((isCompact_sphere (0 : ℂ) 1).image_of_continuousOn hG).isBounded
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro ζ hζ
  exact (hM _ ⟨ζ, hζ, rfl⟩).trans (le_max_left _ _)

/-- At targets beyond the actual boundary curve, the logarithmic potential
has the expected logarithmic lower growth. -/
theorem regularExterior_boundary_potential_log_lower
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {M : ℝ} (hM : ∀ ζ ∈ sphere (0 : ℂ) 1,
      ‖rescaleExterior s F ζ‖ ≤ M)
    {w : ℂ} (hw : M < ‖w‖) :
    Real.log (‖w‖ - M) ≤
      Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1 := by
  have hpositive : 0 < ‖w‖ - M := sub_pos.mpr hw
  have hInt := regularExterior_boundary_log_circleIntegrable F hc hs0 hs1 w
  have hbound : ∀ ζ ∈ sphere (0 : ℂ) 1,
      Real.log (‖w‖ - M) ≤ Real.log ‖rescaleExterior s F ζ - w‖ := by
    intro ζ hζ
    have htri : ‖w‖ ≤ ‖rescaleExterior s F ζ - w‖ +
        ‖rescaleExterior s F ζ‖ := by
      calc
        ‖w‖ = ‖rescaleExterior s F ζ -
            (rescaleExterior s F ζ - w)‖ := by congr 1; abel
        _ ≤ ‖rescaleExterior s F ζ‖ +
            ‖rescaleExterior s F ζ - w‖ := norm_sub_le _ _
        _ = _ := by ring
    exact Real.log_le_log hpositive (by linarith [hM ζ hζ])
  have hcmp : Real.circleAverage (fun _ : ℂ => Real.log (‖w‖ - M)) 0 1 ≤
      Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1 := by
    apply Real.circleAverage_mono (circleIntegrable_const _ 0 1) hInt
    simpa using hbound
  simpa only [Real.circleAverage_const] using hcmp

/-- Along every vertical line the actual rotated potential grows beyond
every prescribed real level at both ends. -/
theorem regularExterior_rotated_potential_vertical_coercive
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a R : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      R ≤ regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I) := by
  obtain ⟨M, hM0, hM⟩ := regularExterior_boundary_curve_norm_bounded F hc hs0 hs1
  let T : ℝ := max 0 (M + Real.exp R) + 1
  refine ⟨T, by dsimp [T]; linarith [le_max_left (0 : ℝ) (M + Real.exp R)], ?_⟩
  intro t ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have him : z.im = t := by simp [z]
  have htnorm : |t| ≤ ‖ξ * z‖ := by
    rw [norm_mul, hξ, one_mul]
    simpa only [him] using Complex.abs_im_le_norm z
  have hlarge : Real.exp R ≤ ‖ξ * z‖ - M := by
    dsimp [T] at ht
    have hMexp : M + Real.exp R ≤ max 0 (M + Real.exp R) := le_max_right _ _
    linarith
  have hw : M < ‖ξ * z‖ := by linarith [Real.exp_pos R]
  have hpot := regularExterior_boundary_potential_log_lower
    F hc hs0 hs1 hM hw
  have hlog : R ≤ Real.log (‖ξ * z‖ - M) := by
    rw [← Real.log_exp R]
    exact Real.log_le_log (Real.exp_pos R) hlarge
  rw [regularExterior_rotated_potential_eq F s ξ hξ z]
  exact hlog.trans hpot

end SpringerLean
