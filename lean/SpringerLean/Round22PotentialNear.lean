import SpringerLean.Round21LocalShift

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- The part of the enlarged regularized domain lying inside the unit circle
maps into the omitted set for the original exterior disk. -/
theorem regularExterior_inner_image_omitted
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s)
    {v : ℂ} (hsv : s < ‖v‖) (hv1 : ‖v‖ < 1) :
    rescaleExterior s F v ∈ exteriorOmitted (rescaleExterior s F) := by
  intro hw
  obtain ⟨u, hu, heq⟩ := hw
  have hu1 : 1 < ‖u‖ := hu
  have huabove : u ∈ exteriorAbove s := lt_trans (by linarith) hu1
  have hvabove : v ∈ exteriorAbove s := hsv
  have hsame : u = v :=
    rescaleExterior_injOn hs0 hc.2.1 huabove hvabove heq
  rw [hsame] at hu1
  linarith

/-- On the interior side of the regularized boundary, the actual boundary
logarithmic potential is zero. -/
theorem regularExterior_inner_image_boundary_log_potential_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hsv : s < ‖v‖) (hv1 : ‖v‖ < 1) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - rescaleExterior s F v‖)
      0 1 = 0 := by
  exact regularExterior_omitted_boundary_log_potential_zero_all
    F hc hs0 hs1 (regularExterior_inner_image_omitted F hc hs0 hsv hv1)

/-- The boundary potential of an image value on the whole enlarged
regularized exterior domain. -/
theorem regularExterior_enlarged_image_boundary_log_potential
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hsv : s < ‖v‖) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - rescaleExterior s F v‖)
      0 1 = max (Real.log ‖v‖) 0 := by
  rcases lt_trichotomy ‖v‖ 1 with hv1 | hv1 | hv1
  · rw [regularExterior_inner_image_boundary_log_potential_zero
      F hc hs0 hs1 hsv hv1]
    have hlog : Real.log ‖v‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) (le_of_lt hv1)
    exact (max_eq_right hlog).symm
  · rw [regularExterior_curve_boundary_log_potential_zero F hc hs0 hs1 hv1]
    simp [hv1]
  · rw [regularExterior_image_boundary_log_potential F hc hs0 hs1 hv1]
    exact (max_eq_left (Real.log_nonneg (le_of_lt hv1))).symm

/-- The regularized map is noncritical throughout its enlarged analytic
domain, including the unit circle itself. -/
theorem rescaleExterior_deriv_ne_zero_above
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s)
    {v : ℂ} (hv : v ∈ exteriorAbove s) :
    deriv (rescaleExterior s F) v ≠ 0 := by
  have hUopen : IsOpen (exteriorAbove s) := by
    simpa [exteriorAbove, Set.preimage] using
      (isOpen_Ioi.preimage (continuous_norm : Continuous (fun z : ℂ => ‖z‖)))
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : DifferentiableOn ℂ (rescaleExterior s F) (exteriorAbove s) := by
    intro z hz
    exact (rescaleExterior_analyticAt hs0 hF hz).differentiableAt.differentiableWithinAt
  exact deriv_ne_zero_of_differentiableOn_injOn hUopen hG
    (rescaleExterior_injOn hs0 hc.2.1) hv

/-- The image of the enlarged domain is open, by the same local inverse
theorem that gives noncriticality on that domain. -/
theorem rescaleExterior_enlarged_image_isOpen
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) :
    IsOpen (rescaleExterior s F '' exteriorAbove s) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro w ⟨v, hv, rfl⟩
  have hUopen : IsOpen (exteriorAbove s) := by
    simpa [exteriorAbove, Set.preimage] using
      (isOpen_Ioi.preimage (continuous_norm : Continuous (fun z : ℂ => ‖z‖)))
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : AnalyticAt ℂ (rescaleExterior s F) v :=
    rescaleExterior_analyticAt hs0 hF hv
  have hd : deriv (rescaleExterior s F) v ≠ 0 :=
    rescaleExterior_deriv_ne_zero_above F hc hs0 hv
  have hImage : rescaleExterior s F '' exteriorAbove s ∈
      map (rescaleExterior s F) (𝓝 v) :=
    Filter.image_mem_map (hUopen.mem_nhds hv)
  rw [hG.hasStrictDerivAt.map_nhds_eq hd] at hImage
  exact hImage

/-- The actual regularized boundary potential is continuous at each point
of the actual regularized boundary curve. The local inverse is constructed
at that point of the enlarged analytic domain; no boundary extension of F
is assumed. -/
theorem regularExterior_boundary_log_potential_continuousAt_enlarged_image
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hsv : s < ‖v‖) :
    ContinuousAt
      (fun w : ℂ => Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1)
      (rescaleExterior s F v) := by
  let G := rescaleExterior s F
  have hvU : v ∈ exteriorAbove s := hsv
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : AnalyticAt ℂ G v := rescaleExterior_analyticAt hs0 hF hvU
  have hd : deriv G v ≠ 0 := rescaleExterior_deriv_ne_zero_above F hc hs0 hvU
  let R : ℂ → ℂ := hG.hasStrictDerivAt.localInverse G (deriv G v) v hd
  have hR0 : R (G v) = v := by
    exact HasStrictFDerivAt.localInverse_apply_image
      (hG.hasStrictDerivAt.hasStrictFDerivAt_equiv hd)
  have hRcont : ContinuousAt R (G v) :=
    (hG.hasStrictDerivAt.hasStrictFDerivAt_equiv hd).localInverse_continuousAt
  have hUopen : IsOpen (exteriorAbove s) := by
    simpa [exteriorAbove, Set.preimage] using
      (isOpen_Ioi.preimage (continuous_norm : Continuous (fun z : ℂ => ‖z‖)))
  have hRin : ∀ᶠ w in 𝓝 (G v), R w ∈ exteriorAbove s := by
    apply hRcont.eventually
    rw [hR0]
    exact hUopen.mem_nhds hvU
  have hright : ∀ᶠ w in 𝓝 (G v), G (R w) = w :=
    hG.hasStrictDerivAt.eventually_right_inverse hd
  let P : ℂ → ℝ := fun w => Real.circleAverage
    (fun ζ : ℂ => Real.log ‖G ζ - w‖) 0 1
  let M : ℂ → ℝ := fun w => max (Real.log ‖R w‖) 0
  have hnear : P =ᶠ[𝓝 (G v)] M := by
    filter_upwards [hRin, hright] with w hwU hRw
    have hvalue := regularExterior_enlarged_image_boundary_log_potential
      F hc hs0 hs1 hwU
    change P (G (R w)) = M w at hvalue
    rwa [hRw] at hvalue
  have hvpos : 0 < ‖v‖ := lt_trans hs0 hsv
  have hRnorm : ContinuousAt (fun w => ‖R w‖) (G v) := hRcont.norm
  have hM : ContinuousAt M (G v) := by
    have hlog : ContinuousAt (fun w => Real.log ‖R w‖) (G v) := by
      apply (Real.continuousAt_log ?_).comp hRnorm
      rw [hR0]
      exact ne_of_gt hvpos
    exact hlog.max continuousAt_const
  exact hM.congr_of_eventuallyEq hnear

/-- The actual boundary logarithmic potential is continuous throughout
the open image of the enlarged regularized domain. -/
theorem regularExterior_boundary_log_potential_continuousOn_enlarged_image
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ContinuousOn
      (fun w : ℂ => Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1)
      (rescaleExterior s F '' exteriorAbove s) := by
  rintro w ⟨v, hv, rfl⟩
  exact (regularExterior_boundary_log_potential_continuousAt_enlarged_image
    F hc hs0 hs1 hv).continuousWithinAt

/-- The special boundary-curve version used for the positive-threshold
contact point. -/
theorem regularExterior_boundary_log_potential_continuousAt_curve
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : ‖v‖ = 1) :
    ContinuousAt
      (fun w : ℂ => Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1)
      (rescaleExterior s F v) := by
  exact regularExterior_boundary_log_potential_continuousAt_enlarged_image
    F hc hs0 hs1 (by rw [hv]; exact hs1)

/-- Rotation by a unit complex number transports the actual logarithmic
potential without changing its normalization. -/
theorem regularExterior_rotated_potential_eq
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (hξ : ‖ξ‖ = 1) (z : ℂ) :
    regularExteriorRotatedPotential F s ξ z =
      Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - ξ * z‖) 0 1 := by
  apply Real.circleAverage_congr_sphere
  intro ζ _
  change Real.log ‖z - conj ξ * rescaleExterior s F ζ‖ =
    Real.log ‖rescaleExterior s F ζ - ξ * z‖
  have hunit : ξ * conj ξ = 1 := by
    rw [RCLike.mul_conj, hξ]
    norm_num
  have hid : ξ * (z - conj ξ * rescaleExterior s F ζ) =
      ξ * z - rescaleExterior s F ζ := by
    rw [mul_sub, ← mul_assoc, hunit, one_mul]
  calc
    Real.log ‖z - conj ξ * rescaleExterior s F ζ‖ =
        Real.log ‖ξ * (z - conj ξ * rescaleExterior s F ζ)‖ := by
      rw [norm_mul, hξ, one_mul]
    _ = Real.log ‖rescaleExterior s F ζ - ξ * z‖ := by
      rw [hid, norm_sub_rev]

/-- Continuity of the rotated actual potential at every actual contact
point on the regularized boundary. -/
theorem regularExterior_rotated_potential_continuousAt_curve
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {v : ℂ} (hv : ‖v‖ = 1) :
    ContinuousAt (regularExteriorRotatedPotential F s ξ)
      (conj ξ * rescaleExterior s F v) := by
  let G := rescaleExterior s F
  have hunit : ξ * conj ξ = 1 := by
    rw [RCLike.mul_conj, hξ]
    norm_num
  have hpoint : ξ * (conj ξ * G v) = G v := by
    rw [← mul_assoc, hunit, one_mul]
  have hbase := regularExterior_boundary_log_potential_continuousAt_curve
    F hc hs0 hs1 hv
  have hmul : ContinuousAt (fun z : ℂ => ξ * z) (conj ξ * G v) :=
    continuousAt_const.mul continuousAt_id
  have hcomp : ContinuousAt
      (fun z : ℂ => Real.circleAverage
        (fun ζ : ℂ => Real.log ‖G ζ - ξ * z‖) 0 1)
      (conj ξ * G v) := by
    exact hbase.comp_of_eq hmul hpoint
  have heq : (regularExteriorRotatedPotential F s ξ) =
      (fun z : ℂ => Real.circleAverage
        (fun ζ : ℂ => Real.log ‖G ζ - ξ * z‖) 0 1) := by
    funext z
    exact regularExterior_rotated_potential_eq F s ξ hξ z
  rw [heq]
  exact hcomp

/-- A positive actual vertical difference has a zero of the rotated
potential where the potential is continuous along that vertical line. -/
theorem regularExterior_contact_zero_and_continuous
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a : ℝ)
    (hpos : 0 < (∫ t : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a t)) :
    ∃ t₀ : ℝ,
      regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t₀ : ℂ) * Complex.I) = 0 ∧
      ContinuousAt
        (fun t : ℝ => regularExteriorRotatedPotential F s ξ
          ((a : ℂ) + (t : ℂ) * Complex.I)) t₀ := by
  obtain ⟨v, hv, hvre⟩ :=
    regularExterior_projection_exists_eq_of_vertical_integral_pos
      F hc hs0 hs1 ξ a hpos
  let W : ℂ := conj ξ * rescaleExterior s F v
  have hvnorm : ‖v‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using hv
  have hpoint : ((a : ℂ) + (W.im : ℂ) * Complex.I) = W := by
    rw [← hvre]
    exact Complex.re_add_im W
  have hcurve : ContinuousAt (regularExteriorRotatedPotential F s ξ) W :=
    regularExterior_rotated_potential_continuousAt_curve F hc hs0 hs1 ξ hξ hvnorm
  have hline : ContinuousAt (fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I) W.im := by
    fun_prop
  refine ⟨W.im, ?_, hcurve.comp_of_eq hline hpoint⟩
  rw [hpoint, regularExterior_rotated_potential_eq F s ξ hξ]
  have hunit : ξ * conj ξ = 1 := by
    rw [RCLike.mul_conj, hξ]
    norm_num
  rw [show ξ * W = rescaleExterior s F v from by
    dsimp [W]
    rw [← mul_assoc, hunit, one_mul]]
  exact regularExterior_curve_boundary_log_potential_zero F hc hs0 hs1 hvnorm

/-- Along a vertical line through an actual regularized boundary point, the
rotated logarithmic potential is integrable on every sufficiently short
closed interval. This is the local integrability needed for the boundary
slope estimate; no global potential regularity is assumed. -/
theorem regularExterior_rotated_potential_integrable_near_curve
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {v : ℂ} (hv : ‖v‖ = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 ≤ h → h < δ →
      IntegrableOn
        (fun t : ℝ => regularExteriorRotatedPotential F s ξ
          (((conj ξ * rescaleExterior s F v).re : ℂ) +
            (t : ℂ) * Complex.I))
        (Icc ((conj ξ * rescaleExterior s F v).im - h)
          ((conj ξ * rescaleExterior s F v).im + h)) := by
  let G := rescaleExterior s F
  let W := conj ξ * G v
  let p : ℝ → ℂ := fun t => (W.re : ℂ) + (t : ℂ) * Complex.I
  let S : Set ℂ := G '' exteriorAbove s
  have hunit : ξ * conj ξ = 1 := by
    rw [RCLike.mul_conj, hξ]
    norm_num
  have hp0 : ξ * p W.im = G v := by
    have hW : p W.im = W := Complex.re_add_im W
    rw [hW]
    dsimp [W]
    rw [← mul_assoc, hunit, one_mul]
  have hSopen : IsOpen S := rescaleExterior_enlarged_image_isOpen F hc hs0
  have hS0 : G v ∈ S := ⟨v, by change s < ‖v‖; rw [hv]; exact hs1, rfl⟩
  have hmap : Continuous (fun t : ℝ => ξ * p t) := by
    fun_prop
  have hEvent : ∀ᶠ t in 𝓝 W.im, ξ * p t ∈ S := by
    apply hmap.continuousAt.eventually
    change S ∈ 𝓝 (ξ * p W.im)
    rw [hp0]
    exact hSopen.mem_nhds hS0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hEvent
  refine ⟨δ, hδ, ?_⟩
  intro h hh0 hhδ
  have hsub : ∀ t ∈ Icc (W.im - h) (W.im + h), ξ * p t ∈ S := by
    intro t ht
    apply hball
    change dist t W.im < δ
    rw [Real.dist_eq]
    have hbound : |t - W.im| ≤ h := abs_le.mpr (by constructor <;> linarith [ht.1, ht.2])
    exact lt_of_le_of_lt hbound hhδ
  have hcont : ContinuousOn
      (fun t : ℝ => Real.circleAverage
        (fun ζ : ℂ => Real.log ‖G ζ - ξ * p t‖) 0 1)
      (Icc (W.im - h) (W.im + h)) := by
    exact (regularExterior_boundary_log_potential_continuousOn_enlarged_image
      F hc hs0 hs1).comp hmap.continuousOn hsub
  have heq : (fun t : ℝ => regularExteriorRotatedPotential F s ξ (p t)) =
      (fun t : ℝ => Real.circleAverage
        (fun ζ : ℂ => Real.log ‖G ζ - ξ * p t‖) 0 1) := by
    funext t
    exact regularExterior_rotated_potential_eq F s ξ hξ (p t)
  change IntegrableOn (fun t : ℝ => regularExteriorRotatedPotential F s ξ (p t)) _
  rw [heq]
  exact hcont.integrableOn_compact isCompact_Icc

end SpringerLean
