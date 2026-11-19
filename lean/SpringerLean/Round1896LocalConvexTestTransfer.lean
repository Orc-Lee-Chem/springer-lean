import SpringerLean.Round1895ActualLocalConvexTrace

open MeasureTheory Filter Set Metric
open scoped Topology ComplexConjugate

namespace SpringerLean

set_option maxHeartbeats 600000
set_option Elab.async false

/-- A monotone radial test is bounded by its convex projection test on the
actual boundary trace. This is the functional step behind the p in [4,8]
interpolation; the specific derivative estimates for its test remain
separate. -/
theorem actualRadialTrace_antitone_localConvexTest_le_cosine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (h : ℝ → ℝ) (hh : Continuous h)
    (hanti : AntitoneOn h (Icc (0 : ℝ) 1))
    (hconv : ConvexOn ℝ (Set.Icc (-1) 1) (fun x : ℝ => h |x|)) :
    (2 * Real.pi)⁻¹ *
      (∫ θ in Ioo (-Real.pi) Real.pi,
        h (‖actualExteriorRadialTrace F θ‖ / 2)) ≤
      Real.circleAverage (fun z : ℂ => h |z.re|) 0 1 := by
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo]
    finiteness)
  obtain ⟨M,hM⟩ :=
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).image hh).isBounded.exists_norm_le
  let T : ℝ → ℝ := fun θ => ‖actualExteriorRadialTrace F θ‖ / 2
  let X : ℝ → ℝ := fun θ => |(conj ξ * actualExteriorRadialTrace F θ).re / 2|
  have hTaem : AEStronglyMeasurable (fun θ => h (T θ)) μ := by
    have hf : Continuous (fun z : ℂ => h (‖z‖ / 2)) := by fun_prop
    exact hf.comp_aestronglyMeasurable
      (actualExteriorRadialTrace_aestronglyMeasurable F hc)
  have hXaem : AEStronglyMeasurable (fun θ => h (X θ)) μ := by
    have hf : Continuous (fun z : ℂ => h |(conj ξ * z).re / 2|) := by fun_prop
    exact hf.comp_aestronglyMeasurable
      (actualExteriorRadialTrace_aestronglyMeasurable F hc)
  have hbound : ∀ᵐ θ : ℝ ∂μ, T θ ∈ Icc 0 1 ∧ X θ ∈ Icc 0 1 ∧ X θ ≤ T θ := by
    filter_upwards [actualExteriorRadialTrace_ae_norm_le_two F hc] with θ hn
    have hnX : |(conj ξ * actualExteriorRadialTrace F θ).re| ≤
        ‖actualExteriorRadialTrace F θ‖ := by
      calc
        _ ≤ ‖conj ξ * actualExteriorRadialTrace F θ‖ := Complex.abs_re_le_norm _
        _ = ‖actualExteriorRadialTrace F θ‖ := by
          rw [norm_mul, Complex.norm_conj, hξ, one_mul]
    have hx : X θ ≤ T θ := by
      dsimp [X,T]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right hnX (by norm_num)
    have ht0 : 0 ≤ T θ := by dsimp [T]; positivity
    have hx0 : 0 ≤ X θ := by dsimp [X]; positivity
    have ht1 : T θ ≤ 1 := by dsimp [T]; linarith
    exact ⟨⟨ht0,ht1⟩,⟨hx0,le_trans hx ht1⟩,hx⟩
  have hTi : Integrable (fun θ => h (T θ)) μ := by
    apply (integrable_const M).mono' hTaem
    filter_upwards [hbound] with θ hb
    exact hM _ ⟨T θ,hb.1,rfl⟩
  have hXi : Integrable (fun θ => h (X θ)) μ := by
    apply (integrable_const M).mono' hXaem
    filter_upwards [hbound] with θ hb
    exact hM _ ⟨X θ,hb.2.1,rfl⟩
  have hpoint : ∀ᵐ θ : ℝ ∂μ, h (T θ) ≤ h (X θ) := by
    filter_upwards [hbound] with θ hb
    exact hanti hb.2.1 hb.1 hb.2.2
  have hint : (∫ θ in Ioo (-Real.pi) Real.pi, h (T θ)) ≤
      ∫ θ in Ioo (-Real.pi) Real.pi, h (X θ) :=
    integral_mono_ae hTi hXi hpoint
  have hscaled := mul_le_mul_of_nonneg_left hint
    (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
  have horder := actualExteriorRadialTrace_half_projection_localConvex_le
    F hc ξ hξ (fun x : ℝ => h |x|) hconv (by fun_prop)
  exact le_trans hscaled horder

/-- The quadratic compensation used by the [4,8] interpolation is kept
inside the convex test. No moment endpoint or derivative estimate is
assumed in this transfer theorem. -/
theorem actualRadialTrace_compensated_localConvexTest_le_cosine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (h : ℝ → ℝ) (hh : Continuous h)
    (hanti : AntitoneOn h (Icc (0 : ℝ) 1)) (c : ℝ)
    (hconv : ConvexOn ℝ (Set.Icc (-1) 1)
      (fun x : ℝ => h |x| + c * x ^ 2)) :
    (2 * Real.pi)⁻¹ *
      (∫ θ in Ioo (-Real.pi) Real.pi,
        h (‖actualExteriorRadialTrace F θ‖ / 2) +
        c * ((conj ξ * actualExteriorRadialTrace F θ).re / 2) ^ 2) ≤
      Real.circleAverage (fun z : ℂ => h |z.re| + c * z.re ^ 2) 0 1 := by
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo]
    finiteness)
  let T : ℂ → ℝ := fun z => ‖z‖ / 2
  let X : ℂ → ℝ := fun z => (conj ξ * z).re / 2
  let f : ℂ → ℝ := fun z => h (T z) + c * (X z) ^ 2
  let g : ℂ → ℝ := fun z => h |X z| + c * (X z) ^ 2
  have hfc : Continuous f := by dsimp [f,T,X]; fun_prop
  have hgc : Continuous g := by dsimp [g,X]; fun_prop
  have hIntegrable (u : ℂ → ℝ) (hu : Continuous u) :
      Integrable (fun θ : ℝ => u (actualExteriorRadialTrace F θ)) μ := by
    obtain ⟨M,hM⟩ :=
      ((isCompact_closedBall (0 : ℂ) 2).image hu).isBounded.exists_norm_le
    apply (integrable_const M).mono'
      (hu.comp_aestronglyMeasurable
        (actualExteriorRadialTrace_aestronglyMeasurable F hc))
    filter_upwards [actualExteriorRadialTrace_ae_norm_le_two F hc] with θ hn
    have hz : actualExteriorRadialTrace F θ ∈ closedBall (0 : ℂ) 2 := by
      simpa only [mem_closedBall, dist_zero_right] using hn
    exact hM _ ⟨actualExteriorRadialTrace F θ,hz,rfl⟩
  have hfi := hIntegrable f hfc
  have hgi := hIntegrable g hgc
  have hpoint : ∀ᵐ θ : ℝ ∂μ,
      f (actualExteriorRadialTrace F θ) ≤
        g (actualExteriorRadialTrace F θ) := by
    filter_upwards [actualExteriorRadialTrace_ae_norm_le_two F hc] with θ hn
    let z := actualExteriorRadialTrace F θ
    have hnX : |(conj ξ * z).re| ≤ ‖z‖ := by
      calc
        _ ≤ ‖conj ξ * z‖ := Complex.abs_re_le_norm _
        _ = ‖z‖ := by rw [norm_mul, Complex.norm_conj, hξ, one_mul]
    have hx : |X z| ≤ T z := by
      dsimp [X,T]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right hnX (by norm_num)
    have ht : T z ∈ Icc (0 : ℝ) 1 := by
      dsimp [T]
      constructor
      · positivity
      · linarith
    have hxx : |X z| ∈ Icc (0 : ℝ) 1 :=
      ⟨abs_nonneg _, le_trans hx ht.2⟩
    have hhx := hanti hxx ht hx
    dsimp [f,g]
    linarith
  have hint :
      (∫ θ in Ioo (-Real.pi) Real.pi,
        f (actualExteriorRadialTrace F θ)) ≤
      ∫ θ in Ioo (-Real.pi) Real.pi,
        g (actualExteriorRadialTrace F θ) :=
    integral_mono_ae hfi hgi hpoint
  have hscaled := mul_le_mul_of_nonneg_left hint
    (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
  have horder := actualExteriorRadialTrace_half_projection_localConvex_le
    F hc ξ hξ (fun x : ℝ => h |x| + c * x ^ 2) hconv (by fun_prop)
  exact le_trans hscaled horder

end SpringerLean

#check @SpringerLean.actualRadialTrace_antitone_localConvexTest_le_cosine
#print axioms SpringerLean.actualRadialTrace_antitone_localConvexTest_le_cosine
#check @SpringerLean.actualRadialTrace_compensated_localConvexTest_le_cosine
#print axioms SpringerLean.actualRadialTrace_compensated_localConvexTest_le_cosine
