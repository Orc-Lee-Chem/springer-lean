import SpringerLean.Round1496ActualSecondGlobalCap
import SpringerLean.Round632OmittedSequentialLimit
import SpringerLean.Round639RegularBoundaryOmitted
import SpringerLean.Round636OmittedCollarUniform

open scoped ComplexConjugate
open Filter
open scoped Topology

namespace SpringerLean

/-- Full-hull endpoint projection caps apply pointwise to the actual
harmonic filling at every point of the open source disk. -/
theorem actualHarmonic_two_endpoint_caps_of_hull_caps
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P₁ P₂ : ℂ)
    (hcap₁ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ ‖P₁‖)
    (hcap₂ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₂/(‖P₂‖:ℂ))*w).re ≤ ‖P₂‖)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (conj (P₁/(‖P₁‖:ℂ))*actualHarmonic F z).re ≤ ‖P₁‖ ∧
    (conj (P₂/(‖P₂‖:ℂ))*actualHarmonic F z).re ≤ ‖P₂‖ := by
  have hw := actualHarmonic_mem_convexHull_omitted F hc hz
  exact ⟨hcap₁ _ hw, hcap₂ _ hw⟩

/-- Every convergent cluster of the actual regularized boundary curves
as the regularization tends to one lies in the original omitted set.
This is the compactness input for an approximate boundary cap. -/
theorem rescaleExterior_unitCircle_cluster_mem_omitted
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℕ → ℝ} {ζ : ℕ → ℂ} {w : ℂ}
    (hs : Tendsto s atTop (𝓝 (1:ℝ)))
    (hs0 : ∀ᶠ n in atTop, 0 < s n)
    (hs1 : ∀ᶠ n in atTop, s n < 1)
    (hζ : ∀ᶠ n in atTop, ‖ζ n‖ = 1)
    (hw : Tendsto (fun n => rescaleExterior (s n) F (ζ n))
      atTop (𝓝 w)) :
    w ∈ exteriorOmitted F := by
  apply exteriorOmitted_rescale_mem_of_tendsto F hc hs ?_ hw
  filter_upwards [hs0,hs1,hζ] with n hn0 hn1 hnorm
  exact rescaleExterior_unitCircle_mem_omitted F hc hn0 hn1 hnorm

/-- The genuine boundary curves of the regularized maps satisfy any
original omitted-hull projection cap up to an arbitrarily small error,
uniformly over the entire unit circle, along the standard scale sequence. -/
theorem regularExterior_projection_cap_eventually_scaleSeq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (R : ℝ)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ ζ : ℂ, ‖ζ‖=1 →
      (conj ξ*rescaleExterior (omittedScaleSeq n) F ζ).re ≤ R+ε := by
  let ψ : ℂ → ℝ := fun w => (conj ξ*w).re-R
  have hψ : Continuous ψ := by fun_prop
  have hK : ∀ w ∈ exteriorOmitted F, w ∈ Set.univ → ψ w ≤ 0 := by
    intro w hw _
    have hh := hcap w (subset_convexHull ℝ (exteriorOmitted F) hw)
    dsimp [ψ]
    linarith
  have he := exteriorOmitted_rescale_inequality_eventually_scaleSeq
    F hc Set.univ isClosed_univ ψ hψ hK hε
  filter_upwards [he] with n hn ζ hζ
  have hboundary := rescaleExterior_unitCircle_mem_omitted F hc
    (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) hζ
  have hle := hn _ hboundary (Set.mem_univ _)
  dsimp [ψ] at hle
  linarith

/-- A nonslit Catalan candidate has the same selected two endpoints
whose regularized boundary projections satisfy uniform approximate
caps along one common scale tail. -/
theorem exteriorInverseCoeff_candidate_selected_regularized_two_caps
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧
      Set.EqOn F (slitMap a) exteriorDisk)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      (∀ᶠ n : ℕ in atTop, ∀ ζ : ℂ, ‖ζ‖=1 →
        (conj (P₁/(‖P₁‖:ℂ))*rescaleExterior (omittedScaleSeq n) F ζ).re ≤
          ‖P₁‖+ε ∧
        (conj (P₂/(‖P₂‖:ℂ))*rescaleExterior (omittedScaleSeq n) F ζ).re ≤
          ‖P₂‖+ε) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,hlog₁,hlog₂,
    hW₁,hW₂,hmW₁,hmW₂,hmax₁,hneg,hmax₂,hcap₁,hcap₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_global_caps
      F hc k hk hB hns
  have he₁ := regularExterior_projection_cap_eventually_scaleSeq
    F hc (P₁/(‖P₁‖:ℂ)) ‖P₁‖ hcap₁ hε
  have he₂ := regularExterior_projection_cap_eventually_scaleSeq
    F hc (P₂/(‖P₂‖:ℂ)) ‖P₂‖ hcap₂ hε
  refine ⟨P₁,P₂,hP₁,hP₂,?_⟩
  filter_upwards [he₁,he₂] with n hn₁ hn₂ ζ hζ
  exact ⟨hn₁ ζ hζ,hn₂ ζ hζ⟩

end SpringerLean

#print axioms SpringerLean.actualHarmonic_two_endpoint_caps_of_hull_caps
#print axioms SpringerLean.rescaleExterior_unitCircle_cluster_mem_omitted
#print axioms SpringerLean.regularExterior_projection_cap_eventually_scaleSeq
#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_regularized_two_caps
