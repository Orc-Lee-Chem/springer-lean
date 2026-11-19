import SpringerLean.Round1325RotatedOppositeWitness
import SpringerLean.Round1319CandidateFirst359
import SpringerLean.Round619ActualSecondEndpoint

open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- The selected opposite-half convex-hull maximizer is beyond 8/5 and
is an actual omitted point.  The first endpoint comes directly from
the weak Catalan candidate, including equality. -/
theorem exteriorOmitted_exists_candidate_two_actual_endpoints359
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧
      (359/180 : ℝ) < ‖P₁‖ ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      P₂ ∈ exteriorOmitted F ∧
      (8/5 : ℝ) < ‖P₂‖ ∧
      (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) := by
  obtain ⟨P₁,hP₁,hlarge,hmax,hR2,_,_⟩ :=
    exteriorOmitted_exists_candidate_first_endpoint359 F hc k hk hB
  let ξ : ℂ := P₁/(‖P₁‖ : ℂ)
  have hRpos : (0 : ℝ) < ‖P₁‖ := by linarith
  have hR0 : (‖P₁‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
  have hξP : ξ*(‖P₁‖ : ℂ)=P₁ := by
    dsimp [ξ]
    field_simp [hR0]
  obtain ⟨w,hw,hwproj⟩ :=
    exteriorOmitted_opposite_hull_witness_of_first359 F hc P₁ hP₁ hlarge hR2
  obtain ⟨P₂,hP₂,hneg,hhalf⟩ :=
    exteriorOmitted_exists_half_radius_maximizer F hc ξ
  have hwneg : (conj ξ*w).re ≤ 0 := by linarith
  have hP₂ge : ‖w‖ ≤ ‖P₂‖ := hhalf w hw hwneg
  have hwNorm : (8/5 : ℝ) < ‖w‖ := by
    have hh := Complex.re_le_norm (-(conj ξ*w))
    have hξ : ‖ξ‖ = 1 := by
      dsimp [ξ]
      simp [norm_div, Complex.norm_real, abs_of_pos hRpos, ne_of_gt hRpos]
    rw [Complex.neg_re, norm_neg, norm_mul, Complex.norm_conj, hξ, one_mul] at hh
    linarith
  have hP₂large : (8/5 : ℝ) < ‖P₂‖ := lt_of_lt_of_le hwNorm hP₂ge
  have hsign (v : ℂ) :
      (conj P₁*v).re = ‖P₁‖*(conj ξ*v).re := by
    calc
      _ = (conj (ξ*(‖P₁‖ : ℂ))*v).re := by rw [hξP]
      _ = ‖P₁‖*(conj ξ*v).re := by
        simp [map_mul, mul_assoc, Complex.mul_re]
        ring
  have hP₂neg : (conj P₁*P₂).re ≤ 0 := by
    rw [hsign]
    exact mul_nonpos_of_nonneg_of_nonpos hRpos.le hneg
  have hP₂max : ∀ v ∈ convexHull ℝ (exteriorOmitted F),
      (conj P₁*v).re ≤ 0 → ‖v‖ ≤ ‖P₂‖ := by
    intro v hv hnv
    rw [hsign] at hnv
    exact hhalf v hv (nonpos_of_mul_nonpos_right hnv hRpos)
  have hP₂actual : P₂ ∈ exteriorOmitted F :=
    exteriorOmitted_half_maximizer_mem_of_radius_bounds F hc P₁ P₂
      (subset_convexHull ℝ _ hP₁) hP₂ (by linarith) hP₂large.le
      hP₂neg hP₂max
  exact ⟨P₁,P₂,hP₁,hlarge,hmax,hP₂actual,hP₂large,hneg,hhalf⟩

/-- Every selected first global maximizer and every corresponding
opposite-half hull maximizer obey the strict radius bound, not only
the particular witnesses chosen above. -/
theorem exteriorOmitted_candidate_any_second_radius_gt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ exteriorOmitted F)
    (hmax₁ : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖)
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hhalf : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj P₁*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) :
    (8/5 : ℝ) < ‖P₂‖ := by
  obtain ⟨Q,hQ,hQbig,hQmax,hQ2,_,_⟩ :=
    exteriorOmitted_exists_candidate_first_endpoint359 F hc k hk hB
  have hnorm : ‖P₁‖ = ‖Q‖ :=
    le_antisymm (hQmax P₁ (subset_convexHull ℝ _ hP₁))
      (hmax₁ Q (subset_convexHull ℝ _ hQ))
  have hlarge : (359/180 : ℝ) < ‖P₁‖ := by rw [hnorm]; exact hQbig
  have hP₁2 : ‖P₁‖ ≤ 2 := exteriorOmitted_norm_le_two F hc hP₁
  let ξ : ℂ := P₁/(‖P₁‖ : ℂ)
  have hRpos : (0 : ℝ) < ‖P₁‖ := by linarith
  have hR0 : (‖P₁‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
  have hξP : ξ*(‖P₁‖ : ℂ)=P₁ := by
    dsimp [ξ]
    field_simp [hR0]
  obtain ⟨w,hw,hwproj⟩ :=
    exteriorOmitted_opposite_hull_witness_of_first359 F hc P₁ hP₁ hlarge hP₁2
  have hξ : ‖ξ‖ = 1 := by
    dsimp [ξ]
    simp [norm_div, Complex.norm_real, abs_of_pos hRpos, ne_of_gt hRpos]
  have hsign (v : ℂ) :
      (conj P₁*v).re = ‖P₁‖*(conj ξ*v).re := by
    calc
      _ = (conj (ξ*(‖P₁‖ : ℂ))*v).re := by rw [hξP]
      _ = ‖P₁‖*(conj ξ*v).re := by
        simp [map_mul, mul_assoc, Complex.mul_re]
        ring
  have hwneg : (conj P₁*w).re ≤ 0 := by
    rw [hsign]
    exact mul_nonpos_of_nonneg_of_nonpos hRpos.le (by linarith)
  have hwNorm : (8/5 : ℝ) < ‖w‖ := by
    have hh := Complex.re_le_norm (-(conj ξ*w))
    rw [Complex.neg_re, norm_neg, norm_mul, Complex.norm_conj, hξ, one_mul] at hh
    linarith
  exact lt_of_lt_of_le hwNorm (hhalf w hw hwneg)

end SpringerLean
