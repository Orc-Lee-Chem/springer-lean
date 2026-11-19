import SpringerLean.Round1499SineArcRatio
import SpringerLean.Round33CenteredArc

open MeasureTheory Set

namespace SpringerLean

/-- The centered arcs are nested by their half-width. -/
theorem centeredAngularArc_mono
    {q h : ℝ} (hqh : q ≤ h) :
    centeredAngularArc q ⊆ centeredAngularArc h := by
  intro θ hθ
  rcases hθ with hleft | hright
  · exact Or.inl ⟨hleft.1,hleft.2.trans hqh⟩
  · exact Or.inr ⟨by linarith [hright.1],hright.2⟩

/-- The mean-preserving top flattening of the comparison circle. -/
noncomputable def cappedAngularCosine (R h θ : ℝ) : ℝ :=
  by classical exact if θ ∈ centeredAngularArc h then R else 2*Real.cos θ

/-- On an arc contained in the plateau, the capped top integral is its
raw angular length times its height. -/
theorem cappedAngularCosine_small_arc_integral
    {q h R : ℝ} (hq0 : 0 ≤ q) (hqh : q ≤ h)
    (hhpi : h < Real.pi) :
    (∫ θ in centeredAngularArc q, cappedAngularCosine R h θ) =
      2*q*R := by
  classical
  have hqpi : q < Real.pi := lt_of_le_of_lt hqh hhpi
  have hsub := centeredAngularArc_mono hqh
  have hmeas : MeasurableSet (centeredAngularArc q) :=
    measurableSet_Ioc.union measurableSet_Icc
  have heq :
      (∫ θ in centeredAngularArc q, cappedAngularCosine R h θ) =
        (∫ θ in centeredAngularArc q, R) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmeas] with θ hθ
    change (if θ ∈ centeredAngularArc h then R else 2*Real.cos θ) = R
    rw [if_pos (hsub hθ)]
  rw [heq,setIntegral_const,Measure.real_def,
    centeredAngularArc_volume q hq0 hqpi,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*q)]
  simp only [smul_eq_mul]

end SpringerLean

#print axioms SpringerLean.centeredAngularArc_mono
#print axioms SpringerLean.cappedAngularCosine_small_arc_integral
