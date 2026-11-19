import SpringerLean.Round1531PeakArcPointwise

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 320000

/-- A continuous profile symmetric about the positive real direction has
twice its positive-half-arc integral on a centered arc. -/
theorem centeredAngularArc_integral_symmetric
    (f : ℝ → ℝ) (hf : Continuous f)
    (hsym : ∀ θ : ℝ, f (2*Real.pi-θ)=f θ)
    {h : ℝ} (hh0 : 0 ≤ h) (hhpi : h < Real.pi) :
    (∫ θ in centeredAngularArc h, f θ) =
      2*(∫ θ in Ioc (0:ℝ) h, f θ) := by
  have hdisj : Disjoint (Ioc (0:ℝ) h)
      (Icc (2*Real.pi-h) (2*Real.pi)) := by
    apply disjoint_left.mpr
    intro θ hleft hright
    linarith [hleft.2,hright.1]
  have hleftInt : IntegrableOn f (Ioc (0:ℝ) h) :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hrightInt : IntegrableOn f (Icc (2*Real.pi-h) (2*Real.pi)) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hright :
      (∫ θ in Icc (2*Real.pi-h) (2*Real.pi), f θ) =
        ∫ θ in Ioc (0:ℝ) h, f θ := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] :
        2*Real.pi-h ≤ 2*Real.pi),
      ← intervalIntegral.integral_of_le hh0]
    have hcomp :
        (∫ θ in (0:ℝ)..h, f (2*Real.pi-θ)) =
          ∫ θ in (2*Real.pi-h)..(2*Real.pi), f θ := by
      simpa only [sub_zero] using
        (intervalIntegral.integral_comp_sub_left (f:=f)
          (a:=(0:ℝ)) (b:=h) (2*Real.pi))
    rw [←hcomp]
    simp_rw [hsym]
  rw [centeredAngularArc,
    setIntegral_union hdisj measurableSet_Icc hleftInt hrightInt,
    hright]
  ring

end SpringerLean

#print axioms SpringerLean.centeredAngularArc_integral_symmetric
