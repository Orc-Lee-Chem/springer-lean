import SpringerLean.Round27PotentialSubmean

open Filter
open scoped Topology

namespace SpringerLean

/-- A function that locally agrees with the positive part of the logarithm
of a nonvanishing analytic function is harmonic at points where it is
strictly positive. -/
theorem harmonicAt_of_eventuallyEq_max_log_norm_of_pos
    {P : ℂ → ℝ} {Q : ℂ → ℂ} {z : ℂ}
    (hQ : AnalyticAt ℂ Q z) (hQ0 : Q z ≠ 0)
    (hEq : P =ᶠ[𝓝 z] (fun u : ℂ => max (Real.log ‖Q u‖) 0))
    (hPpos : 0 < P z) :
    InnerProductSpace.HarmonicAt P z := by
  have hlogpos : 0 < Real.log ‖Q z‖ := by
    have hcenter := hEq.self_of_nhds
    by_contra hn
    have hnonpos : Real.log ‖Q z‖ ≤ 0 := le_of_not_gt hn
    change P z = max (Real.log ‖Q z‖) 0 at hcenter
    rw [max_eq_right hnonpos] at hcenter
    linarith
  have hcont : ContinuousAt (fun u : ℂ => Real.log ‖Q u‖) z :=
    (Real.continuousAt_log (by exact norm_ne_zero_iff.mpr hQ0)).comp
      hQ.continuousAt.norm
  have hpositive : ∀ᶠ u in 𝓝 z, 0 < Real.log ‖Q u‖ :=
    hcont.eventually (isOpen_Ioi.mem_nhds hlogpos)
  have hEqLog : P =ᶠ[𝓝 z] (fun u : ℂ => Real.log ‖Q u‖) := by
    filter_upwards [hEq, hpositive] with u hu hupos
    rw [hu]
    exact max_eq_left (le_of_lt hupos)
  exact (InnerProductSpace.harmonicAt_congr_nhds hEqLog).mpr
    (hQ.harmonicAt_log_norm hQ0)

end SpringerLean
