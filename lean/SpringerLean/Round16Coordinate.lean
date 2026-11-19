import SpringerLean.Round16LocalRoot

open Filter
open scoped Topology

namespace SpringerLean

/-- An analytic nonvanishing factor can be absorbed into a local coordinate
whose strict derivative at the center is one. -/
theorem exists_local_power_coordinate
    {h : ℂ → ℂ} {v : ℂ} (ha : AnalyticAt ℂ h v) (hv : h v ≠ 0)
    {m : ℕ} (hm : 0 < m) :
    ∃ T : ℂ → ℂ,
      T v = 0 ∧
      HasStrictDerivAt T 1 v ∧
      (∀ᶠ z in 𝓝 v, (z - v) ^ m * h z = h v * (T z) ^ m) := by
  obtain ⟨R, hR1, hRder, hRpow⟩ := exists_strict_local_pow_root m hm
  let H : ℂ → ℂ := fun z => h z / h v
  let T : ℂ → ℂ := fun z => (z - v) * R (H z)
  have hH1 : H v = 1 := by simp [H, hv]
  have hT0 : T v = 0 := by simp [T]
  have hHder : HasStrictDerivAt H (deriv h v / h v) v := by
    simpa [H] using ha.hasStrictDerivAt.div_const (h v)
  have hcomp : HasStrictDerivAt (fun z => R (H z))
      ((m : ℂ)⁻¹ * (deriv h v / h v)) v := by
    have hRder' : HasStrictDerivAt R (m : ℂ)⁻¹ (H v) := by
      simpa only [hH1] using hRder
    simpa only [Function.comp_def] using hRder'.comp v hHder
  have hsub : HasStrictDerivAt (fun z : ℂ => z - v) 1 v := by
    have h := (hasStrictDerivAt_id v).sub (hasStrictDerivAt_const v v)
    have hfun : (id - fun _ : ℂ => v) = (fun z : ℂ => z - v) := by
      funext z
      rfl
    rw [hfun] at h
    simpa using h
  have hTder : HasStrictDerivAt T 1 v := by
    have h := hsub.mul hcomp
    have hfun : ((fun z : ℂ => z - v) * fun z => R (H z)) = T := by
      funext z
      rfl
    rw [hfun] at h
    simpa only [hH1, hR1, sub_self, zero_mul, add_zero, mul_one, one_mul] using h
  have hHcont : Tendsto H (𝓝 v) (𝓝 (1 : ℂ)) := by
    simpa only [hH1] using hHder.hasDerivAt.continuousAt.tendsto
  have hpow : ∀ᶠ z in 𝓝 v, (R (H z)) ^ m = H z :=
    hHcont.eventually hRpow
  refine ⟨T, hT0, hTder, ?_⟩
  filter_upwards [hpow] with z hz
  dsimp [T, H] at *
  rw [mul_pow, hz]
  field_simp [hv]

end SpringerLean
