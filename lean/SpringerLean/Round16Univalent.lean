import SpringerLean.Round16OrderExclusion
import Mathlib.Topology.Perfect

open Filter Set
open scoped Topology

namespace SpringerLean

/-- The centered difference of an analytic map injective on an open set
cannot vanish identically on any neighborhood of an interior point. -/
theorem analyticOrderAt_sub_ne_top_of_injOn
    {U : Set ℂ} {G : ℂ → ℂ} {v : ℂ}
    (hU : IsOpen U) (hinj : Set.InjOn G U) (hv : v ∈ U) :
    analyticOrderAt (fun z => G z - G v) v ≠ ⊤ := by
  intro htop
  have hzero : ∀ᶠ z in 𝓝 v, G z - G v = 0 :=
    analyticOrderAt_eq_top.mp htop
  have hpunct : ∀ᶠ z in 𝓝[≠] v, z ∈ U ∧ G z = G v ∧ z ≠ v := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (hU.mem_nhds hv),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hzero,
      self_mem_nhdsWithin] with z hzU hz0 hzNe
    exact ⟨hzU, sub_eq_zero.mp hz0, hzNe⟩
  obtain ⟨z, hzU, hzEq, hzNe⟩ := hpunct.exists
  exact hzNe (hinj hzU hv hzEq)

/-- A holomorphic injection on an open subset of the complex plane has no
critical points. This proof uses the local analytic order, a power-root
coordinate, and the root-of-unity contradiction. -/
theorem deriv_ne_zero_of_differentiableOn_injOn
    {U : Set ℂ} {G : ℂ → ℂ} {v : ℂ}
    (hU : IsOpen U) (hDiff : DifferentiableOn ℂ G U)
    (hinj : Set.InjOn G U) (hv : v ∈ U) : deriv G v ≠ 0 := by
  let f : ℂ → ℂ := fun z => G z - G v
  have hGa : AnalyticAt ℂ G v := hDiff.analyticAt (hU.mem_nhds hv)
  have hfa : AnalyticAt ℂ f v := hGa.sub analyticAt_const
  have hfinite : analyticOrderAt f v ≠ ⊤ :=
    analyticOrderAt_sub_ne_top_of_injOn hU hinj hv
  let m : ℕ := analyticOrderNatAt f v
  obtain ⟨h, hha, hh0, hfact⟩ :=
    (hfa.analyticOrderNatAt_eq_iff hfinite).mp rfl
  have hm : 0 < m := by
    by_contra hnot
    have hm0 : m = 0 := by omega
    have hvfact := hfact.self_of_nhds
    have hhzero : h v = 0 := by
      change G v - G v = (v - v) ^ m • h v at hvfact
      rw [hm0] at hvfact
      simpa only [sub_self, pow_zero, one_smul] using hvfact.symm
    exact hh0 hhzero
  obtain ⟨T, hT0, hTder, hcoord⟩ :=
    exists_local_power_coordinate hha hh0 hm
  have hlocal : ∀ᶠ z in 𝓝 v, G z - G v = h v * (T z) ^ m := by
    filter_upwards [hfact, hcoord] with z hz1 hz2
    change G z - G v = (z - v) ^ m • h z at hz1
    simpa only [smul_eq_mul] using hz1.trans hz2
  have hm1 : m = 1 :=
    local_injective_power_order_eq_one hinj (hU.mem_nhds hv) hm hT0 hTder hlocal
  have hlocal1 : (fun z : ℂ => G z - G v) =ᶠ[𝓝 v]
      (fun z => h v * T z) := by
    change ∀ᶠ z in 𝓝 v, G z - G v = h v * T z
    simpa only [hm1, pow_one] using hlocal
  have hder : deriv G v = h v := by
    have heq := hlocal1.deriv_eq
    rw [deriv_sub_const, deriv_const_mul_field, hTder.hasDerivAt.deriv,
      mul_one] at heq
    exact heq
  rw [hder]
  exact hh0

end SpringerLean
