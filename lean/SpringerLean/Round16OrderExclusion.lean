import SpringerLean.Round16Coordinate
import Mathlib.RingTheory.RootsOfUnity.Complex

open Filter Metric Set
open scoped Topology

namespace SpringerLean

/-- A locally injective map cannot agree near its center with a nontrivial
power of a local coordinate of strict derivative one. -/
theorem local_injective_power_order_eq_one
    {U : Set ℂ} {G T : ℂ → ℂ} {v c : ℂ} {m : ℕ}
    (hinj : Set.InjOn G U) (hv : U ∈ 𝓝 v)
    (hm : 0 < m) (hT0 : T v = 0) (hTder : HasStrictDerivAt T 1 v)
    (hlocal : ∀ᶠ z in 𝓝 v, G z - G v = c * (T z) ^ m) : m = 1 := by
  by_contra hne
  have hm2 : 1 < m := by omega
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))
  have hω : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m (by omega)
  have hωpow : ω ^ m = 1 := hω.pow_eq_one
  have hωne : ω ≠ 1 := hω.ne_one hm2
  let V : Set ℂ := U ∩ {z | G z - G v = c * (T z) ^ m}
  have hV : V ∈ 𝓝 v := inter_mem hv hlocal
  have hmap : Filter.map T (𝓝 v) = 𝓝 (0 : ℂ) := by
    simpa only [hT0] using hTder.map_nhds_eq (by norm_num)
  have himg : T '' V ∈ 𝓝 (0 : ℂ) := by
    rw [← hmap]
    exact Filter.image_mem_map hV
  have hcont : Tendsto (fun z : ℂ => ω * z) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (fun z : ℂ => ω * z) 0 := by fun_prop
    simpa using h.tendsto
  have hpre : (fun z : ℂ => ω * z) ⁻¹' (T '' V) ∈ 𝓝 (0 : ℂ) :=
    hcont.eventually himg
  have hboth : (T '' V ∩ (fun z : ℂ => ω * z) ⁻¹' (T '' V)) ∈
      𝓝 (0 : ℂ) := inter_mem himg hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hboth
  let t : ℂ := (ε / 2 : ℝ)
  have ht0 : t ≠ 0 := by
    have htpos : 0 < ε / 2 := half_pos hε
    change ((ε / 2 : ℝ) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt htpos)
  have htball : t ∈ ball (0 : ℂ) ε := by
    change dist t 0 < ε
    simp only [dist_zero_right, t, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos hε)]
    linarith
  have ht : t ∈ T '' V ∩ (fun z : ℂ => ω * z) ⁻¹' (T '' V) := hball htball
  obtain ⟨x, hxV, hxT⟩ := ht.1
  obtain ⟨y, hyV, hyT⟩ := ht.2
  have hxU : x ∈ U := hxV.1
  have hyU : y ∈ U := hyV.1
  have hpow : (T x) ^ m = (T y) ^ m := by
    rw [hxT, hyT, mul_pow, hωpow, one_mul]
  have hG : G x = G y := by
    have hx := hxV.2
    have hy := hyV.2
    change G x - G v = c * (T x) ^ m at hx
    change G y - G v = c * (T y) ^ m at hy
    rw [hpow] at hx
    linear_combination hx - hy
  have hxy : x = y := hinj hxU hyU hG
  have heq : t = ω * t := by
    calc
      t = T x := hxT.symm
      _ = T y := congrArg T hxy
      _ = ω * t := hyT
  apply hωne
  have : ω * t = (1 : ℂ) * t := by simpa using heq.symm
  exact (mul_right_cancel₀ ht0 this)

end SpringerLean
