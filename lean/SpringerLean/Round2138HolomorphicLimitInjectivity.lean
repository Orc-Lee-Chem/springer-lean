import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros

open Set Filter Metric Function
open scoped Topology

namespace SpringerLean

/-- A locally uniform limit of zero-free holomorphic functions is either
zero throughout the domain or zero-free. Apply the maximum modulus
principle to the reciprocals on a disk about an isolated zero. -/
theorem holomorphicLimit_eqOn_zero_or_nonvanishing
    {ι : Type*} {l : Filter ι} [l.NeBot] {U : Set ℂ} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hFn : ∀ᶠ i in l, ∀ z ∈ U, F i z ≠ 0)
    (hf : TendstoLocallyUniformlyOn F f l U) :
    EqOn f 0 U ∨ ∀ z ∈ U, f z ≠ 0 := by
  rw [or_iff_not_imp_left]
  intro h0 z hz hfz
  have hd := hf.differentiableOn hF hU
  have ha := hd.analyticOnNhd hU
  rcases (ha z hz).eventually_eq_zero_or_eventually_ne_zero with he | he
  · exact h0 (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hz he)
  · rw [eventually_nhdsWithin_iff] at he
    obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp
      (he.and (hU.eventually_mem hz))
    have hsub : closedBall z r ⊆ U := fun w hw => (hball hw).2
    have hsp : sphere z r ⊆ U := sphere_subset_closedBall.trans hsub
    have hs0 (w : ℂ) (hw : w ∈ sphere z r) : f w ≠ 0 :=
      (hball (sphere_subset_closedBall hw)).1 (ne_of_mem_sphere hw hr.ne')
    obtain ⟨w,hw,hmin⟩ := (isCompact_sphere z r).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr hr.le) (hd.continuousOn.norm.mono hsp)
    let m := ‖f w‖
    have hm : 0 < m := norm_pos_iff.mpr (hs0 w hw)
    have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_sphere z r)).mp (hf.mono hsp)
    have hv := Metric.tendstoUniformlyOn_iff.mp hu (m/2) (half_pos hm)
    have hh : ∀ᶠ i in l, m/2 ≤ ‖F i z‖ := by
      filter_upwards [hv,hF,hFn] with i hi hid hin
      have hdi : DiffContOnCl ℂ (fun v => (F i v)⁻¹) (ball z r) :=
        (hid.inv hin).diffContOnCl_ball hsub
      have hb : ∀ v ∈ frontier (ball z r), ‖(F i v)⁻¹‖ ≤ (m/2)⁻¹ := by
        intro v hv
        have hs := frontier_ball_subset_sphere hv
        have hmin' : m ≤ ‖f v‖ := hmin hs
        have hl : m/2 ≤ ‖F i v‖ := by
          have hclose := hi v hs
          have hdist : ‖f v - F i v‖ < m/2 := by
            simpa only [dist_eq_norm, norm_sub_rev] using hclose
          have ht : ‖f v‖ ≤ ‖f v - F i v‖ + ‖F i v‖ := by
            simpa only [sub_add_cancel] using norm_add_le (f v - F i v) (F i v)
          linarith only [hmin',hdist,ht]
        rw [norm_inv]
        exact (inv_le_inv₀ (norm_pos_iff.mpr (hin v (hsp hs))) (half_pos hm)).mpr hl
      have hj := Complex.norm_le_of_forall_mem_frontier_norm_le
        isBounded_ball hdi hb (subset_closure (mem_ball_self hr))
      rw [norm_inv] at hj
      exact (inv_le_inv₀ (norm_pos_iff.mpr (hin z hz)) (half_pos hm)).mp hj
    have hle := ge_of_tendsto (hf.tendsto_at hz).norm hh
    rw [hfz,norm_zero] at hle
    exact (not_le_of_gt (half_pos hm)) hle

theorem holomorphicLimit_eqOn_const_or_injOn
    {ι : Type*} {l : Filter ι} [l.NeBot] {U : Set ℂ} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hFi : ∀ᶠ i in l, InjOn (F i) U)
    (hf : TendstoLocallyUniformlyOn F f l U) :
    (∃ c : ℂ, EqOn f (fun _ => c) U) ∨ InjOn f U := by
  rw [or_iff_not_imp_left]
  intro hn x hx y hy he
  by_contra hxy
  have ha := (hf.differentiableOn hF hU).analyticOnNhd hU
  have hnb : U ∩ {y}ᶜ ∈ 𝓝 x :=
    inter_mem (hU.mem_nhds hx) (isOpen_compl_singleton.mem_nhds hxy)
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp hnb
  have hsub : ball x r ⊆ U := fun z hz => (hrb hz).1
  have hlim : TendstoLocallyUniformlyOn (fun i z => F i z - F i y)
      (fun z => f z - f y) l (ball x r) :=
    (hf.mono hsub).fun_sub
      (((hf.tendsto_at hy).tendstoUniformlyOn_const _).tendstoLocallyUniformlyOn)
  rcases holomorphicLimit_eqOn_zero_or_nonvanishing isOpen_ball (convex_ball _ _).isPreconnected
      (hF.mono fun i hi => (hi.mono hsub).sub_const _)
      (hFi.mono fun i hi z hz => sub_ne_zero.mpr (fun h =>
        (hrb hz).2 (hi (hsub hz) hy h))) hlim with h | h
  · apply hn
    refine ⟨f y,ha.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hc hx ?_⟩
    filter_upwards [ball_mem_nhds x hr] with z hz
    exact sub_eq_zero.mp (h hz)
  · exact h x (mem_ball_self hr) (sub_eq_zero.mpr he)

end SpringerLean
