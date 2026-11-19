import SpringerLean.Round2138HolomorphicLimitInjectivity
import SpringerLean.Round16Univalent
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.UniformSpace.Ascoli

open Set Metric Filter Function
open scoped Topology Uniformity UniformConvergence

namespace SpringerLean

private theorem equicontinuousAt_of_mapsTo_unitDisk
    {ι : Type*} {U : Set ℂ} {A : ι → ℂ → ℂ} {z : ℂ} (hU : U ∈ 𝓝 z)
    (hd : ∀ i, DifferentiableOn ℂ (A i) U)
    (hm : ∀ i, MapsTo (A i) U (ball 0 1)) : EquicontinuousAt A z := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hU
  have hz := hsub (mem_ball_self hr)
  rw [Metric.nhds_basis_ball.equicontinuousAt_iff Metric.uniformity_basis_dist]
  intro ε hε
  obtain ⟨δ,hδ,hδ'⟩ := exists_pos_mul_lt hε (2/r)
  refine ⟨min δ r,lt_min hδ hr,?_⟩
  intro w hw i
  have hw' := mem_ball.mp hw
  have hwR : w ∈ ball z r := mem_ball.mpr (hw'.trans_le (min_le_right _ _))
  have hmaps : MapsTo (A i) (ball z r) (closedBall (A i z) 2) := by
    intro v hv
    rw [mem_closedBall]
    have hV := mem_ball_zero_iff.mp (hm i (hsub hv))
    have hZ := mem_ball_zero_iff.mp (hm i hz)
    linarith only [dist_le_norm_add_norm (A i v) (A i z),hV,hZ]
  have hle := Complex.dist_le_div_mul_dist_of_mapsTo_ball ((hd i).mono hsub) hmaps hwR
  have hlt := mul_lt_mul_of_pos_left (hw'.trans_le (min_le_left _ _))
    (div_pos (by norm_num : (0:ℝ)<2) hr)
  change dist (A i z) (A i w) < ε
  rw [dist_comm]
  exact hle.trans_lt (hlt.trans hδ')

/-- Maximize the magnitude of the derivative over normalized holomorphic
embeddings into the disk. Compactness is local uniform convergence.
The compact-open argument follows the approach of mathlib PR 33505. -/
theorem exists_extremal_holomorphic_disk_embedding
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) {x : ℂ} (hx : x ∈ U)
    (hseed : ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ MapsTo f U (ball 0 1) ∧
      InjOn f U ∧ f x = 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ MapsTo g U (ball 0 1) ∧ InjOn g U ∧
      g x = 0 ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → MapsTo f U (ball 0 1) →
        InjOn f U → f x = 0 → ‖deriv f x‖ ≤ ‖deriv g x‖ := by
  let K : Set (Set ℂ) := {s | s ⊆ U ∧ IsCompact s}
  let A : (ℂ →ᵤ[K] ℂ) → (ℂ → ℂ) := UniformOnFun.toFun K
  let S : Set (ℂ →ᵤ[K] ℂ) := {f | DifferentiableOn ℂ (A f) U ∧
    MapsTo (A f) U (ball 0 1) ∧ InjOn (A f) U ∧ A f x = 0}
  have hs : S.Nonempty := by
    obtain ⟨f,hf⟩ := hseed
    exact ⟨UniformOnFun.ofFun K f,hf⟩
  have hcompact : IsCompact (closure S) := by
    have hK : ∀ T ∈ K, IsCompact T := fun _ h => h.2
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := A) (s := S) hK
    · exact .id
    · intro T hT z hz
      exact (equicontinuousAt_of_mapsTo_unitDisk (hU.mem_nhds (hT.1 hz))
        (fun i : S => i.2.1) (fun i : S => i.2.2.1)).equicontinuousWithinAt T
    · intro T hT z hz
      exact ⟨closedBall 0 1,isCompact_closedBall _ _,fun i hi => ball_subset_closedBall (hi.2.1 (hT.1 hz))⟩
  have hlim {f : ℂ →ᵤ[K] ℂ} {T : Set (ℂ →ᵤ[K] ℂ)} :
      TendstoLocallyUniformlyOn A (A f) (𝓝[T] f) U := by
    have h : Tendsto id (𝓝[T] f) (𝓝 f) := tendsto_id'.mpr nhdsWithin_le_nhds
    simpa only [tendstoLocallyUniformlyOn_iff_forall_isCompact hU,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn,K,mem_setOf_eq,and_imp,A,comp_id] using h
  have hd (f : ℂ →ᵤ[K] ℂ) :
      ∀ᶠ g in 𝓝[S] f, DifferentiableOn ℂ (A g) U :=
    eventually_mem_nhdsWithin.mono fun g hg => hg.1
  have hnorm : ContinuousOn (fun f => ‖deriv (A f) x‖) (closure S) := by
    intro f hf
    have h : TendstoLocallyUniformlyOn A (A f) (𝓝[closure S] f) U := hlim
    have hD : ∀ᶠ g in 𝓝[closure S] f, DifferentiableOn ℂ (A g) U := by
      filter_upwards [eventually_mem_nhdsWithin] with g hg
      haveI : (𝓝[S] g).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hg
      exact hlim.differentiableOn (hd g) hU
    exact (h.deriv hD hU |>.tendsto_at hx).norm
  obtain ⟨f,hf,hmax⟩ := hcompact.exists_isMaxOn hs.closure hnorm
  haveI : (𝓝[S] f).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hf
  have hlimS : TendstoLocallyUniformlyOn A (A f) (𝓝[S] f) U := hlim
  have hD := hlimS.differentiableOn (hd f) hU
  have hf0 : A f x = 0 :=
    tendsto_nhds_unique (hlimS.tendsto_at hx)
      (tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.2.symm))
  have hle (z : ℂ) (hz : z ∈ U) : ‖A f z‖ ≤ 1 :=
    le_of_tendsto (hlimS.tendsto_at hz).norm <|
      eventually_mem_nhdsWithin.mono fun g hg => (mem_ball_zero_iff.mp (hg.2.1 hz)).le
  have hm : MapsTo (A f) U (ball 0 1) := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    by_contra h
    have hM : IsMaxOn (fun w => ‖A f w‖) U z :=
      fun w hw => (hle w hw).trans (le_of_not_gt h)
    have he := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc hU hD hz hM hx
    change A f x = A f z at he
    norm_num [←he,hf0] at h
  have hpos : 0 < ‖deriv (A f) x‖ := by
    obtain ⟨g,hg⟩ := hs
    exact (norm_pos_iff.mpr (deriv_ne_zero_of_differentiableOn_injOn hU hg.1 hg.2.2.1 hx)).trans_le
      (hmax (subset_closure hg))
  have hi : InjOn (A f) U := by
    apply (holomorphicLimit_eqOn_const_or_injOn hU hc (hd f)
      (eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.1) hlimS).resolve_left
    rintro ⟨c,hc'⟩
    rw [(hc'.eventuallyEq_of_mem (hU.mem_nhds hx)).deriv_eq,deriv_const,norm_zero] at hpos
    exact lt_irrefl 0 hpos
  refine ⟨A f,hD,hm,hi,hf0,?_⟩
  intro g hgd hgm hgi hg0
  exact hmax (subset_closure (show UniformOnFun.ofFun K g ∈ S from ⟨hgd,hgm,hgi,hg0⟩))

end SpringerLean
