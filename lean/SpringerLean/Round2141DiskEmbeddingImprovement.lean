import SpringerLean.Round2140DiskMobius
import SpringerLean.Round16Univalent
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Complex.BranchLogRoot

open Set Filter Metric Function
open scoped Topology

namespace SpringerLean

/-- The branch property used by the extremal proof of disk uniformization. -/
def HasHolomorphicSquareRootBranches (U : Set ℂ) : Prop :=
  ∀ q : ℂ → ℂ, DifferentiableOn ℂ q U → (∀ z ∈ U, q z ≠ 0) →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ EqOn (fun z => g z ^ 2) q U

theorem hasHolomorphicSquareRootBranches_of_isSimplyConnected
    {U : Set ℂ} (hU : IsOpen U) (hc : IsSimplyConnected U) :
    HasHolomorphicSquareRootBranches U := by
  intro q hq hn
  have h0 : (0:ℂ) ∉ q '' U := by
    rintro ⟨z,hz,hz0⟩
    exact hn z hz hz0
  obtain ⟨g,hg,hsq⟩ := Complex.exists_continuousOn_pow_eq hc hU hq.continuousOn h0 two_ne_zero
  refine ⟨g,?_,fun z _ => hsq z⟩
  intro z hz
  have hg0 : g z ≠ 0 := fun h => hn z hz (by rw [←hsq,h]; norm_num)
  have hp : HasDerivAt (fun w : ℂ => w^2) (2*g z) (g z) := by
    simpa using hasDerivAt_pow 2 (g z)
  have he : ((fun w : ℂ => w^2) ∘ g) =ᶠ[𝓝 z] q := .of_forall hsq
  exact (HasDerivAt.of_comp_left (hg.continuousAt (hU.mem_nhds hz)) hp
    (hq.hasDerivAt (hU.mem_nhds hz)) (mul_ne_zero two_ne_zero hg0) he).differentiableAt.differentiableWithinAt

private theorem norm_deriv_lt_one_of_noninjective_disk
    (f : ℂ → ℂ) (hd : DifferentiableOn ℂ f (ball 0 1))
    (hm : MapsTo f (ball 0 1) (ball 0 1)) (h0 : f 0 = 0)
    (hn : ¬InjOn f (ball 0 1)) : ‖deriv f 0‖ < 1 := by
  have hc : MapsTo f (ball 0 1) (closedBall (f 0) 1) := by
    rw [h0]
    exact fun z hz => ball_subset_closedBall (hm hz)
  have hle := Complex.norm_deriv_le_one_of_mapsTo_ball hd hc zero_lt_one
  refine lt_of_le_of_ne hle (fun he => hn ?_)
  have hds : ‖dslope f 0 0‖ = 1/1 := by rw [dslope_same,he,div_one]
  have ha := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd hc
    (mem_ball_self zero_lt_one) hds
  have hne : deriv f 0 ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at he
    exact zero_ne_one he
  intro z hz w hw hzw
  have haZ : f z = z*deriv f 0 := by
    simpa only [h0,sub_zero,zero_add,smul_eq_mul,dslope_same] using ha hz
  have haW : f w = w*deriv f 0 := by
    simpa only [h0,sub_zero,zero_add,smul_eq_mul,dslope_same] using ha hw
  exact mul_right_cancel₀ hne (haZ.symm.trans (hzw.trans haW))

/-- A missing point of an embedding into the disk allows a strict
increase of the normalized derivative. The reverse factor is a
noninjective disk self-map, so Schwarz gives strictness. -/
theorem improve_holomorphic_disk_embedding
    {U : Set ℂ} (hU : IsOpen U) (hroot : HasHolomorphicSquareRootBranches U)
    {x : ℂ} (hx : x ∈ U) (f : ℂ → ℂ)
    (hd : DifferentiableOn ℂ f U) (hm : MapsTo f U (ball 0 1))
    (hi : InjOn f U) (h0 : f x = 0) (hn : ¬SurjOn f U (ball 0 1)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ MapsTo G U (ball 0 1) ∧ InjOn G U ∧
      G x = 0 ∧ ‖deriv f x‖ < ‖deriv G x‖ := by
  obtain ⟨b,hb,hb'⟩ : ∃ b ∈ ball (0:ℂ) 1, b ∉ f '' U := by
    by_contra h
    apply hn
    intro y hy
    by_contra hy'
    exact h ⟨y,hy,hy'⟩
  let q := diskMobius b ∘ f
  have hqd : DifferentiableOn ℂ q U := (diskMobius_differentiableOn hb).comp hd hm
  have hqn (z : ℂ) (hz : z ∈ U) : q z ≠ 0 := by
    intro h
    have he := (diskMobius_injOn hb) (hm hz) hb
      (h.trans (diskMobius_at_parameter b).symm)
    exact hb' ⟨z,hz,he⟩
  obtain ⟨g,hgd,hgq⟩ := hroot q hqd hqn
  have hgm : MapsTo g U (ball 0 1) := by
    intro z hz
    have h := mem_ball_zero_iff.mp ((diskMobius_mapsTo hb).comp hm hz)
    change ‖q z‖ < 1 at h
    rw [←hgq hz,norm_pow] at h
    exact mem_ball_zero_iff.mpr (by nlinarith [norm_nonneg (g z)])
  have hgi : InjOn g U := by
    intro z hz w hw he
    apply hi hz hw
    apply diskMobius_injOn hb (hm hz) (hm hw)
    exact (hgq hz).symm.trans ((congrArg (fun t : ℂ => t^2) he).trans (hgq hw))
  let d := g x
  let G := diskMobius d ∘ g
  have hD := hgm hx
  have hGd := (diskMobius_differentiableOn hD).comp hgd hgm
  have hGm := (diskMobius_mapsTo hD).comp hgm
  have hGi := (diskMobius_injOn hD).comp hgi hgm
  have hG0 : G x = 0 := diskMobius_at_parameter d
  let B := ball (0:ℂ) 1
  let P (z : ℂ) := z^2
  have hPm : MapsTo P B B := by
    intro z hz
    have h := mem_ball_zero_iff.mp hz
    apply mem_ball_zero_iff.mpr
    rw [show P z = z^2 from rfl,norm_pow]
    nlinarith [norm_nonneg z]
  let ψ := diskMobius (-b) ∘ P ∘ diskMobius (-d)
  have hψm : MapsTo ψ B B :=
    (diskMobius_mapsTo (neg_mem_unitDisk hb)).comp (hPm.comp (diskMobius_mapsTo (neg_mem_unitDisk hD)))
  have hPd : DifferentiableOn ℂ P B := by unfold P; fun_prop
  have hψd : DifferentiableOn ℂ ψ B :=
    (diskMobius_differentiableOn (neg_mem_unitDisk hb)).comp
      (hPd.comp (diskMobius_differentiableOn (neg_mem_unitDisk hD)) (diskMobius_mapsTo (neg_mem_unitDisk hD)))
      (hPm.comp (diskMobius_mapsTo (neg_mem_unitDisk hD)))
  have hd2 : d^2 = -b := by
    have hh := hgq hx
    change d^2 = diskMobius b (f x) at hh
    rwa [h0,diskMobius_at_zero] at hh
  have hψ0 : ψ 0 = 0 := by
    simp only [ψ,comp_apply,diskMobius_at_zero,neg_neg,P,hd2,diskMobius_at_parameter]
  have hψn : ¬InjOn ψ B := by
    intro h
    let v : ℂ := 1/2
    have hv : v ∈ B := mem_ball_zero_iff.mpr (by norm_num [v,norm_div])
    have hv' := neg_mem_unitDisk hv
    have he : ψ (diskMobius d v) = ψ (diskMobius d (-v)) := by
      change diskMobius (-b) (diskMobius (-d) (diskMobius d v)^2) =
        diskMobius (-b) (diskMobius (-d) (diskMobius d (-v))^2)
      rw [diskMobius_leftInverse hD hv,diskMobius_leftInverse hD hv',neg_sq]
    have hr := h (diskMobius_mapsTo hD hv) (diskMobius_mapsTo hD hv') he
    have hf := diskMobius_injOn hD hv hv' hr
    norm_num [v] at hf
  have hψ := norm_deriv_lt_one_of_noninjective_disk ψ hψd hψm hψ0 hψn
  have hcomp : EqOn (ψ ∘ G) f U := by
    intro z hz
    change diskMobius (-b) ((diskMobius (-d) (diskMobius d (g z)))^2) = f z
    rw [diskMobius_leftInverse hD (hgm hz)]
    have hs : g z ^ 2 = diskMobius b (f z) := hgq hz
    rw [hs,diskMobius_leftInverse hb (hm hz)]
  have hψat : HasDerivAt ψ (deriv ψ 0) (G x) := by
    rw [hG0]
    exact hψd.hasDerivAt (ball_mem_nhds _ zero_lt_one)
  have hGat := hGd.hasDerivAt (hU.mem_nhds hx)
  have hder : deriv f x = deriv ψ 0 * deriv G x :=
    ((hcomp.eventuallyEq_of_mem (hU.mem_nhds hx)).deriv_eq).symm.trans (hψat.comp x hGat).deriv
  refine ⟨G,hGd,hGm,hGi,hG0,?_⟩
  rw [hder,norm_mul]
  have hpos := norm_pos_iff.mpr (deriv_ne_zero_of_differentiableOn_injOn hU hGd hGi hx)
  simpa only [one_mul] using mul_lt_mul_of_pos_right hψ hpos

end SpringerLean
