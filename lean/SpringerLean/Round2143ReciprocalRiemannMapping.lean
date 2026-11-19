import SpringerLean.Round2142RiemannMapping
import SpringerLean.Round2136EvenContinuumFactorReduction
import SpringerLean.Round2137ReciprocalSphereComplement

open Set Metric Function

namespace SpringerLean

theorem reciprocalDiskUniformization_of_squareRootBranches
    (K : Set ℂ) (hK : IsCompact K) (a b : ℂ) (ha : a ∈ continuumFill K) (hb : b ∈ continuumFill K)
    (hab : a ≠ b) (hroot : HasHolomorphicSquareRootBranches (reciprocalExteriorDomain K a)) :
    Nonempty (ReciprocalDiskUniformization K a) := by
  let U := reciprocalExteriorDomain K a
  let D := ball (0:ℂ) 1
  have hU := reciprocalExteriorDomain_isOpen K hK a
  have h0 : (0:ℂ) ∈ U := mem_insert _ _
  obtain ⟨g,hd,hg,hg0⟩ := exists_holomorphic_disk_bijOn_of_squareRootBranches hU
    (reciprocalExteriorDomain_isConnected K hK a ha).isPreconnected
    (reciprocalExteriorDomain_ne_univ K a b hb hab) hroot h0
  let f := invFunOn g U
  have hleft := hg.injOn.leftInvOn_invFunOn
  have hright := hg.surjOn.rightInvOn_invFunOn
  have hm : MapsTo f D U := hg.surjOn.mapsTo_invFunOn
  have hf0 : f 0 = 0 := by
    have he := hleft h0
    rwa [hg0] at he
  have hf : DifferentiableOn ℂ f D := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := hg.surjOn hw
    exact (analyticAt_invFunOn_of_open_injOn g U hU hd hg.injOn z hz).differentiableAt.differentiableWithinAt
  refine ⟨⟨f,hf,⟨hm,?_,?_⟩,hf0⟩⟩
  · intro w hw z hz he
    exact (hright hw).symm.trans ((congrArg g he).trans (hright hz))
  · intro z hz
    exact ⟨g z,hg.mapsTo hz,hleft hz⟩

theorem reciprocalDiskUniformization_of_isSimplyConnected
    (K : Set ℂ) (hK : IsCompact K) (a b : ℂ) (ha : a ∈ continuumFill K) (hb : b ∈ continuumFill K)
    (hab : a ≠ b) (hc : IsSimplyConnected (reciprocalExteriorDomain K a)) :
    Nonempty (ReciprocalDiskUniformization K a) :=
  reciprocalDiskUniformization_of_squareRootBranches K hK a b ha hb hab
    (hasHolomorphicSquareRootBranches_of_isSimplyConnected (reciprocalExteriorDomain_isOpen K hK a) hc)

end SpringerLean
