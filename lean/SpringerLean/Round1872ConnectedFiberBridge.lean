import Mathlib.Topology.Connected.Clopen

open Set

namespace SpringerLean

/-- For an open and closed map to a preconnected target, a preconnected
set joining one entire fiber forces the whole source to be preconnected.
This avoids a separate development of lemniscate components. -/
theorem preconnectedSpace_of_open_closed_fiber_bridge
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PreconnectedSpace Y]
    (f : X → Y) (hopen : IsOpenMap f) (hclosed : IsClosedMap f)
    (y : Y) (S : Set X) (hS : IsPreconnected S) (hfiber : f ⁻¹' {y} ⊆ S) :
    PreconnectedSpace X := by
  apply preconnectedSpace_iff_clopen.2
  intro A hA
  by_cases hA0 : A = ∅
  · exact Or.inl hA0
  right
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.2 hA0
  have himageA : f '' A = univ :=
    (show IsClopen (f '' A) from ⟨hclosed A hA.isClosed, hopen A hA.isOpen⟩).eq_univ
      (hAne.image f)
  have hyA : y ∈ f '' A := by rw [himageA]; trivial
  obtain ⟨a, haA, hfa⟩ := hyA
  have haS : a ∈ S := hfiber (by simpa using hfa)
  have hSA : S ⊆ A := hS.subset_isClopen hA ⟨a, haS, haA⟩
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  have hBne : Aᶜ.Nonempty := ⟨x, hx⟩
  have himageB : f '' Aᶜ = univ :=
    (show IsClopen (f '' Aᶜ) from
      ⟨hclosed Aᶜ hA.compl.isClosed, hopen Aᶜ hA.compl.isOpen⟩).eq_univ (hBne.image f)
  have hyB : y ∈ f '' Aᶜ := by rw [himageB]; trivial
  obtain ⟨b, hbB, hfb⟩ := hyB
  have hbS : b ∈ S := hfiber (by simpa using hfb)
  exact hbB (hSA hbS)

end SpringerLean

#print axioms SpringerLean.preconnectedSpace_of_open_closed_fiber_bridge
