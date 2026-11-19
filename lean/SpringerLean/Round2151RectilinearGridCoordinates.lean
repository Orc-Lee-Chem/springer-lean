import SpringerLean.Round2147RectilinearPrimitives
import Mathlib.Data.Finset.Sort

open Set Metric Complex

namespace SpringerLean

private theorem exists_strictMono_grid_cover_finset (s : Finset ℝ) :
    ∃ X : ℕ → ℝ, StrictMono X ∧ ∀ x ∈ s, ∃ i, 0 < i ∧ i < s.card+1 ∧ X i = x := by
  obtain ⟨l,hl⟩ := s.finite_toSet.bddBelow
  obtain ⟨u,hu⟩ := s.finite_toSet.bddAbove
  let e := s.orderEmbOfFin rfl
  let X : ℕ → ℝ
    | 0 => min l u - 1
    | n+1 => if hn : n < s.card then e ⟨n,hn⟩ else u + ((n-s.card:ℕ):ℝ) + 1
  have hX : StrictMono X := by
    apply strictMono_nat_of_lt_succ
    intro n
    cases n with
    | zero =>
      simp only [X]
      split_ifs with h
      · have he := hl (s.orderEmbOfFin_mem rfl ⟨0,h⟩)
        linarith [min_le_left l u]
      · have hnon : (0:ℝ) ≤ ((0-s.card:ℕ):ℝ) := by positivity
        linarith [min_le_right l u]
    | succ n =>
      simp only [X,Nat.succ_eq_add_one]
      split_ifs with hn hm hm
      · exact e.strictMono (show (⟨n,hn⟩:Fin s.card) < ⟨n+1,hm⟩ by simp)
      · have he := hu (s.orderEmbOfFin_mem rfl ⟨n,hn⟩)
        have hn' : (0:ℝ) ≤ ((n+1-s.card:ℕ):ℝ) := by positivity
        linarith
      · omega
      · have hh : n-s.card < (n+1)-s.card := by omega
        gcongr
  refine ⟨X,hX,fun x hx => ?_⟩
  have hx' : x ∈ Set.range e := by rwa [Finset.range_orderEmbOfFin]
  obtain ⟨i,hi⟩ := hx'
  refine ⟨i.val+1,by omega,by omega,?_⟩
  simp only [X,dif_pos i.isLt]
  exact hi

namespace RectilinearWalk

variable {U : Set ℂ} {a b : ℂ}

noncomputable def vertices : ∀ {b}, RectilinearWalk U a b → Finset ℂ
  | _, .point _ => {a}
  | _, .step (w := w) p _ _ => open Classical in insert w p.vertices

theorem source_mem_vertices (p : RectilinearWalk U a b) : a ∈ p.vertices := by
  classical
  induction p with
  | point => simp [vertices]
  | step _ _ _ h => exact Finset.mem_insert_of_mem h

theorem target_mem_vertices (p : RectilinearWalk U a b) : b ∈ p.vertices := by
  classical
  cases p with
  | point => simp [vertices]
  | step => exact Finset.mem_insert_self _ _

def trace : ∀ {b}, RectilinearWalk U a b → Set ℂ
  | _, .point _ => {a}
  | _, .step (z := z) (w := w) p _ _ => p.trace ∪ Rectangle z w

theorem trace_isCompact (p : RectilinearWalk U a b) : IsCompact p.trace := by
  induction p with
  | point => exact isCompact_singleton
  | step _ _ _ h => exact h.union (isCompact_uIcc.reProdIm isCompact_uIcc)

theorem trace_subset (p : RectilinearWalk U a b) : p.trace ⊆ U := by
  induction p with
  | point ha => exact singleton_subset_iff.mpr ha
  | step _ _ he hb => exact union_subset hb he

/-- The coordinates of a finite walk occur at interior indices of a
common rectangular grid. The coordinates can be nonuniformly spaced. -/
theorem exists_grid_coordinates (p : RectilinearWalk U a b) :
    ∃ (X Y : ℕ → ℝ) (N : ℕ), StrictMono X ∧ StrictMono Y ∧
      ∀ z ∈ p.vertices, ∃ i j, 0 < i ∧ i < N ∧ 0 < j ∧ j < N ∧
        z.re = X i ∧ z.im = Y j := by
  classical
  let sx := p.vertices.image Complex.re
  let sy := p.vertices.image Complex.im
  obtain ⟨X,hX,hxc⟩ := exists_strictMono_grid_cover_finset sx
  obtain ⟨Y,hY,hyc⟩ := exists_strictMono_grid_cover_finset sy
  let N := max (sx.card+1) (sy.card+1)
  refine ⟨X,Y,N,hX,hY,fun z hz => ?_⟩
  obtain ⟨i,hi,hNi,he⟩ := hxc z.re (Finset.mem_image_of_mem _ hz)
  obtain ⟨j,hj,hNj,he'⟩ := hyc z.im (Finset.mem_image_of_mem _ hz)
  exact ⟨i,j,hi,hNi.trans_le (le_max_left _ _),hj,hNj.trans_le (le_max_right _ _),he.symm,he'.symm⟩

end RectilinearWalk

end SpringerLean
