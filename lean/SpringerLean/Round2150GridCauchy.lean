import SpringerLean.Round2149GridCellFilling
import SpringerLean.Round2146GridCycleSummation
import Mathlib.Analysis.Complex.HasPrimitives

open Set Complex Finset

namespace SpringerLean

noncomputable def gridHorizontalIntegral
    (X Y : ℕ → ℝ) (f : ℂ → ℂ) (i j : ℕ) : ℂ :=
  ∫ x in X i..X (i+1), f (x+Y j*I)

noncomputable def gridVerticalIntegral
    (X Y : ℕ → ℝ) (f : ℂ → ℂ) (i j : ℕ) : ℂ :=
  I * (∫ y in Y j..Y (j+1), f (X i+y*I))

/-- Cauchy's theorem for a closed chain supported on finitely many
edges of a rectangular grid inside a domain with connected spherical
complement. The integrands are evaluated on the actual edges. -/
theorem gridCycle_integral_eq_zero
    {U P : Set ℂ} (hP : IsCompact P) (hPU : P ⊆ U)
    (hc : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' U)ᶜ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (X Y : ℕ → ℝ) (hX : StrictMono X) (hY : StrictMono Y)
    (H V : ℕ → ℕ → ℂ) (N : ℕ)
    (hbase : ∀ i, H i 0 = H (i+1) 0 + V (i+1) 0)
    (hbalance : ∀ i j, H i (j+1) + V (i+1) j = H (i+1) (j+1) + V (i+1) (j+1))
    (hbottom : ∀ i, H i 0 = 0) (hleft : ∀ j, H 0 j = 0) (hVleft : ∀ j, V 0 j = 0)
    (htop : ∀ i j, N ≤ j → V i j = 0) (hright : ∀ i j, N ≤ i → H i j = 0)
    (hH : ∀ i j, H i j ≠ 0 → gridHorizontalEdge X Y i j ⊆ P)
    (hV : ∀ i j, V i j ≠ 0 → gridVerticalEdge X Y i j ⊆ P) :
    ∑ i ∈ range (N+1), ∑ j ∈ range (N+1),
      (H i j * gridHorizontalIntegral X Y f i j + V i j * gridVerticalIntegral X Y f i j) = 0 := by
  let L := gridHorizontalIntegral X Y f
  let M := gridVerticalIntegral X Y f
  have h := gridCycle_pairing H V L M N hbase hbalance hleft hVleft htop hright
  rw [←h]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hw : gridCellWeight H i j = 0
  · rw [hw,zero_mul]
  have hfill := gridCell_subset_filling_of_weight_ne_zero X Y hX hY H V N P
    hbase hbalance hbottom hleft htop hright hH hV hw
  have hcell := hfill.trans (continuumFill_subset_of_sphere_compl_preconnected hP hPU hc)
  have hu (i j : ℕ) :
      Rectangle ((X i : ℂ)+Y j*I) ((X (i+1) : ℂ)+Y (j+1)*I) = gridCell X Y i j := by
    have hXI : X i ≤ X (i+1) := hX.monotone (Nat.le_succ _)
    have hYI : Y j ≤ Y (j+1) := hY.monotone (Nat.le_succ _)
    simp [Rectangle,gridCell,uIcc_of_le hXI,uIcc_of_le hYI]
  have hrect : Rectangle ((X i:ℂ)+Y j*I) ((X (i+1):ℂ)+Y (j+1)*I) ⊆ U := (hu i j).symm ▸ hcell
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((X i:ℂ)+Y j*I) ((X (i+1):ℂ)+Y (j+1)*I) (hf.mono hrect)
  have hsort : L i j + M (i+1) j - L i (j+1) - M i j = 0 := by
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,
      Complex.mul_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,sub_zero,add_zero,
      zero_add,smul_eq_mul] at hcauchy
    dsimp [L,M,gridHorizontalIntegral,gridVerticalIntegral]
    linear_combination hcauchy
  rw [hsort,mul_zero]

end SpringerLean
