import SpringerLean.Round1873PolynomialLemniscateBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import SpringerLean.Round773MonicChebyshevScale

open Set Polynomial

namespace SpringerLean

/-- The unit lemniscate of every nonconstant complex Chebyshev polynomial
is connected.  This is the unscaled sharpness family for Proposition 9.2. -/
theorem chebyshev_complex_unit_lemniscate_preconnected
    (n : ℕ) (hn : 0 < n) :
    IsPreconnected {z : ℂ | ‖(Chebyshev.T ℂ (n : ℤ)).eval z‖ ≤ 1} := by
  let S : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc (-1) 1
  have hrootcard : (Chebyshev.T ℝ (n : ℤ)).roots.card =
      (Chebyshev.T ℝ (n : ℤ)).natDegree := by
    rw [Chebyshev.roots_T_real, Chebyshev.natDegree_T]
    simp only [Int.natAbs_natCast, Finset.card_val]
    rw [Finset.card_image_of_injOn]
    · simp
    · exact (Finset.range n).nodup_map_iff_injOn.mp (Chebyshev.roots_T_real_nodup n)
  have hmap : (Chebyshev.T ℝ (n : ℤ)).roots.map (algebraMap ℝ ℂ) =
      (Chebyshev.T ℂ (n : ℤ)).roots := by
    rw [← Chebyshev.map_T (algebraMap ℝ ℂ)]
    exact roots_map_of_injective_of_card_eq_natDegree
      (FaithfulSMul.algebraMap_injective ℝ ℂ) hrootcard
  have hS : IsPreconnected S :=
    isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
  have hSK : S ⊆ {z : ℂ | ‖(Chebyshev.T ℂ (n : ℤ)).eval z‖ ≤ 1} := by
    rintro z ⟨x, hx, rfl⟩
    have heval : (Chebyshev.T ℂ (n : ℤ)).eval (x : ℂ) =
        (((Chebyshev.T ℝ (n : ℤ)).eval x : ℝ) : ℂ) := by
      calc
        (Chebyshev.T ℂ (n : ℤ)).eval (x : ℂ) =
            ((Chebyshev.T ℝ (n : ℤ)).map (algebraMap ℝ ℂ)).eval (x : ℂ) := by
              rw [Chebyshev.map_T]
        _ = (((Chebyshev.T ℝ (n : ℤ)).eval x : ℝ) : ℂ) := by simp
    change ‖(Chebyshev.T ℂ (n : ℤ)).eval (x : ℂ)‖ ≤ 1
    rw [heval, Complex.norm_real]
    exact Chebyshev.abs_eval_T_real_le_one (n : ℤ) (abs_le.mpr hx)
  have hzeros : ∀ z : ℂ, (Chebyshev.T ℂ (n : ℤ)).eval z = 0 → z ∈ S := by
    intro z hz
    have hp : Chebyshev.T ℂ (n : ℤ) ≠ 0 := Chebyshev.T_ne_zero ℂ (n : ℤ)
    have hzroot : z ∈ (Chebyshev.T ℂ (n : ℤ)).roots := (mem_roots hp).2 hz
    rw [← hmap] at hzroot
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hzroot
    refine ⟨x, ?_, rfl⟩
    rw [Chebyshev.roots_T_real] at hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hx)
    exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hdegree : 0 < (Chebyshev.T ℂ (n : ℤ)).natDegree := by
    simpa [Chebyshev.natDegree_T] using hn
  exact polynomial_lemniscate_isPreconnected_of_zero_bridge
    (Chebyshev.T ℂ (n : ℤ)) hdegree 1 (by norm_num) S hS hSK hzeros

/-- The monic, capacity-normalized Chebyshev family used in the sharpness
argument has a connected unit lemniscate in the complex plane. -/
theorem monicChebyshevCandidate_unit_lemniscate_preconnected
    (n : ℕ) (hn : 0 < n) :
    IsPreconnected {z : ℂ |
      ‖((monicChebyshevCandidate n).map (algebraMap ℝ ℂ)).eval z‖ ≤ 1} := by
  have hs : (monicChebyshevScale n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _))
  have heval (z : ℂ) :
      ((monicChebyshevCandidate n).map (algebraMap ℝ ℂ)).eval z =
      (Chebyshev.T ℂ (n : ℤ)).eval ((monicChebyshevScale n : ℂ) * z) := by
    simp [monicChebyshevCandidate, Polynomial.map_comp, Chebyshev.map_T,
      Polynomial.eval_comp]
  have h := (Homeomorph.mulLeft₀ (monicChebyshevScale n : ℂ) hs).isPreconnected_preimage.mpr
    (chebyshev_complex_unit_lemniscate_preconnected n hn)
  convert h using 1
  ext z
  simp only [mem_setOf_eq, mem_preimage, Homeomorph.coe_mulLeft₀]
  rw [heval]

/-- The connectedness hypothesis in the sharpness family is genuine,
including nonemptiness, for every positive degree. -/
theorem monicChebyshevCandidate_unit_lemniscate_connected
    (n : ℕ) (hn : 0 < n) :
    IsConnected {z : ℂ |
      ‖((monicChebyshevCandidate n).map (algebraMap ℝ ℂ)).eval z‖ ≤ 1} := by
  refine ⟨⟨0, ?_⟩, monicChebyshevCandidate_unit_lemniscate_preconnected n hn⟩
  have heval :
      ((monicChebyshevCandidate n).map (algebraMap ℝ ℂ)).eval 0 =
      (((Chebyshev.T ℝ (n : ℤ)).eval 0 : ℝ) : ℂ) := by
    simp [monicChebyshevCandidate, Polynomial.map_comp, Chebyshev.map_T,
      Polynomial.eval_comp]
  change ‖((monicChebyshevCandidate n).map (algebraMap ℝ ℂ)).eval 0‖ ≤ 1
  rw [heval, Complex.norm_real]
  exact Chebyshev.abs_eval_T_real_le_one (n : ℤ) (by norm_num)

end SpringerLean

#print axioms SpringerLean.chebyshev_complex_unit_lemniscate_preconnected
#print axioms SpringerLean.monicChebyshevCandidate_unit_lemniscate_preconnected
#print axioms SpringerLean.monicChebyshevCandidate_unit_lemniscate_connected
