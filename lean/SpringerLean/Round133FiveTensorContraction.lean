import SpringerLean.Round132FiveKernelActualMatrix

set_option maxHeartbeats 1000000

namespace SpringerLean

/-- The same actual-map normalized fifth Grunsky matrix, as a finite
kernel with output index first and input index second. -/
noncomputable def schoberActualC5 (F : ℂ → ℂ)
    (j i : Fin 5) : ℂ :=
  ((Real.sqrt ((j.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
    ((Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      schoberBiCoeff (j.val + 1) (i.val + 1)
        (schoberKernelQ5
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9))

theorem schoberActualC5_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : Fin 5 → ℂ) :
    (∑ j : Fin 5,
      ‖∑ i : Fin 5, schoberActualC5 F j i * v i‖ ^ 2) ≤
      ∑ i : Fin 5, ‖v i‖ ^ 2 := by
  simpa only [schoberActualC5] using
    exterior_schoberKernelQ5_normalized_contraction F hc v

theorem schoberActualC5_bilinear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : Fin 5 → ℂ) :
    ‖∑ j : Fin 5,
      v j * (∑ i : Fin 5, schoberActualC5 F j i * v i)‖ ≤
      ∑ i : Fin 5, ‖v i‖ ^ 2 :=
  finiteComplexBilinear_norm_le_of_l2_contraction
    (schoberActualC5 F) (schoberActualC5_contraction F hc) v

noncomputable def schoberActualC5Tensor2 (F : ℂ → ℂ)
    (p q : Fin 5 × Fin 5) : ℂ :=
  schoberActualC5 F p.1 q.1 * schoberActualC5 F p.2 q.2

noncomputable def schoberActualC5Tensor3 (F : ℂ → ℂ)
    (p q : (Fin 5 × Fin 5) × Fin 5) : ℂ :=
  schoberActualC5Tensor2 F p.1 q.1 * schoberActualC5 F p.2 q.2

noncomputable def schoberActualC5Tensor4 (F : ℂ → ℂ)
    (p q : ((Fin 5 × Fin 5) × Fin 5) × Fin 5) : ℂ :=
  schoberActualC5Tensor3 F p.1 q.1 * schoberActualC5 F p.2 q.2

noncomputable def schoberActualC5Tensor5 (F : ℂ → ℂ)
    (p q : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5) : ℂ :=
  schoberActualC5Tensor4 F p.1 q.1 * schoberActualC5 F p.2 q.2

theorem schoberActualC5Tensor2_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : Fin 5 × Fin 5 → ℂ) :
    (∑ p : Fin 5 × Fin 5,
      ‖∑ q : Fin 5 × Fin 5,
        schoberActualC5Tensor2 F p q * v q‖ ^ 2) ≤
      ∑ q : Fin 5 × Fin 5, ‖v q‖ ^ 2 := by
  simpa only [schoberActualC5Tensor2] using
    finiteComplexTensor_contraction (schoberActualC5 F) (schoberActualC5 F)
      (schoberActualC5_contraction F hc)
      (schoberActualC5_contraction F hc) v

theorem schoberActualC5Tensor3_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : (Fin 5 × Fin 5) × Fin 5 → ℂ) :
    (∑ p : (Fin 5 × Fin 5) × Fin 5,
      ‖∑ q : (Fin 5 × Fin 5) × Fin 5,
        schoberActualC5Tensor3 F p q * v q‖ ^ 2) ≤
      ∑ q : (Fin 5 × Fin 5) × Fin 5, ‖v q‖ ^ 2 := by
  simpa only [schoberActualC5Tensor3] using
    finiteComplexTensor_contraction
      (schoberActualC5Tensor2 F) (schoberActualC5 F)
      (schoberActualC5Tensor2_contraction F hc)
      (schoberActualC5_contraction F hc) v

theorem schoberActualC5Tensor4_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : ((Fin 5 × Fin 5) × Fin 5) × Fin 5 → ℂ) :
    (∑ p : ((Fin 5 × Fin 5) × Fin 5) × Fin 5,
      ‖∑ q : ((Fin 5 × Fin 5) × Fin 5) × Fin 5,
        schoberActualC5Tensor4 F p q * v q‖ ^ 2) ≤
      ∑ q : ((Fin 5 × Fin 5) × Fin 5) × Fin 5, ‖v q‖ ^ 2 := by
  simpa only [schoberActualC5Tensor4] using
    finiteComplexTensor_contraction
      (schoberActualC5Tensor3 F) (schoberActualC5 F)
      (schoberActualC5Tensor3_contraction F hc)
      (schoberActualC5_contraction F hc) v

theorem schoberActualC5Tensor5_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5 → ℂ) :
    (∑ p : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5,
      ‖∑ q : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5,
        schoberActualC5Tensor5 F p q * v q‖ ^ 2) ≤
      ∑ q : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5,
        ‖v q‖ ^ 2 := by
  simpa only [schoberActualC5Tensor5] using
    finiteComplexTensor_contraction
      (schoberActualC5Tensor4 F) (schoberActualC5 F)
      (schoberActualC5Tensor4_contraction F hc)
      (schoberActualC5_contraction F hc) v

theorem schoberActualC5Tensor2_bilinear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : Fin 5 × Fin 5 → ℂ) :
    ‖∑ p : Fin 5 × Fin 5,
      v p * (∑ q : Fin 5 × Fin 5,
        schoberActualC5Tensor2 F p q * v q)‖ ≤
      ∑ p : Fin 5 × Fin 5, ‖v p‖ ^ 2 :=
  finiteComplexBilinear_norm_le_of_l2_contraction
    (schoberActualC5Tensor2 F) (schoberActualC5Tensor2_contraction F hc) v

theorem schoberActualC5Tensor3_bilinear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : (Fin 5 × Fin 5) × Fin 5 → ℂ) :
    ‖∑ p : (Fin 5 × Fin 5) × Fin 5,
      v p * (∑ q : (Fin 5 × Fin 5) × Fin 5,
        schoberActualC5Tensor3 F p q * v q)‖ ≤
      ∑ p : (Fin 5 × Fin 5) × Fin 5, ‖v p‖ ^ 2 :=
  finiteComplexBilinear_norm_le_of_l2_contraction
    (schoberActualC5Tensor3 F) (schoberActualC5Tensor3_contraction F hc) v

theorem schoberActualC5Tensor4_bilinear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : ((Fin 5 × Fin 5) × Fin 5) × Fin 5 → ℂ) :
    ‖∑ p : ((Fin 5 × Fin 5) × Fin 5) × Fin 5,
      v p * (∑ q : ((Fin 5 × Fin 5) × Fin 5) × Fin 5,
        schoberActualC5Tensor4 F p q * v q)‖ ≤
      ∑ p : ((Fin 5 × Fin 5) × Fin 5) × Fin 5, ‖v p‖ ^ 2 :=
  finiteComplexBilinear_norm_le_of_l2_contraction
    (schoberActualC5Tensor4 F) (schoberActualC5Tensor4_contraction F hc) v

theorem schoberActualC5Tensor5_bilinear_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5 → ℂ) :
    ‖∑ p : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5,
      v p * (∑ q : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5,
        schoberActualC5Tensor5 F p q * v q)‖ ≤
      ∑ p : (((Fin 5 × Fin 5) × Fin 5) × Fin 5) × Fin 5,
        ‖v p‖ ^ 2 :=
  finiteComplexBilinear_norm_le_of_l2_contraction
    (schoberActualC5Tensor5 F) (schoberActualC5Tensor5_contraction F hc) v

end SpringerLean
