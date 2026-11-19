import SpringerLean.DiskEnergy

open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- The exact coefficient energy of the derivative difference tends to zero.
The exponent is `j+1`, as dictated by the actual regularized germ. -/
theorem exteriorForwardCoeff_dilated_difference_energy_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    Tendsto
      (fun s : ℝ => ∑' j : ℕ,
        ((j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) *
          (s ^ (j + 1) - 1) ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let w : ℕ → ℝ := fun j =>
    (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    positivity
  have hsum : Summable w := exteriorForwardCoeff_weighted_summable F hc
  have hfilter : (𝓝[<] (1 : ℝ)) ≤ 𝓝 (1 : ℝ) := nhdsWithin_le_nhds
  have hterm (j : ℕ) : Tendsto
      (fun s : ℝ => w j * (s ^ (j + 1) - 1) ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hs : Tendsto (fun s : ℝ => s) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_id.mono_left hfilter
    convert tendsto_const_nhds.mul ((hs.pow (j + 1)).sub tendsto_const_nhds |>.pow 2) using 1 <;> simp
  have hbound : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      ∀ j, ‖w j * (s ^ (j + 1) - 1) ^ 2‖ ≤ w j := by
    have h0 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ s :=
      hfilter (eventually_ge_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hs1 j
    have hsle : s ≤ 1 := hs1.le
    have hpow0 : 0 ≤ s ^ (j + 1) := pow_nonneg hs0 _
    have hpow1 : s ^ (j + 1) ≤ 1 := by
      simpa using (pow_le_pow_left₀ hs0 hsle (j + 1))
    have hsq : (s ^ (j + 1) - 1) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (s ^ (j + 1))]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw j) (sq_nonneg _))]
    exact mul_le_of_le_one_right (hw j) hsq
  have h := tendsto_tsum_of_dominated_convergence hsum hterm hbound
  simpa [w] using h

/-- The regularized complex area integrals themselves tend to the actual
inverse coefficient. Identifying their limit with the unregularized integral
is a separate analytic step. -/
theorem regularHarmonic_first_integral_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto
      (fun s : ℝ => (Real.pi : ℂ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          regularHarmonic s F z ^ (n - 1) *
            deriv (regularForwardGerm s F) (conj z) ∂volume))
      (𝓝[<] (1 : ℝ)) (𝓝 (exteriorInverseCoeff F n)) := by
  have hpos : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hbelow : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 :=
    self_mem_nhdsWithin
  have heq : (fun s : ℝ => (Real.pi : ℂ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          regularHarmonic s F z ^ (n - 1) *
            deriv (regularForwardGerm s F) (conj z) ∂volume)) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun s : ℝ => (s : ℂ) ^ (n + 1) * exteriorInverseCoeff F n) := by
    filter_upwards [hpos, hbelow] with s hs0 hs1
    exact (regularHarmonic_first_identity F hc hs0 hs1 hn).symm.trans
      (rescaleExterior_inverseCoeff F hc hs0 hs1 hn)
  have hs : Tendsto (fun s : ℝ => (s : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun s : ℝ => s) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ))))
  have hlim := (hs.pow (n + 1)).mul
    (tendsto_const_nhds (x := exteriorInverseCoeff F n))
  have hlim' := hlim.congr' heq.symm
  simpa only [one_pow, one_mul] using hlim'

end SpringerLean
