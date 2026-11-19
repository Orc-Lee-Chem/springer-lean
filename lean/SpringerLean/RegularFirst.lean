import SpringerLean.RegularResidue

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean

/-- Differentiating the finite binomial theorem in its analytic variable.
This identity is independent of integration and works at any differentiability point. -/
theorem harmonic_binomial_deriv
    (g : ℂ → ℂ) (n : ℕ) (z u : ℂ)
    (hg : DifferentiableAt ℂ g u) :
    (n : ℂ) * (z + g u) ^ (n - 1) * deriv g u =
      ∑ p ∈ Finset.range n,
        (n.choose p : ℂ) * z ^ p *
          deriv (fun v => (g v) ^ (n - p)) u := by
  have hdiff : DifferentiableAt ℂ (fun v : ℂ => z + g v) u :=
    hg.const_add z
  have hleft : deriv (fun v : ℂ => (z + g v) ^ n) u =
      (n : ℂ) * (z + g u) ^ (n - 1) * deriv g u := by
    have hpow := deriv_pow hdiff n
    have hfunpow : ((fun v : ℂ => z + g v) ^ n) =
        (fun v : ℂ => (z + g v) ^ n) := by
      funext v
      simp
    rw [hfunpow, deriv_const_add] at hpow
    exact hpow
  have hfun : (fun v : ℂ => (z + g v) ^ n) =
      (fun v : ℂ => ∑ p ∈ Finset.range (n + 1),
        z ^ p * (g v) ^ (n - p) * (n.choose p : ℂ)) := by
    funext v
    exact add_pow z (g v) n
  have hterm (p : ℕ) :
      deriv (fun v : ℂ => z ^ p * (g v) ^ (n - p) * (n.choose p : ℂ)) u =
        (n.choose p : ℂ) * z ^ p *
          deriv (fun v : ℂ => (g v) ^ (n - p)) u := by
    rw [deriv_mul_const_field, deriv_const_mul_field]
    ring
  have hsum : deriv (fun v : ℂ => ∑ p ∈ Finset.range (n + 1),
        z ^ p * (g v) ^ (n - p) * (n.choose p : ℂ)) u =
      ∑ p ∈ Finset.range (n + 1),
        (n.choose p : ℂ) * z ^ p *
          deriv (fun v : ℂ => (g v) ^ (n - p)) u := by
    rw [deriv_fun_sum]
    · apply Finset.sum_congr rfl
      intro p hp
      exact hterm p
    · intro p hp
      exact ((hg.pow _).const_mul _).mul_const _
  calc
    (n : ℂ) * (z + g u) ^ (n - 1) * deriv g u =
        deriv (fun v : ℂ => (z + g v) ^ n) u := hleft.symm
    _ = deriv (fun v : ℂ => ∑ p ∈ Finset.range (n + 1),
          z ^ p * (g v) ^ (n - p) * (n.choose p : ℂ)) u := by rw [hfun]
    _ = ∑ p ∈ Finset.range (n + 1),
          (n.choose p : ℂ) * z ^ p *
            deriv (fun v : ℂ => (g v) ^ (n - p)) u := hsum
    _ = ∑ p ∈ Finset.range n,
          (n.choose p : ℂ) * z ^ p *
            deriv (fun v : ℂ => (g v) ^ (n - p)) u := by
          rw [Finset.sum_range_succ]
          simp [deriv_const]

/-- The first complex area identity of Lemma 3.1 for every regular dilate.
The inverse coefficient is the derivative-defined coefficient of the actual
inverse branch of the same rescaled exterior map. -/
theorem rescaleExterior_inverseCoeff_eq_diskIntegral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    exteriorInverseCoeff (rescaleExterior s F) n =
      (Real.pi : ℂ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          (z + exteriorForwardGerm (rescaleExterior s F) (conj z)) ^ (n - 1) *
            deriv (exteriorForwardGerm (rescaleExterior s F)) (conj z) ∂volume) := by
  let G := rescaleExterior s F
  let g := exteriorForwardGerm G
  let D : Set ℂ := Metric.ball 0 1
  have hclass : CenteredExteriorUnivalent G :=
    rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have hR : 1 < s⁻¹ := by
    exact (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hga : AnalyticOnNhd ℂ g (Metric.ball 0 s⁻¹) := by
    have h := regularForwardGerm_analyticOnNhd F hc hs0
    rw [regularForwardGerm_eq_actual s hs0 F] at h
    exact h
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hconj : Continuous (fun z : ℂ => conj z) := by fun_prop
  have hconjMaps : Set.MapsTo (fun z : ℂ => conj z)
      (Metric.closedBall (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right, ← Complex.star_def,
      norm_star] using hz
  have hzc (z : ℂ) (hz : z ∈ D) : conj z ∈ Metric.ball (0 : ℂ) s⁻¹ := by
    have hzlt : ‖z‖ < 1 := by
      simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    have hnorm : ‖conj z‖ = ‖z‖ := by
      simpa only [← Complex.star_def] using norm_star z
    have hsbound : ‖z‖ < s⁻¹ := lt_trans hzlt hR
    simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hsbound
  have hdiff (z : ℂ) (hz : z ∈ D) : DifferentiableAt ℂ g (conj z) :=
    (hga (conj z) (hzc z hz)).differentiableAt
  have hpoint (z : ℂ) (hz : z ∈ D) :
      (n : ℂ) * ((z + g (conj z)) ^ (n - 1) * deriv g (conj z)) =
        ∑ p ∈ Finset.range n,
          (n.choose p : ℂ) *
            (z ^ p * deriv (fun u => (g u) ^ (n - p)) (conj z)) := by
    calc
      (n : ℂ) * ((z + g (conj z)) ^ (n - 1) * deriv g (conj z)) =
          (n : ℂ) * (z + g (conj z)) ^ (n - 1) * deriv g (conj z) := by ring
      _ = ∑ p ∈ Finset.range n,
          (n.choose p : ℂ) * z ^ p *
            deriv (fun u => (g u) ^ (n - p)) (conj z) :=
        harmonic_binomial_deriv g n z (conj z) (hdiff z hz)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hint (p : ℕ) : IntegrableOn
      (fun z : ℂ => (n.choose p : ℂ) *
        (z ^ p * deriv (fun u => (g u) ^ (n - p)) (conj z))) D := by
    have hp : AnalyticOnNhd ℂ (fun u => (g u) ^ (n - p))
        (Metric.ball 0 s⁻¹) := hga.pow _
    have hder : ContinuousOn (deriv (fun u => (g u) ^ (n - p)))
        (Metric.closedBall (0 : ℂ) 1) :=
      hp.deriv.continuousOn.mono (Metric.closedBall_subset_ball hR)
    have hcont : ContinuousOn
        (fun z : ℂ => (n.choose p : ℂ) *
          (z ^ p * deriv (fun u => (g u) ^ (n - p)) (conj z)))
        (Metric.closedBall (0 : ℂ) 1) := by
      exact continuousOn_const.mul
        ((continuousOn_id.pow p).mul
          (hder.comp hconj.continuousOn hconjMaps))
    exact (hcont.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  have hpowAnalytic (p : ℕ) :
      AnalyticOnNhd ℂ (fun u => (g u) ^ (n - p))
        (Metric.ball 0 s⁻¹) := hga.pow _
  have hsum : (Real.pi : ℂ)⁻¹ *
      (∫ z in D,
        ∑ p ∈ Finset.range n,
          (n.choose p : ℂ) *
            (z ^ p * deriv (fun u => (g u) ^ (n - p)) (conj z)) ∂volume) =
      ∑ p ∈ Finset.range n, (n.choose p : ℂ) *
        actualTaylorCoeff (fun u => (g u) ^ (n - p)) (p + 1) := by
    rw [integral_finsetSum (Finset.range n) (fun p hp => hint p), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [integral_const_mul]
    calc
      (Real.pi : ℂ)⁻¹ * ((n.choose p : ℂ) *
        (∫ z in D, z ^ p * deriv (fun u => (g u) ^ (n - p)) (conj z) ∂volume)) =
          (n.choose p : ℂ) *
            ((Real.pi : ℂ)⁻¹ *
              (∫ z in D, z ^ p * deriv (fun u => (g u) ^ (n - p)) (conj z) ∂volume)) := by ring
      _ = _ := by
        rw [show D = Metric.ball (0 : ℂ) 1 by rfl,
          analytic_deriv_disk_moment _ hR (hpowAnalytic p) p]
  have hres := rescaleExterior_residue_binomial_actual F hc hs0 hs1 n
  have hmain : (n : ℂ) *
      ((Real.pi : ℂ)⁻¹ *
        (∫ z in D, (z + g (conj z)) ^ (n - 1) * deriv g (conj z) ∂volume)) =
      exteriorFormalResidue G n := by
    calc
      _ = (Real.pi : ℂ)⁻¹ *
          (∫ z in D, (n : ℂ) *
            ((z + g (conj z)) ^ (n - 1) * deriv g (conj z)) ∂volume) := by
              rw [integral_const_mul]
              ring
      _ = (Real.pi : ℂ)⁻¹ *
          (∫ z in D,
            ∑ p ∈ Finset.range n,
              (n.choose p : ℂ) *
                (z ^ p * deriv (fun u => (g u) ^ (n - p)) (conj z)) ∂volume) := by
              congr 1
              apply setIntegral_congr_fun hD
              intro z hz
              exact hpoint z hz
      _ = ∑ p ∈ Finset.range n, (n.choose p : ℂ) *
            actualTaylorCoeff (fun u => (g u) ^ (n - p)) (p + 1) := hsum
      _ = exteriorFormalResidue G n := by
          simpa only [G, g] using hres.symm
  have hcoef := exteriorInverseCoeff_mul_eq_formalResidue G hclass n hn
  rw [← hcoef] at hmain
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hresult := mul_left_cancel₀ hn0 hmain
  simpa [G, g, D] using hresult.symm

/-- The same identity in the manuscript's explicit notation
`g_s(u)=s g(su)`, `H_s(z)=z+g_s(conj z)`. -/
theorem regularHarmonic_first_identity
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    exteriorInverseCoeff (rescaleExterior s F) n =
      (Real.pi : ℂ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          regularHarmonic s F z ^ (n - 1) *
            deriv (regularForwardGerm s F) (conj z) ∂volume) := by
  simpa only [regularHarmonic, regularForwardGerm_eq_actual s hs0 F] using
    rescaleExterior_inverseCoeff_eq_diskIntegral F hc hs0 hs1 hn

/-- The original odd-order form of the first complex area identity. -/
theorem regularHarmonic_odd_first_identity
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {k : ℕ} (hk : 1 ≤ k) :
    exteriorInverseCoeff (rescaleExterior s F) (2 * k - 1) =
      (Real.pi : ℂ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          regularHarmonic s F z ^ (2 * k - 2) *
            deriv (regularForwardGerm s F) (conj z) ∂volume) := by
  have hn : 1 ≤ 2 * k - 1 := by omega
  simpa only [show (2 * k - 1) - 1 = 2 * k - 2 by omega] using
    (regularHarmonic_first_identity F hc hs0 hs1 (n := 2 * k - 1) hn)

/-- The order-one integral has the expected actual forward coefficient. -/
theorem regularHarmonic_first_identity_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (Real.pi : ℂ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        deriv (regularForwardGerm s F) (conj z) ∂volume) =
      (s : ℂ) ^ 2 * exteriorForwardCoeff F 1 := by
  have h := regularHarmonic_first_identity F hc hs0 hs1 (n := 1) (by omega)
  simp only [Nat.sub_self, pow_zero, one_mul] at h
  rw [exteriorInverseCoeff_one_eq_forwardCoeff_one
      (rescaleExterior s F)
      (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1),
    rescaleExterior_forwardCoeff F hc hs0 1] at h
  simpa using h.symm

/-- The order-three integral checks the sign and indexing against
`B₃=b₃+b₁²` for the same actual dilate. -/
theorem regularHarmonic_first_identity_three
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (Real.pi : ℂ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        regularHarmonic s F z ^ 2 *
          deriv (regularForwardGerm s F) (conj z) ∂volume) =
      exteriorForwardCoeff (rescaleExterior s F) 3 +
        (exteriorForwardCoeff (rescaleExterior s F) 1) ^ 2 := by
  have h := regularHarmonic_first_identity F hc hs0 hs1 (n := 3) (by omega)
  rw [exteriorInverseCoeff_three_eq_forward
    (rescaleExterior s F)
    (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)] at h
  simpa using h.symm


end SpringerLean
