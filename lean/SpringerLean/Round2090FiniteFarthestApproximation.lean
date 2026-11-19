import SpringerLean.Round2089AveragedFactorEstimate

open MeasureTheory Set Metric
open scoped BigOperators

namespace SpringerLean

/-- A finite net and a sufficiently high power give a uniform scalar
approximation to the farthest-distance logarithm on the entire plane.
The two prescribed distinct points keep every logarithm positive in
its argument, independently of the evaluation point. -/
theorem exists_finiteGaussianLogScale_approximation
    (K : Set ℂ) (hK : IsCompact K)
    (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (B : Fin N → ℂ) (i j : Fin N) (m : ℕ),
      B i ≠ B j ∧ 0 < m ∧
      ∀ z : ℂ,
        (m:ℝ) * (Real.log (continuumFarthestDistance K z)-ε) ≤ finiteGaussianLogScale B m z ∧
        finiteGaussianLogScale B m z ≤ (m:ℝ) * (Real.log (continuumFarthestDistance K z)+ε) := by
  classical
  let c := ‖u-v‖ / 2
  have hc : 0 < c := half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr huv))
  let δ := c*ε
  have hδ : 0 < δ := mul_pos hc hε
  obtain ⟨S,hSK,hfin,hcover⟩ := hK.finite_cover_balls hδ
  let T := insert u (insert v hfin.toFinset)
  let N := T.card
  let e := T.equivFin
  let B (i : Fin N) : ℂ := (e.symm i).1
  have htK : ↑T ⊆ K := by
    intro x hx
    change x ∈ T at hx
    simp only [T, Finset.mem_insert, Set.Finite.mem_toFinset] at hx
    rcases hx with rfl | rfl | hx
    · exact hu
    · exact hv
    · exact hSK hx
  have huT : u ∈ T := by simp [T]
  have hvT : v ∈ T := by simp [T]
  let i := e ⟨u,huT⟩
  let j := e ⟨v,hvT⟩
  have hi : B i = u := by simp [B,i]
  have hj : B j = v := by simp [B,j]
  have hiJ : B i ≠ B j := by rwa [hi,hj]
  have hN : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N from i.isLt.pos)
  obtain ⟨m,hm⟩ := exists_nat_gt ((|Real.log (N:ℝ)|+1)/ε)
  have hmR : 0 < (m:ℝ) := (div_pos (by positivity) hε).trans hm
  have hmul : Real.log (N:ℝ) / 2 ≤ (m:ℝ)*ε := by
    have hh := (div_lt_iff₀ hε).mp hm
    linarith [le_abs_self (Real.log (N:ℝ)), abs_nonneg (Real.log (N:ℝ))]
  refine ⟨N,B,i,j,m,hiJ,by exact_mod_cast hmR,?_⟩
  intro z
  let D := continuumFarthestDistance (↑T : Set ℂ) z
  let d := continuumFarthestDistance K z
  have hT : IsCompact (↑T : Set ℂ) := T.finite_toSet.isCompact
  have hTne : (↑T : Set ℂ).Nonempty := ⟨u,huT⟩
  have hcD : c ≤ D := half_norm_sub_le_continuumFarthestDistance
    (↑T : Set ℂ) hT u v huT hvT z
  have hD0 : 0 < D := hc.trans_le hcD
  obtain ⟨p,hp,hval⟩ := continuumFarthestDistance_eq_distance_at_max _ hT hTne z
  have hDd : D ≤ d := by
    change D = ‖z-p‖ at hval
    rw [hval]
    exact continuumFarthestDistance_ge_distance K hK z p (htK hp)
  have hdD : d ≤ D + δ := by
    obtain ⟨q,hq,hqval⟩ := continuumFarthestDistance_eq_distance_at_max K hK ⟨u,hu⟩ z
    have hqcover := hcover hq
    simp only [mem_iUnion] at hqcover
    obtain ⟨w,hw,hqw⟩ := hqcover
    have hwT : w ∈ T := by simp [T,hw]
    have hwd := continuumFarthestDistance_ge_distance (↑T : Set ℂ) hT z w hwT
    have hqwd : ‖q-w‖ < δ := by simpa [mem_ball,dist_eq_norm] using hqw
    have htriangle := norm_sub_le (z-w) (q-w)
    rw [show (z-w)-(q-w)=z-q by ring] at htriangle
    rw [show d=‖z-q‖ from hqval]
    linarith
  have hloglower : Real.log d - ε ≤ Real.log D := by
    have hd0 := hD0.trans_le hDd
    have hr := Real.log_le_sub_one_of_pos (div_pos hd0 hD0)
    rw [Real.log_div hd0.ne' hD0.ne'] at hr
    have hdiv : d/D ≤ 1+ε := (div_le_iff₀ hD0).mpr (by
      have hδD := mul_le_mul_of_nonneg_right hcD hε.le
      dsimp [δ] at hdD
      nlinarith)
    linarith
  have hlogupper : Real.log D ≤ Real.log d := Real.log_le_log hD0 hDd
  let A := ∑ l : Fin N, ‖(z-B l)^m‖^2
  have hAlo : (D^m)^2 ≤ A := by
    let l := e ⟨p,hp⟩
    have hl : B l = p := by simp [B,l]
    have hbound := Finset.single_le_sum (s := Finset.univ)
      (f := fun k : Fin N => ‖(z-B k)^m‖^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ l)
    rwa [norm_pow,hl,← hval] at hbound
  have hAhi : A ≤ (N:ℝ)*(D^m)^2 := by
    calc
      _ ≤ ∑ l : Fin N, (D^m)^2 := by
        apply Finset.sum_le_sum
        intro l _
        rw [norm_pow]
        have hl : ‖z-B l‖ ≤ D := continuumFarthestDistance_ge_distance _ hT _ _ (e.symm l).2
        gcongr
      _ = _ := by simp
  have hA0 : 0 < A := (pow_pos (pow_pos hD0 m) 2).trans_le hAlo
  have ha := Real.log_le_log (pow_pos (pow_pos hD0 m) 2) hAlo
  have hb := Real.log_le_log hA0 hAhi
  rw [Real.log_pow, Real.log_pow] at ha
  rw [Real.log_mul hN.ne' (pow_ne_zero _ (pow_ne_zero _ hD0.ne')), Real.log_pow, Real.log_pow] at hb
  norm_num at ha hb
  change (m:ℝ)*(Real.log d-ε) ≤ Real.log (Real.sqrt A) ∧
    Real.log (Real.sqrt A) ≤ (m:ℝ)*(Real.log d+ε)
  rw [Real.log_sqrt hA0.le]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hloglower hmR.le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hlogupper hmR.le
    nlinarith

end SpringerLean
