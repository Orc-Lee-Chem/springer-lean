import SpringerLean.Round1449MovingRootAlgebra

namespace SpringerLean
set_option maxHeartbeats 200000

/-- Exact algebraic normalization of the explicit moving-arc saving.
This is an identity, before any numerical weakening or circle-moment
comparison. -/
theorem movingArc_explicit_saving_normalization
    (n : ℕ) (hn : 1501 ≤ n) {W d : ℝ} (hd : 0 < d) :
    let N : ℝ := n
    let t : ℝ := N*d
    let b : ℝ := Real.sqrt (3*d)
    let r : ℝ := Real.sqrt N
    let q : ℝ := Real.sqrt t
    let v : ℝ := refinedAffineV W
    let A : ℝ := v^2*N*((n-1:ℕ):ℝ)*(2:ℝ)^(n-2)
    let B : ℝ := N/2
    let s₀ : ℝ := 2*b^2/5
    (b/Real.pi)*(A*Real.exp (-B*s₀)/2)*
      ((995/1000:ℝ)*4*b^4/45) =
      (Real.sqrt 3/(10*Real.pi))*(995/1000)*
        (1-1/N)*v^2*((2:ℝ)^n/r)*t^2*q*
        Real.exp (-(3/5:ℝ)*t) := by
  dsimp
  let N : ℝ := n
  let t : ℝ := N*d
  let b : ℝ := Real.sqrt (3*d)
  let r : ℝ := Real.sqrt N
  let q : ℝ := Real.sqrt t
  let v : ℝ := refinedAffineV W
  let A : ℝ := v^2*N*((n-1:ℕ):ℝ)*(2:ℝ)^(n-2)
  let B : ℝ := N/2
  let s₀ : ℝ := 2*b^2/5
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (by omega : 0<n)
  have hr : 0 < r := Real.sqrt_pos.2 hN
  have hb2 : b^2=3*d := Real.sq_sqrt (by positivity)
  have hbr : b*r=Real.sqrt 3*q :=
    movingArc_sqrt_factor (by omega : 1≤n) hd.le
  have hnorm := movingArc_root_normalization hN hr hb2 hbr
  have hNat : ((n-1:ℕ):ℝ)=N-1 := by
    dsimp [N]
    rw [Nat.cast_sub (by omega : 1≤n)]
    norm_num
  have hpow : (2:ℝ)^n=4*(2:ℝ)^(n-2) := by
    conv_lhs => rw [show n=n-2+2 by omega, pow_add]
    norm_num
    ring
  have hExp : Real.exp (-B*s₀)=Real.exp (-(3/5:ℝ)*t) := by
    congr 1
    dsimp [B,s₀,t]
    rw [hb2]
    ring
  rw [hExp,hNat]
  calc
    (b/Real.pi)*
        (v^2*N*(N-1)*(2:ℝ)^(n-2)*
          Real.exp (-(3/5:ℝ)*t)/2)*
        ((995/1000:ℝ)*4*b^4/45) =
      ((995/1000:ℝ)/(90*Real.pi))*v^2*
        (4*(2:ℝ)^(n-2))*(b^5*N*(N-1))*
        Real.exp (-(3/5:ℝ)*t) := by ring
    _ = ((995/1000:ℝ)/(90*Real.pi))*v^2*
        ((2:ℝ)^n)*(b^5*N*(N-1))*
        Real.exp (-(3/5:ℝ)*t) := by rw [hpow]
    _ = (Real.sqrt 3/(10*Real.pi))*(995/1000)*
        (1-1/N)*v^2*((2:ℝ)^n/r)*t^2*q*
        Real.exp (-(3/5:ℝ)*t) := by
      rw [hnorm]
      ring

end SpringerLean

#print axioms SpringerLean.movingArc_explicit_saving_normalization
