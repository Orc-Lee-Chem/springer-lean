import SpringerLean.Round2039EvenBLPConvexOnSupport
import Mathlib.Analysis.Convex.Piecewise

namespace SpringerLean

noncomputable def evenStarBLPTangentExtension (k : ℕ) (x : ℝ) : ℝ :=
  if x ≤ Real.log 2 then evenStarBLPCorrectedLog k x else
    evenStarBLPCorrectedLog k (Real.log 2) +
      deriv (evenStarBLPCorrectedLog k) (Real.log 2) * (x-Real.log 2)

private theorem linear_convexOn (s : ℝ) (D : Set ℝ)
    (hD : Convex ℝ D) :
    ConvexOn ℝ D (fun x : ℝ => s*x) := by
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  dsimp
  apply le_of_eq
  ring

private theorem evenStarBLP_shifted_antitone
    (k : ℕ) (hk : 0 < k) :
    let f := evenStarBLPCorrectedLog k
    let a := Real.log 2
    let s := deriv f a
    AntitoneOn (fun x => f x-s*x) (Set.Iic a) := by
  let f := evenStarBLPCorrectedLog k
  let a := Real.log 2
  let s := deriv f a
  let h : ℝ → ℝ := fun x => f x-s*x
  have hconv := evenStarBLPCorrectedLog_convexOn_support k hk
  have hfd : ∀ x ∈ Set.Iic a, DifferentiableAt ℝ f x := by
    intro x hx
    exact (evenStarBLPCorrectedLog_hasDerivAt k hk x).differentiableAt
  have hmono : MonotoneOn (deriv f) (Set.Iic a) :=
    hconv.monotoneOn_deriv hfd
  have hhder (x : ℝ) : HasDerivAt h (deriv f x-s) x := by
    have hlinear : HasDerivAt (fun t : ℝ => s*t) s x := by
      convert (hasDerivAt_const x s).mul (hasDerivAt_id x) using 1
      · ext t; rfl
      · simp
    have hfx := evenStarBLPCorrectedLog_hasDerivAt k hk x
    convert hfx.sub hlinear using 1
    rw [hfx.deriv]
  have hhcont : ContinuousOn h (Set.Iic a) := by
    intro x hx
    exact (hhder x).continuousAt.continuousWithinAt
  have hhdiff : DifferentiableOn ℝ h (interior (Set.Iic a)) := by
    intro x hx
    exact (hhder x).differentiableAt.differentiableWithinAt
  have hneg : ∀ x ∈ interior (Set.Iic a), deriv h x ≤ 0 := by
    intro x hx
    have hxle : x ∈ Set.Iic a := interior_subset hx
    have hdx : deriv f x ≤ s :=
      hmono hxle (Set.self_mem_Iic) hxle
    rw [(hhder x).deriv]
    linarith
  exact antitoneOn_of_deriv_nonpos (convex_Iic a)
    hhcont hhdiff hneg

theorem evenStarBLPTangentExtension_convex
    (k : ℕ) (hk : 0 < k) :
    ConvexOn ℝ Set.univ (evenStarBLPTangentExtension k) := by
  let f := evenStarBLPCorrectedLog k
  let a := Real.log 2
  let s := deriv f a
  let h : ℝ → ℝ := fun x => f x-s*x
  let c : ℝ := f a-s*a
  have hconv : ConvexOn ℝ (Set.Iic a) f :=
    evenStarBLPCorrectedLog_convexOn_support k hk
  have hshift : ConvexOn ℝ (Set.Iic a) h := by
    have hlin : ConvexOn ℝ (Set.Iic a) (fun x : ℝ => -s*x) :=
      linear_convexOn (-s) _ (convex_Iic _)
    have hsum := hconv.add hlin
    convert hsum using 1
    ext x
    simp [h, Pi.add_apply]
    ring
  have hcconv : ConvexOn ℝ (Set.Ici a) (fun _ : ℝ => c) :=
    convexOn_const c (convex_Ici a)
  have hcmono : MonotoneOn (fun _ : ℝ => c) (Set.Ici a) := by
    intro x hx y hy hxy
    rfl
  have hanti : AntitoneOn h (Set.Iic a) :=
    evenStarBLP_shifted_antitone k hk
  have hboundary : h a=c := rfl
  have hpiece : ConvexOn ℝ Set.univ
      ((Set.Iic a).piecewise h (fun _ => c)) :=
    convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
      hshift hcconv hanti hcmono hboundary
  have hlin : ConvexOn ℝ Set.univ (fun x : ℝ => s*x) :=
    linear_convexOn s _ convex_univ
  have hsum := hpiece.add hlin
  convert hsum using 1
  funext x
  by_cases hx : x ≤ a
  · simp [evenStarBLPTangentExtension, Set.piecewise, hx, h, f, a]
  · simp [evenStarBLPTangentExtension, Set.piecewise, hx, h, c, f, a]
    ring

end SpringerLean
