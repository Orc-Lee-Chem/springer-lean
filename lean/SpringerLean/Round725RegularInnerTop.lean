import SpringerLean.Round724ActualAngularRectangle

open MeasureTheory Set Filter
open scoped Topology

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Three honest limits remove the rectangle errors: the left edge goes
to minus infinity, the horizontal edges go to0 and pi, and the right edge
approaches0 from the left.  No boundary extension of a general F is used. -/
theorem regularExterior_logarithmicActualTopValue_le_majorant
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (c z : ℂ) (hcn : ‖c‖ = 1)
    (hx : z.re < 0) (hh0 : 0 < z.im) (hhpi : z.im < Real.pi) :
    logarithmicActualTopValue (rescaleExterior s F) c z ≤ angularSineMajorant c z := by
  obtain ⟨L, hL0, hrect⟩ := regularExterior_logarithmicTop_le_majorant_add_rectangle_error
    F hc hs0 hs1
  let S := logarithmicActualTopValue (rescaleExterior s F) c z
  let M := angularSineMajorant c z
  let C : ℝ := 4+2*Real.pi*L
  have hfirst (b d : ℝ) (hxb : z.re ≤ b) (hb : b < 0)
      (hd : 0 < d) (hdh : d < z.im) (hdpi : d < Real.pi-z.im) :
      S ≤ M+(4*d+(1-Real.exp b)*C) := by
    have hlim : Tendsto
        (fun a : ℝ => M+(4*Real.pi*Real.exp a+4*d+(1-Real.exp b)*C)) atBot
        (𝓝 (M+(4*d+(1-Real.exp b)*C))) := by
      have he : Tendsto (fun a : ℝ => 4*Real.pi*Real.exp a) atBot (𝓝 0) := by
        have hc : Tendsto (fun _ : ℝ => 4*Real.pi) atBot (𝓝 (4*Real.pi)) := tendsto_const_nhds
        simpa using hc.mul Real.tendsto_exp_atBot
      have hm : Tendsto (fun _ : ℝ => M) atBot (𝓝 M) := tendsto_const_nhds
      have hdconst : Tendsto (fun _ : ℝ => 4*d) atBot (𝓝 (4*d)) := tendsto_const_nhds
      have hbconst : Tendsto (fun _ : ℝ => (1-Real.exp b)*C) atBot
          (𝓝 ((1-Real.exp b)*C)) := tendsto_const_nhds
      simpa only [zero_add] using hm.add ((he.add hdconst).add hbconst)
    apply ge_of_tendsto hlim
    filter_upwards [eventually_le_atBot z.re] with a ha
    have hz : z ∈ complexClosedRectangle a b d (Real.pi-d) :=
      ⟨⟨ha, hxb⟩, hdh.le, by linarith⟩
    exact hrect c hcn a b d (ha.trans hxb) hb hd (by linarith) z hz
  have hsecond (b : ℝ) (hxb : z.re ≤ b) (hb : b < 0) :
      S ≤ M+(1-Real.exp b)*C := by
    have hlim : Tendsto (fun d : ℝ => M+(4*d+(1-Real.exp b)*C))
        (𝓝[>] (0 : ℝ)) (𝓝 (M+(1-Real.exp b)*C)) := by
      have hcont : ContinuousAt (fun d : ℝ => M+(4*d+(1-Real.exp b)*C)) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlim
    have hpos : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), 0 < d := self_mem_nhdsWithin
    have hsmall : Iio (min z.im (Real.pi-z.im)) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min hh0 (sub_pos.mpr hhpi)))
    filter_upwards [hpos, hsmall] with d hd hdsmall
    exact hfirst b d hxb hb hd
      (hdsmall.trans_le (min_le_left _ _)) (hdsmall.trans_le (min_le_right _ _))
  have hlim : Tendsto (fun b : ℝ => M+(1-Real.exp b)*C)
      (𝓝[<] (0 : ℝ)) (𝓝 M) := by
    have hcont : ContinuousAt (fun b : ℝ => M+(1-Real.exp b)*C) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  have hneg : ∀ᶠ b : ℝ in 𝓝[<] (0 : ℝ), b < 0 := self_mem_nhdsWithin
  have hlarge : Ioi z.re ∈ 𝓝[<] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx)
  filter_upwards [hneg, hlarge] with b hb hxb
  exact hsecond b hxb.le hb

/-- Sharp arbitrary-set top integral on EVERY inner circle for the actual
regularized map.  Raw angular mass is2h, hence the right side is4r sin h.
Transfer from regularized maps to an arbitrary F is a separate step. -/
theorem regularExterior_actualAngularTopValue_le_sine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (c : ℂ) (hcn : ‖c‖ = 1) {r h : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hh0 : 0 < h) (hhpi : h < Real.pi) :
    actualAngularTopValue (rescaleExterior s F) c r h ≤ 4*r*Real.sin h := by
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  by_cases hr : r = 0
  · have hv := (le_abs_self (actualAngularTopValue (rescaleExterior s F) c r h)).trans
      (actualAngularTopValue_abs_le (rescaleExterior s F) hcG c hr0 hr1 hh0 hhpi)
    simpa only [hr, mul_zero, zero_mul] using hv
  · have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    let z : ℂ := (Real.log r : ℂ)+(h : ℂ)*Complex.I
    have hzx : z.re < 0 := by simpa [z] using Real.log_neg hrp hr1
    have hzh0 : 0 < z.im := by simpa [z] using hh0
    have hzhpi : z.im < Real.pi := by simpa [z] using hhpi
    have hv := regularExterior_logarithmicActualTopValue_le_majorant
      F hc hs0 hs1 c z hcn hzx hzh0 hzhpi
    rw [angularSineMajorant_coordinates] at hv
    simpa [logarithmicActualTopValue, z, Real.exp_log hrp, hcn] using hv

end SpringerLean

#print axioms SpringerLean.regularExterior_logarithmicActualTopValue_le_majorant
#print axioms SpringerLean.regularExterior_actualAngularTopValue_le_sine
