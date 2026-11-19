import SpringerLean.Round1574WeightedFillingDerivative

namespace SpringerLean
set_option maxHeartbeats 2000000

/-- Exact integer data printed in the paper's energy multiplier table.
The first field is the abscissa in units of 1/60; the remaining fields
are the values of chi, f, sigma in units of 1/1,000,000. -/
structure EnergyMultiplierNode where
  i : ℤ
  chi : ℤ
  f : ℤ
  sigma : ℤ
deriving DecidableEq, Repr

def energyMultiplierNode (j : ℕ) : EnergyMultiplierNode :=
  match j with
  | 0 => ⟨0,0,0,0⟩
  | 1 => ⟨1,154782,108880,154782⟩
  | 2 => ⟨2,296418,204283,296418⟩
  | 3 => ⟨3,426093,288087,426093⟩
  | 4 => ⟨4,546465,362857,546465⟩
  | 5 => ⟨5,656924,428908,656924⟩
  | 6 => ⟨6,761604,436711,656924⟩
  | 7 => ⟨7,848869,442103,656924⟩
  | 8 => ⟨8,922115,445633,656924⟩
  | 9 => ⟨9,984120,447686,656924⟩
  | 10 => ⟨10,1043512,448757,656924⟩
  | 11 => ⟨11,1103045,448991,656924⟩
  | 12 => ⟨13,1222097,447033,656924⟩
  | 13 => ⟨15,1340424,442030,656924⟩
  | 14 => ⟨17,1456370,434305,656924⟩
  | 15 => ⟨19,1565487,424567,656924⟩
  | 16 => ⟨21,1663241,413819,656924⟩
  | 17 => ⟨23,1753104,402252,656924⟩
  | 18 => ⟨26,1875468,383902,656924⟩
  | 19 => ⟨29,1982241,365443,656924⟩
  | 20 => ⟨38,2227072,314435,656924⟩
  | 21 => ⟨60,2573054,220609,656924⟩
  | _ => ⟨0,0,0,0⟩

/-- A piecewise-affine slope in the paper's physical coordinates. -/
def energyMultiplierSlope (x y : ℤ) (i j : ℤ) : ℚ :=
  ((y-x:ℤ):ℚ)*60/(((j-i:ℤ):ℚ)*1000000)

/-- The three uniform endpoint coefficients A, D, B at k=751.
The max in B covers both extrema of the k-dependent middle term. -/
def energyMultiplierEndpointCoeffs (caseNo : ℕ) : ℚ × ℚ × ℚ := Id.run do
  let cell := if caseNo = 42 then 21 else caseNo/2
  let endpoint := if caseNo = 42 then 21 else cell+caseNo%2
  let u := energyMultiplierNode cell
  let w := energyMultiplierNode (cell+1)
  let v := energyMultiplierNode endpoint
  let t : ℚ := v.i/60
  let chi : ℚ := v.chi/1000000
  let f : ℚ := v.f/1000000
  let sigma : ℚ := v.sigma/1000000
  let cp : ℚ := if cell = 21 then 0 else
    energyMultiplierSlope u.chi w.chi u.i w.i
  let fp : ℚ := if cell = 21 then 0 else
    energyMultiplierSlope u.f w.f u.i w.i
  let sp : ℚ := if cell = 21 then 0 else
    energyMultiplierSlope u.sigma w.sigma u.i w.i
  let h : ℚ := f+t*fp
  let A : ℚ := chi+fp-|sp|/2-
    (2*max 0 f+2*|h|+t*|sp|+sigma)/751
  let D : ℚ := (751*chi+t*|cp|)/(4*750)
  let mixed : ℚ := max |2*f-cp/4| |2*f-(751/(4*750):ℚ)*cp|
  let B : ℚ := |chi-sigma|+mixed+t*|cp|/(2*750)+
    (|h|+t*|sp|/2+sigma)/751
  return (A,D,B)

def energyMultiplierEndpointValid (caseNo : ℕ) : Prop :=
  let (A,D,B) := energyMultiplierEndpointCoeffs caseNo
  1 < A ∧ D ≤ (25/16:ℚ) ∧ B^2 ≤ 4*(A-1)*((25/16:ℚ)-D)

/-- The first exact endpoint test checks the data and formula before
the entire finite family is discharged. -/
theorem energyMultiplierEndpoint_case0 : energyMultiplierEndpointValid 0 := by
  norm_num [energyMultiplierEndpointValid,energyMultiplierEndpointCoeffs,
    energyMultiplierNode,energyMultiplierSlope]

/-- Every one of the 43 one-sided endpoint matrices satisfies the same
strict positive-A and completed-square discriminant test. -/
theorem energyMultiplierEndpoint_all43 :
    ∀ j : Fin 43, energyMultiplierEndpointValid j := by
  intro j
  fin_cases j <;>
    norm_num [energyMultiplierEndpointValid,energyMultiplierEndpointCoeffs,
      energyMultiplierNode,energyMultiplierSlope]

end SpringerLean

#print axioms SpringerLean.energyMultiplierEndpoint_case0
#print axioms SpringerLean.energyMultiplierEndpoint_all43
