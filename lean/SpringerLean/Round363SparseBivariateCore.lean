import SpringerLean.Round331SparseCoefficientCore

namespace SpringerLean.RatPolyCheck

def sparseBiTable {σ : Type _} (f : Nat → Nat → Sparse σ) (I J : Nat) :
    List (List (Sparse σ)) :=
  (List.range (I + 1)).map (fun i => (List.range (J + 1)).map (f i))

def sparseBiGet {σ : Type _} (A : List (List (Sparse σ))) (i j : Nat) : Sparse σ :=
  (A.getD i []).getD j []

def sparseBivariatePow {σ : Type _} [DecidableEq σ]
    (r : σ → σ → Bool) (f : Nat → Nat → Sparse σ) (I J : Nat) :
    Nat → List (List (Sparse σ))
  | 0 => sparseBiTable (fun i j => if i = 0 ∧ j = 0 then [([], 1)] else []) I J
  | d + 1 =>
    let previous := sparseBivariatePow r f I J d
    sparseBiTable (fun i j =>
      sparseSum (fun p => sparseSum (fun q =>
        Structural.mul r (sparseBiGet previous q p) (f (i - q) (j - p)))
          (i + 1)) (j + 1)) I J

end SpringerLean.RatPolyCheck

namespace SpringerLean
open RatPolyCheck

def forwardKernelSparse (i j : Nat) : Sparse (Bool × Nat) :=
  if i = 0 ∨ j = 0 then [] else [([(false, i + j - 1)], 1)]

def fastLogGrunskyCoeffExpr (i j : Nat) : CoeffExpr :=
  sparseToExpr (sparseSum (fun d =>
    let table := sparseBivariatePow coeffExprVariableOrder forwardKernelSparse i j d
    (sparseBiGet table i j).map (fun t => (t.1, ((d : Rat)⁻¹) * t.2))) (j + 1))

end SpringerLean
