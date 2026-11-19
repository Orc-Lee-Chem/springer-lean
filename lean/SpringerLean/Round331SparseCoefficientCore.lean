import SpringerLean.Round321CertificateCore

namespace SpringerLean.RatPolyCheck

def sparseSum {σ : Type _} [DecidableEq σ] (f : Nat → Sparse σ) : Nat → Sparse σ
  | 0 => []
  | n + 1 => add (sparseSum f n) (f n)

def sparseCauchyCoeff {σ : Type _} [DecidableEq σ]
    (r : σ → σ → Bool) (A B : List (Sparse σ)) (n : Nat) : Sparse σ :=
  sparseSum (fun i => Structural.mul r (A.getD i []) (B.getD (n - i) [])) (n + 1)

def sparseSeriesMul {σ : Type _} [DecidableEq σ]
    (r : σ → σ → Bool) (A B : List (Sparse σ)) (N : Nat) : List (Sparse σ) :=
  (List.range (N + 1)).map (fun n => sparseCauchyCoeff r A B n)

def sparseSeriesOne {σ : Type _} (N : Nat) : List (Sparse σ) :=
  (List.range (N + 1)).map (fun n => if n = 0 then [([], 1)] else [])

/-- A finite coefficient table. Each Cauchy product combines equal
monomials before the next multiplication; constant terms do not create
an exponentially expanded expression tree. -/
def sparseSeriesPow {σ : Type _} [DecidableEq σ]
    (r : σ → σ → Bool) (f : List (Sparse σ)) (N : Nat) : Nat → List (Sparse σ)
  | 0 => sparseSeriesOne N
  | k + 1 => sparseSeriesMul r (sparseSeriesPow r f N k) f N

def variableProductExpr {σ : Type _} : List σ → Expr σ
  | [] => .const 1
  | a :: as => .mul (.var a) (variableProductExpr as)

def sparseToExpr {σ : Type _} : Sparse σ → Expr σ
  | [] => .const 0
  | (m, q) :: ps => Expr.smartAdd (.mul (.const q) (variableProductExpr m)) (sparseToExpr ps)

end SpringerLean.RatPolyCheck

namespace SpringerLean
open RatPolyCheck

def phiSparseCoefficients (N : Nat) : List (Sparse (Bool × Nat)) :=
  (List.range (N + 1)).map (fun n =>
    if n = 0 then [([], 1)] else if n = 1 then [] else [([(false, n - 1)], 1)])

def fastPhiPowerCoefficients (k N : Nat) : List (Sparse (Bool × Nat)) :=
  sparseSeriesPow coeffExprVariableOrder (phiSparseCoefficients N) N k

def fastSchoberDiagonalExpr (k : Nat) : CoeffExpr :=
  let table := fastPhiPowerCoefficients k (k - 1)
  Expr.fsum (fun j => .mul (.const ((((j + 1 : Nat) : Rat) / (k : Rat)) ^ 2))
    (CoeffExpr.normSq (sparseToExpr (table.getD (k - 1 - j) [])))) k

def fastGramTargetExpr (k : Nat) (C η : Rat) : CoeffExpr :=
  Expr.sub (Expr.sub (.const 1) (Expr.scale C⁻¹ (fastSchoberDiagonalExpr k)))
    (Expr.scale η (Expr.sub (.const 1) (CoeffExpr.normSq (.var (false, 1)))))

def RationalGramCertificate.fastTargetCheck (c : RationalGramCertificate)
    (k : Nat) (C η : Rat) : Bool :=
  c.weightsCheck && RatPolyCheck.Structural.check coeffExprVariableOrder
    (fastGramTargetExpr k C η) c.body

end SpringerLean
