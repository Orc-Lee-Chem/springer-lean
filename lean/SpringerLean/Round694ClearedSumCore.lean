import SpringerLean.Round557FastPolynomialCore

namespace SpringerLean.RatPolyCheck.ClearedSum

/-- A proposed positive common denominator. Divisibility is checked in
the kernel, rather than trusting its externally generated value. -/
def denominatorsDivide {σ : Type _} (D : Nat) (p : Sparse σ) : Bool :=
  p.all (fun t => decide (t.2.den ∣ D))

def clearCoeff (D : Nat) (q : Rat) : Rat :=
  ((q.num * ((D/q.den : Nat) : Int) : Int) : Rat)

/-- Integer coefficients, provided denominatorsDivide succeeds. -/
def clear {σ : Type _} (D : Nat) (p : Sparse σ) : Sparse σ :=
  p.map (fun t => (t.1, clearCoeff D t.2))

def difference {σ : Type _} (r : σ → σ → Bool) (D : Nat)
    (p l q : Sparse σ) : Sparse σ :=
  clear D p ++ Fast.rawMul r [([], -1)] (clear D l ++ clear D q)

def reduced {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) (D : Nat)
    (p l q : Sparse σ) : Sparse σ :=
  let s := difference r D p l q
  (Fast.sortFuel r s.length s).filter (fun t => t.2 != 0)

def checkSparse {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) (D : Nat)
    (p l q : Sparse σ) : Bool :=
  decide (0 < D) && (denominatorsDivide D p &&
    (denominatorsDivide D l && (denominatorsDivide D q &&
      (reduced r D p l q).isEmpty)))

def checkAdd {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) (D : Nat)
    (e l q : Expr σ) : Bool :=
  checkSparse r D (Fast.expand r e) (Fast.expand r l) (Fast.expand r q)

end SpringerLean.RatPolyCheck.ClearedSum
