import SpringerLean.Round557FastPolynomialCore

namespace SpringerLean.RatPolyCheck.Hybrid

/-- Flatten additions, but normalize factors before multiplying them.
The supplied factor normalizer is a computational parameter only. -/
def expandWith {σ : Type _} (r : σ → σ → Bool)
    (nf : Expr σ → Sparse σ) : Expr σ → Sparse σ → Sparse σ
  | .const q,p => ([],q)::p
  | .var i,p => ([i],1)::p
  | .add e f,p => expandWith r nf e (expandWith r nf f p)
  | .mul e f,p => Fast.rawMul r (nf e) (nf f) ++ p

def finish {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool)
    (p : Sparse σ) : Sparse σ :=
  (Fast.sortFuel r p.length p).filter (fun t => t.2 != 0)

/-- Structural fuel controls normalization at products. The zero-fuel
fallback is the existing sound checker; every fuel value is sound. -/
def normalize {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) :
    Nat → Expr σ → Sparse σ
  | 0,e => Fast.normalize r e
  | n+1,e => finish r (expandWith r (normalize r n) e [])

def check {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool)
    (n : Nat) (e f : Expr σ) : Bool :=
  (normalize r n (.add e (.mul (.const (-1)) f))).isEmpty

end SpringerLean.RatPolyCheck.Hybrid
