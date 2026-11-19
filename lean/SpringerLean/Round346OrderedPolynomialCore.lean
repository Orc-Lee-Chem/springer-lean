import SpringerLean.Round345CertificateListBody

namespace SpringerLean.RatPolyCheck.Ordered

def lexLE {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) : List σ → List σ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then lexLE r as bs else r a b

def monomialLE {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) (a b : List σ) : Bool :=
  if a.length < b.length then true else if b.length < a.length then false else lexLE r a b

/-- Structurally recursive merge. The fallback retains all terms, so
soundness does not require ordering or a sufficient-fuel premise. -/
def addFuel {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) :
    Nat → Sparse σ → Sparse σ → Sparse σ
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, p, [] => p
  | n + 1, (m,c) :: p, (l,d) :: q =>
      if m = l then
        if c + d = 0 then addFuel r n p q else (m,c+d) :: addFuel r n p q
      else if monomialLE r m l then
        (m,c) :: addFuel r n p ((l,d) :: q)
      else (l,d) :: addFuel r n ((m,c) :: p) q

def add {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) (p q : Sparse σ) : Sparse σ :=
  addFuel r (p.length + q.length) p q

def mul {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) : Sparse σ → Sparse σ → Sparse σ
  | [], _ => []
  | t :: p, q => add r (q.map (Structural.mulTerm r t)) (mul r p q)

def normalize {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) : Expr σ → Sparse σ
  | .const q => if q = 0 then [] else [([], q)]
  | .var i => [([i], 1)]
  | .add e f => add r (normalize r e) (normalize r f)
  | .mul e f => mul r (normalize r e) (normalize r f)

def check {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) (e f : Expr σ) : Bool :=
  (normalize r (.add e (.mul (.const (-1)) f))).isEmpty

end SpringerLean.RatPolyCheck.Ordered

namespace SpringerLean
open RatPolyCheck
def RationalGramCertificate.orderedCheck (c : RationalGramCertificate)
    (k : Nat) (C η : Rat) : Bool :=
  c.weightsCheck && Ordered.check coeffExprVariableOrder
    (fastGramTargetExpr k C η) c.listBody
end SpringerLean
