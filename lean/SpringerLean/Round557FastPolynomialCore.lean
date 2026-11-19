import SpringerLean.Round346OrderedPolynomialCore

/-! A sort-once polynomial checker. These are executable data algorithms only. -/
namespace SpringerLean.RatPolyCheck.Fast

def rawMul {σ : Type _} (r : σ → σ → Bool) (p q : Sparse σ) : Sparse σ :=
  p.flatMap (fun t => q.map (Structural.mulTerm r t))

def expandAcc {σ : Type _} (r : σ → σ → Bool) : Expr σ → Sparse σ → Sparse σ
  | .const q, p => ([], q) :: p
  | .var i, p => ([i], 1) :: p
  | .add e f, p => expandAcc r e (expandAcc r f p)
  | .mul e f, p => rawMul r (expandAcc r e []) (expandAcc r f []) ++ p

def expand {σ : Type _} (r : σ → σ → Bool) (e : Expr σ) : Sparse σ :=
  expandAcc r e []

def mergeHead {σ : Type _} [DecidableEq σ] (t : List σ × Rat) : Sparse σ → Sparse σ
  | [] => [t]
  | u :: p => if t.1 = u.1 then (t.1, t.2 + u.2) :: p else t :: u :: p

def pack {σ : Type _} [DecidableEq σ] (p : Sparse σ) : Sparse σ :=
  p.foldr mergeHead []

/-- Structural merge sort with a semantics-preserving fallback. No theorem is
needed to execute its recursion in the kernel. -/
def sortFuel {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) :
    Nat → Sparse σ → Sparse σ
  | 0, p => p
  | _ + 1, [] => []
  | _ + 1, [t] => [t]
  | n + 1, t :: u :: p =>
      let q := t :: u :: p
      let k := q.length / 2
      Ordered.add r (sortFuel r n (q.take k)) (sortFuel r n (q.drop k))

def normalize {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool)
    (e : Expr σ) : Sparse σ :=
  let p := expand r e
  (sortFuel r p.length p).filter (fun t => t.2 != 0)

def check {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) (e f : Expr σ) : Bool :=
  (normalize r (.add e (.mul (.const (-1)) f))).isEmpty

end SpringerLean.RatPolyCheck.Fast
