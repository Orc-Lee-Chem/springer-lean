import Init.Data.Rat.Basic

import Init.Data.Fin.Fold

import Init.Data.List.Sort.Basic



-- Executable certificate syntax and algorithms only. No mathematical

-- conclusion, analytic structure or axiom is stored in these data.



namespace SpringerLean.RatPolyCheck

abbrev Sparse (σ : Type _) := List (List σ × Rat)

def insertTerm {σ : Type _} [DecidableEq σ] (t : List σ × Rat) : Sparse σ → Sparse σ
  | [] => if t.2 = 0 then [] else [t]
  | a :: p =>
      if t.2 = 0 then a :: p
      else if t.1 = a.1 then
        if t.2 + a.2 = 0 then p else (a.1, t.2 + a.2) :: p
      else a :: insertTerm t p

def add {σ : Type _} [DecidableEq σ] : Sparse σ → Sparse σ → Sparse σ
  | [], q => q
  | t :: p, q => insertTerm t (add p q)

def mulTerm {σ : Type _} (r : σ → σ → Bool)
    (t u : List σ × Rat) : List σ × Rat :=
  ((t.1 ++ u.1).mergeSort r, t.2 * u.2)

def mul {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) : Sparse σ → Sparse σ → Sparse σ
  | [], _ => []
  | t :: p, q => add (q.map (mulTerm r t)) (mul r p q)

inductive Expr (σ : Type _)
  | const : Rat → Expr σ
  | var : σ → Expr σ
  | add : Expr σ → Expr σ → Expr σ
  | mul : Expr σ → Expr σ → Expr σ

def normalize {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) : Expr σ → Sparse σ
  | .const q => if q = 0 then [] else [([], q)]
  | .var i => [([i], 1)]
  | .add e f => add (normalize r e) (normalize r f)
  | .mul e f => mul r (normalize r e) (normalize r f)

def check {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) (e f : Expr σ) : Bool :=
  (normalize r (.add e (.mul (.const (-1)) f))).isEmpty

def Expr.smartMulLeft {σ : Type _} (e f : Expr σ) : Expr σ :=
  match e with
  | .const q => if q = 0 then .const 0 else .mul e f
  | _ => .mul e f

def Expr.mulUnlessRightZero {σ : Type _} (e : Unit → Expr σ) (f : Expr σ) : Expr σ :=
  match f with
  | .const q => if q = 0 then .const 0 else Expr.smartMulLeft (e ()) f
  | _ => Expr.smartMulLeft (e ()) f

def Expr.smartAddLeft {σ : Type _} (e f : Expr σ) : Expr σ :=
  match e with
  | .const q => if q = 0 then f else .add e f
  | _ => .add e f

def Expr.smartAdd {σ : Type _} (e f : Expr σ) : Expr σ :=
  match f with
  | .const q => if q = 0 then e else Expr.smartAddLeft e f
  | _ => Expr.smartAddLeft e f

def Expr.fsum {σ : Type _} (f : Nat → Expr σ) : Nat → Expr σ
  | 0 => .const 0
  | n + 1 => Expr.smartAdd (Expr.fsum f n) (f n)

def Expr.pow {σ : Type _} (e : Expr σ) : Nat → Expr σ
  | 0 => .const 1
  | n + 1 => .mul (Expr.pow e n) e

def powerCoeffExpr {σ : Type _} (f : Nat → Expr σ) : Nat → Nat → Expr σ
  | 0, n => .const (if n = 0 then 1 else 0)
  | d + 1, n => Expr.fsum
      (fun i => Expr.mulUnlessRightZero (fun _ => powerCoeffExpr f d i) (f (n - i))) (n + 1)

def bipowerCoeffExpr {σ : Type _} (f : Nat → Nat → Expr σ) : Nat → Nat → Nat → Expr σ
  | 0, i, j => .const (if i = 0 ∧ j = 0 then 1 else 0)
  | d + 1, i, j => Expr.fsum (fun p =>
      Expr.fsum (fun q => Expr.mulUnlessRightZero (fun _ => bipowerCoeffExpr f d q p)
        (f (i - q) (j - p))) (i + 1)) (j + 1)

def Expr.sumFin {σ : Type _} : {N : Nat} → (Fin N → Expr σ) → Expr σ
  | 0, _ => .const 0
  | n + 1, f => .add (f 0) (Expr.sumFin (fun i : Fin n => f i.succ))

def Expr.sub {σ : Type _} (e f : Expr σ) : Expr σ := .add e (.mul (.const (-1)) f)

def Expr.scale {σ : Type _} (q : Rat) (e : Expr σ) : Expr σ := .mul (.const q) e

end SpringerLean.RatPolyCheck



namespace SpringerLean

open RatPolyCheck

abbrev CoeffExpr := RatPolyCheck.Expr (Bool × Nat)

def phiCoeffExpr : Nat → CoeffExpr
  | 0 => .const 1
  | n + 1 => if n = 0 then .const 0 else .var (false, n)

def forwardKernelCoeffExpr (i j : Nat) : CoeffExpr :=
  if i = 0 ∨ j = 0 then .const 0 else .var (false, i + j - 1)

def logGrunskyCoeffExpr (i j : Nat) : CoeffExpr :=
  Expr.fsum (fun d => .mul (.const ((d : Rat)⁻¹))
    (bipowerCoeffExpr forwardKernelCoeffExpr d i j)) (j + 1)

def CoeffExpr.conjugate : CoeffExpr → CoeffExpr
  | .const q => .const q
  | .var v => .var (!v.1, v.2)
  | .add e f => .add (conjugate e) (conjugate f)
  | .mul e f => .mul (conjugate e) (conjugate f)

def CoeffExpr.normSq (e : CoeffExpr) : CoeffExpr := .mul e e.conjugate

def schoberDiagonalExpr (k : Nat) : CoeffExpr :=
  Expr.fsum (fun j => .mul (.const ((((j + 1 : Nat) : Rat) / (k : Rat)) ^ 2))
    (CoeffExpr.normSq (powerCoeffExpr phiCoeffExpr k (k - 1 - j)))) k

def grunskyDeficitExpr (N : Nat) (x : Fin N → CoeffExpr) : CoeffExpr :=
  Expr.sub
    (Expr.sumFin (fun i : Fin N => Expr.scale ((((i.val + 1 : Nat) : Rat))⁻¹)
      (CoeffExpr.normSq (x i))))
    (Expr.sumFin (fun j : Fin N => Expr.scale (((j.val + 1 : Nat) : Rat))
      (CoeffExpr.normSq (Expr.sumFin (fun i : Fin N => Expr.mulUnlessRightZero
        (fun _ => logGrunskyCoeffExpr (j.val + 1) (i.val + 1)) (x i))))))

structure GrunskyExprTerm where
  order : Nat
  weight : Rat
  test : Fin order → CoeffExpr

structure SquareExprTerm where
  weight : Rat
  polynomial : CoeffExpr

structure RationalGramCertificate where
  grunskyCount : Nat
  grunsky : Fin grunskyCount → GrunskyExprTerm
  squareCount : Nat
  square : Fin squareCount → SquareExprTerm

def RationalGramCertificate.body (c : RationalGramCertificate) : CoeffExpr :=
  .add
    (Expr.sumFin (fun i : Fin c.grunskyCount => Expr.scale (c.grunsky i).weight
      (grunskyDeficitExpr (c.grunsky i).order (c.grunsky i).test)))
    (Expr.sumFin (fun i : Fin c.squareCount => Expr.scale (c.square i).weight
      (CoeffExpr.normSq (c.square i).polynomial)))

def RationalGramCertificate.weightsCheck (c : RationalGramCertificate) : Bool :=
  decide (∀ i : Fin c.grunskyCount, 0 ≤ (c.grunsky i).weight) &&
    decide (∀ i : Fin c.squareCount, 0 ≤ (c.square i).weight)

def gramTargetExpr (k : Nat) (C η : Rat) : CoeffExpr :=
  Expr.sub (Expr.sub (.const 1) (Expr.scale C⁻¹ (schoberDiagonalExpr k)))
    (Expr.scale η (Expr.sub (.const 1) (CoeffExpr.normSq (.var (false, 1)))))

def coeffExprVariableOrder (v w : Bool × Nat) : Bool :=
  decide (2 * v.2 + (if v.1 then 1 else 0) ≤ 2 * w.2 + (if w.1 then 1 else 0))

def RationalGramCertificate.check (c : RationalGramCertificate) (k : Nat) (C η : Rat) : Bool :=
  c.weightsCheck && RatPolyCheck.check coeffExprVariableOrder (gramTargetExpr k C η) c.body

end SpringerLean



namespace SpringerLean.RatPolyCheck.Structural

def insertVar {σ : Type _} (r : σ → σ → Bool) (a : σ) : List σ → List σ
  | [] => [a]
  | b :: bs => if r a b then a :: b :: bs else b :: insertVar r a bs

def sortVars {σ : Type _} (r : σ → σ → Bool) : List σ → List σ
  | [] => []
  | a :: as => insertVar r a (sortVars r as)


def mulTerm {σ : Type _} (r : σ → σ → Bool)
    (t u : List σ × Rat) : List σ × Rat :=
  (sortVars r (t.1 ++ u.1), t.2 * u.2)

def mul {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) : Sparse σ → Sparse σ → Sparse σ
  | [], _ => []
  | t :: p, q => add (q.map (mulTerm r t)) (mul r p q)

def normalize {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) : Expr σ → Sparse σ
  | .const q => if q = 0 then [] else [([], q)]
  | .var i => [([i], 1)]
  | .add e f => add (normalize r e) (normalize r f)
  | .mul e f => mul r (normalize r e) (normalize r f)

def check {σ : Type _} [DecidableEq σ] (r : σ → σ → Bool) (e f : Expr σ) : Bool :=
  (normalize r (.add e (.mul (.const (-1)) f))).isEmpty

end SpringerLean.RatPolyCheck.Structural



namespace SpringerLean

open RatPolyCheck

def RationalGramCertificate.structuralCheck (c : RationalGramCertificate)
    (k : Nat) (C η : Rat) : Bool :=
  c.weightsCheck && Structural.check coeffExprVariableOrder (gramTargetExpr k C η) c.body

end SpringerLean

