import SpringerLean.Round331SparseCoefficientCore

namespace SpringerLean
open RatPolyCheck

def certificateFinList {α : Type _} : {N : Nat} → (Fin N → α) → List α
  | 0, _ => []
  | n + 1, f => f 0 :: certificateFinList (fun i : Fin n => f i.succ)

theorem certificateFinList_map {α β : Type _} (g : α → β) {N : Nat} (f : Fin N → α) :
    certificateFinList (fun i => g (f i)) = (certificateFinList f).map g := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [certificateFinList, List.map_cons, ih]

def RatPolyCheck.Expr.sumList {σ : Type _} : List (Expr σ) → Expr σ
  | [] => .const 0
  | e :: es => .add e (Expr.sumList es)

theorem RatPolyCheck.Expr.sumList_finList {σ : Type _} {N : Nat} (f : Fin N → Expr σ) :
    Expr.sumList (certificateFinList f) = Expr.sumFin f := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [certificateFinList, Expr.sumList, Expr.sumFin, ih]

/-- Evaluate finite data lists before constructing the polynomial body.
This is the same expression as body, with an explicit proved equality. -/
def RationalGramCertificate.listBody (c : RationalGramCertificate) : CoeffExpr :=
  .add
    (Expr.sumList ((certificateFinList c.grunsky).map (fun t =>
      Expr.scale t.weight (grunskyDeficitExpr t.order t.test))))
    (Expr.sumList ((certificateFinList c.square).map (fun t =>
      Expr.scale t.weight (CoeffExpr.normSq t.polynomial))))

theorem RationalGramCertificate.listBody_eq_body (c : RationalGramCertificate) :
    c.listBody = c.body := by
  simp only [listBody, body, ← certificateFinList_map, Expr.sumList_finList]

def RationalGramCertificate.fastListCheck (c : RationalGramCertificate)
    (k : Nat) (C η : Rat) : Bool :=
  c.weightsCheck && Structural.check coeffExprVariableOrder
    (fastGramTargetExpr k C η) c.listBody

theorem RationalGramCertificate.fastListCheck_eq (c : RationalGramCertificate)
    (k : Nat) (C η : Rat) : c.fastListCheck k C η = c.fastTargetCheck k C η := by
  rw [fastListCheck, listBody_eq_body]
  rfl

end SpringerLean
