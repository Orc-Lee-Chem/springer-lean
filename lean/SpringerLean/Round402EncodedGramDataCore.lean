import SpringerLean.Round380HermitianBlockEncoding

namespace SpringerLean.RawGramData
open RatPolyCheck

/-- A decoder of witness DATA, never a mathematical checker. Every decoded
block is still checked by RationalGramBlock.check and its proved soundness. -/
structure CSVState where
  values : List Int := []
  magnitude : Nat := 0
  negative : Bool := false
  started : Bool := false

def CSVState.value (s : CSVState) : Int :=
  if s.negative then -(Int.ofNat s.magnitude) else Int.ofNat s.magnitude

def csvStep (s : CSVState) (c : Char) : CSVState :=
  if c = ',' then { values := s.value :: s.values }
  else if c = '-' then { s with negative := true, started := true }
  else { s with magnitude := 10 * s.magnitude + (c.toNat - '0'.toNat), started := true }

def csvInts (s : String) : List Int :=
  let state := s.toList.foldl csvStep {}
  (if state.started then state.value :: state.values else state.values).reverse

def readInt (xs : List Int) : Int × List Int := (xs.headD 0, xs.drop 1)

def readNat (xs : List Int) : Nat × List Int :=
  let (n, rest) := readInt xs
  (n.toNat, rest)

def readRat (xs : List Int) : Rat × List Int :=
  let (num, xs) := readInt xs
  let (den, xs) := readInt xs
  ((num : Rat) / (den : Rat), xs)

def readMany {α : Type} (read : List Int → α × List Int) :
    Nat → List Int → List α × List Int
  | 0, xs => ([], xs)
  | n + 1, xs =>
    let (a, xs) := read xs
    let (as, xs) := readMany read n xs
    (a :: as, xs)

def readIndexPower (xs : List Int) : (Nat × Nat) × List Int :=
  let (j, xs) := readNat xs
  let (e, xs) := readNat xs
  ((j, e), xs)

def readMonomial (xs : List Int) : CoeffExpr × List Int :=
  let (n, xs) := readNat xs
  let (powers, xs) := readMany readIndexPower n xs
  let e := powers.foldr (fun t acc => certificateCompactMul
    (certificateCompactPow (.var (false, t.1)) t.2) acc) (.const 1)
  (e, xs)

def readLinearTerm (xs : List Int) : CoeffExpr × List Int :=
  let (q, xs) := readRat xs
  let (e, xs) := readMonomial xs
  (Expr.scale q e, xs)

def readLinear (xs : List Int) : CoeffExpr × List Int :=
  let (n, xs) := readNat xs
  let (terms, xs) := readMany readLinearTerm n xs
  (Expr.sumList terms, xs)

def readGrunsky (xs : List Int) : GrunskyExprTerm × List Int :=
  let (n, xs) := readNat xs
  let (w, xs) := readRat xs
  let (tests, xs) := readMany readLinear n xs
  ({ order := tests.length, weight := w,
     test := fun i => tests.getD i.val (.const 0) }, xs)

def readSquare (xs : List Int) : SquareExprTerm × List Int :=
  let (w, xs) := readRat xs
  let (p, xs) := readLinear xs
  ({ weight := w, polynomial := p }, xs)

def readHermitianTerm (xs : List Int) : CoeffExpr × List Int :=
  let (q, xs) := readRat xs
  let (e, xs) := readMonomial xs
  let (f, xs) := readMonomial xs
  (Expr.scale q (.mul e f.conjugate), xs)

def decodeBlockInts (xs : List Int) : RationalGramBlock :=
  let (nG, xs) := readNat xs
  let (gs, xs) := readMany readGrunsky nG xs
  let (nS, xs) := readNat xs
  let (ss, xs) := readMany readSquare nS xs
  let (nH, xs) := readNat xs
  let (hs, _) := readMany readHermitianTerm nH xs
  { certificate := { grunsky := gs, square := ss }, polynomial := Expr.sumList hs }

def decodeBlock (s : String) : RationalGramBlock := decodeBlockInts (csvInts s)

theorem csvInts_smoke : csvInts "-2,17,0" = [-2, 17, 0] := by decide +kernel
theorem decodeBlock_empty_weights :
    (decodeBlock "0,0,0").certificate.weightsCheck = true := by decide +kernel

end SpringerLean.RawGramData
#print axioms SpringerLean.RawGramData.csvInts_smoke
