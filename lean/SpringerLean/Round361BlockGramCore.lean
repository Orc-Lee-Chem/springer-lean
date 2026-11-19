import SpringerLean.Round365SparseGrunskyCore

namespace SpringerLean
open RatPolyCheck

/-- A small rational block and its proposed reduced polynomial, both raw data. -/
structure RationalGramBlock where
  certificate : ListRationalGramCertificate
  polynomial : CoeffExpr

def RationalGramBlock.check (b : RationalGramBlock) : Bool :=
  b.certificate.weightsCheck &&
    Ordered.check coeffExprVariableOrder b.polynomial b.certificate.sparseBody

def gramBlockPolynomialSum (blocks : List RationalGramBlock) : CoeffExpr :=
  Expr.sumList (blocks.map RationalGramBlock.polynomial)

end SpringerLean
