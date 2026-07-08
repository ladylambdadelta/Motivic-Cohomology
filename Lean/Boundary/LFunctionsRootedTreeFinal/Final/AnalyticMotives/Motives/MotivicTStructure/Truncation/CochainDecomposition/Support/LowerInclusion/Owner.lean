import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Maps.Owner

/-!
# Lower inclusion support in the normalized cochain decomposition

The lower truncation is zero off the lower-tail embedding because it is the
unop of an upper truncation on the opposite complex, and upper truncation is
constructed by extension by zero.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- A normalized lower-tail degree lies in the paired lower-tail embedding. -/
theorem truncLEEmbedding_r_eq_some_of_decompositionLowerTail
    (cut : ℤ)
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
        (cut - 1 - (lowerTail : ℤ)) =
      some lowerTail :=
  ComplexShape.Embedding.r_eq_some
    (TraceAnalyticMotivicTStructure.truncLEEmbedding
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut))
    rfl

/-- Positive normalized lower-tail indices are not boundary indices for the
opposite upper-tail truncation used to define the paired lower truncation. -/
theorem truncLEEmbeddingOp_not_boundary_of_decompositionLowerTail_succ
    (cut : ℤ)
    (lowerTail : ℕ) :
    ¬ (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).op.BoundaryGE
        (Nat.succ lowerTail) :=
  fun hboundary =>
    Nat.succ_ne_zero lowerTail
      (TraceAnalyticMotivicTStructure.truncLEEmbeddingOp_boundary_tail_eq_zero
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
        (Nat.succ lowerTail)
        hboundary)

/-- On a positive normalized lower-tail degree, the paired lower truncation has
the original degree object.  The tail-zero case is deliberately excluded
because it is the boundary degree. -/
theorem additiveDecompositionTruncLE_X_of_decompositionLowerTail_succ
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
        cut
        complex).X (cut - 1 - (Nat.succ lowerTail : ℤ)) =
      complex.X (cut - 1 - (Nat.succ lowerTail : ℤ)) :=
  TraceAnalyticMotivicTStructure.additiveTruncLE_X_of_not_boundary
    (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
    complex
    (cut - 1 - (Nat.succ lowerTail : ℤ))
    (Nat.succ lowerTail)
    (TraceAnalyticMotivicTStructure.truncLEEmbedding_r_eq_some_of_decompositionLowerTail
      cut
      (Nat.succ lowerTail))
    (TraceAnalyticMotivicTStructure
      .truncLEEmbeddingOp_not_boundary_of_decompositionLowerTail_succ
        cut
        lowerTail)

/-- Off the lower-tail embedding, the concrete lower truncation object is
degreewise zero. -/
theorem additiveTruncLE_X_isZero_of_r_eq_none
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        none) :
    IsZero
      ((TraceAnalyticMotivicTStructure.additiveTruncLE
          cut
          complex).X degree) :=
  letI :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  IsZero.unop
    (((HomologicalComplex.op complex).truncGE'
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op).isZero_extend_X'
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
        degree
        hnone)

/-- Off the lower-tail embedding, the lower inclusion chain map has zero
component. -/
theorem additiveTruncLEInclusionMap_f_of_r_eq_none
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        none) :
    (TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap
        cut
        complex).f degree =
      0 :=
  (TraceAnalyticMotivicTStructure.additiveTruncLE_X_isZero_of_r_eq_none
    cut
    complex
    degree
    hnone).eq_of_src
      ((TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap
        cut
        complex).f degree)
      0

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
