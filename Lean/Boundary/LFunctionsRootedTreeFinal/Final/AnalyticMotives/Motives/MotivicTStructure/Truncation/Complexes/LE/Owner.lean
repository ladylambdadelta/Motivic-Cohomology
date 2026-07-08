import Mathlib.Algebra.Homology.Embedding.TruncGE
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Complexes.Owner

/-!
# Concrete analytic `LE` truncations of additive complexes

Mathlib's current truncation implementation in this checkout provides
`truncGE`.  This file constructs the dual lower truncation by applying
`truncGE` to the opposite complex along the opposite of the lower-tail
embedding, then unopping the result back to integer cochain complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Opposite

/-- The integer lower-tail embedding used for the analytic `LE` truncation at
cut `cut`.  It embeds the natural-number shaped lower tail by `n ↦ cut - n`. -/
def TraceAnalyticMotivicTStructure.truncLEEmbedding
    (cut : ℤ) :
    ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpIntLE cut

/-- The opposite of the lower-tail embedding is an upper-tail truncation
embedding. -/
def TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE
    (cut : ℤ) :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE where
  rel' i j h :=
    ComplexShape.Embedding.IsRelIff.rel'
      (e := TraceAnalyticMotivicTStructure.truncLEEmbedding cut)
      i
      j
      h
  mem_next {j} {k'} h :=
    ComplexShape.Embedding.mem_prev
      (e := TraceAnalyticMotivicTStructure.truncLEEmbedding cut)
      h

/-- The opposite-complex `GE` truncation underlying analytic `LE` truncation. -/
def TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    HomologicalComplex TraceAnalyticAdditiveCategoryObjectᵒᵖ
      (ComplexShape.up ℤ).symm :=
  have truncGEInstance :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  HomologicalComplex.truncGE
    (HomologicalComplex.op complex)
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op

/-- The concrete additive-complex `LE` truncation of one analytic complex,
defined by dualizing Mathlib's `truncGE`. -/
def TraceAnalyticMotivicTStructure.additiveTruncLE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticAdditiveCochainComplex :=
  (TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGE cut complex).unopSymm

/-- The opposite-complex map underlying analytic `LE` truncation. -/
def TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGEMap
    (cut : ℤ)
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGE cut target ⟶
      TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGE cut source :=
  have truncGEInstance :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  HomologicalComplex.truncGEMap
    ((HomologicalComplex.opFunctor
      TraceAnalyticAdditiveCategoryObject
      (ComplexShape.up ℤ)).map hom.op)
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op

/-- The concrete additive-complex `LE` truncation of a chain map. -/
def TraceAnalyticMotivicTStructure.additiveTruncLEMap
    (cut : ℤ)
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.additiveTruncLE cut source ⟶
      TraceAnalyticMotivicTStructure.additiveTruncLE cut target :=
  (HomologicalComplex.unopFunctor
    TraceAnalyticAdditiveCategoryObject
    (ComplexShape.up ℤ).symm).map
      (TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGEMap
        cut
        hom).op

/-- The object part of analytic `LE` truncation is the unop of the opposite
`GE` truncation. -/
theorem TraceAnalyticMotivicTStructure.additiveTruncLE_eq_unop_oppositeGE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticMotivicTStructure.additiveTruncLE cut complex =
      (TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGE
        cut
        complex).unopSymm :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
