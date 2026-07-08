import Mathlib.Algebra.Homology.Embedding.TruncGE
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.Complexes.GE.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Owner

/-!
# Abelian-envelope analytic `LE` truncations

The lower-tail truncation in the abelian envelope is obtained by applying
Mathlib's upper-tail truncation to the opposite complex and unopping back.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Opposite

namespace TraceAnalyticMotivicTStructure

/-- The opposite-complex `GE` truncation underlying abelian-envelope `LE`
truncation. -/
def abelianEnvelopeTruncLEOppositeGE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    HomologicalComplex TraceAnalyticAdditiveAbelianEnvelopeᵒᵖ
      (ComplexShape.up ℤ).symm :=
  have truncGEInstance :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  HomologicalComplex.truncGE
    (HomologicalComplex.op complex)
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op

/-- The abelian-envelope lower-tail truncation of an analytic complex. -/
def abelianEnvelopeTruncLE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticAbelianCochainComplex :=
  (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEOppositeGE
    cut
    complex).unopSymm

/-- The opposite-complex map underlying abelian-envelope lower-tail
truncation. -/
def abelianEnvelopeTruncLEOppositeGEMap
    (cut : ℤ)
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEOppositeGE
        cut
        target ⟶
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEOppositeGE
        cut
        source :=
  have truncGEInstance :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  HomologicalComplex.truncGEMap
    ((HomologicalComplex.opFunctor
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)).map hom.op)
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op

/-- The map induced on abelian-envelope lower-tail truncations. -/
def abelianEnvelopeTruncLEMap
    (cut : ℤ)
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE cut source ⟶
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE cut target :=
  (HomologicalComplex.unopFunctor
    TraceAnalyticAdditiveAbelianEnvelope
    (ComplexShape.up ℤ).symm).map
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEOppositeGEMap
        cut
        hom).op

/-- The object part of abelian-envelope lower truncation is the unop of the
opposite-complex upper truncation. -/
theorem abelianEnvelopeTruncLE_eq_unop_oppositeGE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE cut complex =
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEOppositeGE
        cut
        complex).unopSymm :=
  rfl

/-- The opposite-complex upper projection whose unopposite is the
abelian-envelope lower truncation inclusion. -/
def abelianEnvelopeTruncLEOppositeGEProjectionMap
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    HomologicalComplex.op complex ⟶
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEOppositeGE
        cut
        complex :=
  letI :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  letI :
      ∀ degree : ℤ,
        (HomologicalComplex.op complex).HasHomology degree :=
    fun degree =>
      CategoryWithHomology.hasHomology
        ((HomologicalComplex.op complex).sc degree)
  TraceAnalyticMotivicTStructure.truncGEProjectionMap
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
    (HomologicalComplex.op complex)

/-- The abelian-envelope lower truncation inclusion
`truncLE(cut,K) ⟶ K`. -/
def abelianEnvelopeTruncLEInclusionMap
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE cut complex ⟶
      complex :=
  (HomologicalComplex.unopFunctor
    TraceAnalyticAdditiveAbelianEnvelope
    (ComplexShape.up ℤ).symm).map
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEOppositeGEProjectionMap cut complex).op

/-- The abelian-envelope lower inclusion map is the unop-functor image of the
opposite upper projection. -/
theorem abelianEnvelopeTruncLEInclusionMap_eq_unop_projection
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap cut complex =
      (HomologicalComplex.unopFunctor
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ).symm).map
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeTruncLEOppositeGEProjectionMap cut complex).op :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
