import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Maps.Owner

/-!
# Abelian-envelope lower-inclusion support

The abelian-envelope lower truncation is zero off the lower-tail embedding.
This gives zero components for the lower inclusion map outside that tail.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- Off the lower-tail embedding, the abelian-envelope lower truncation object
is degreewise zero. -/
theorem abelianEnvelopeTruncLE_X_isZero_of_r_eq_none
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        none) :
    IsZero
      ((TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
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

/-- Off the lower-tail embedding, the abelian-envelope lower inclusion chain
map has zero component. -/
theorem abelianEnvelopeTruncLEInclusionMap_f_of_r_eq_none
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        none) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEInclusionMap
        cut
        complex).f degree =
      0 :=
  (TraceAnalyticMotivicTStructure
    .abelianEnvelopeTruncLE_X_isZero_of_r_eq_none
      cut
      complex
      degree
      hnone).eq_of_src
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap cut complex).f degree)
        0

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
