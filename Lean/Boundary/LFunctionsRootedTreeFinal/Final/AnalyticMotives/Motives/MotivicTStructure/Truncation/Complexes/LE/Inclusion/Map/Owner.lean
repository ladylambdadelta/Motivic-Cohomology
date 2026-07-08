import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Inclusion.Boundary.Owner

/-!
# Lower truncation inclusion map

The lower truncation inclusion is the dual of the upper truncation projection:
apply the upper projection to the opposite complex, reverse it by `.op`, and
unop the resulting morphism of opposite complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Opposite

namespace TraceAnalyticMotivicTStructure

/-- The opposite-complex upper projection whose unopposite is the lower
truncation inclusion. -/
def additiveTruncLEOppositeGEProjectionMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    HomologicalComplex.op complex ⟶
      TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGE cut complex :=
  letI :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  TraceAnalyticMotivicTStructure.truncGEProjectionMap
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
    (HomologicalComplex.op complex)

/-- The concrete lower truncation inclusion chain map
`truncLE(cut, K) ⟶ K`, obtained by unopping the opposite upper projection. -/
def additiveTruncLEInclusionMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveTruncLE cut complex ⟶ complex :=
  (HomologicalComplex.unopFunctor
    TraceAnalyticAdditiveCategoryObject
    (ComplexShape.up ℤ).symm).map
      (TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGEProjectionMap
        cut
        complex).op

/-- The lower inclusion map is the unop-functor image of the opposite upper
projection. -/
theorem additiveTruncLEInclusionMap_eq_unop_projection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap cut complex =
      (HomologicalComplex.unopFunctor
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ).symm).map
          (TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGEProjectionMap
            cut
            complex).op :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
