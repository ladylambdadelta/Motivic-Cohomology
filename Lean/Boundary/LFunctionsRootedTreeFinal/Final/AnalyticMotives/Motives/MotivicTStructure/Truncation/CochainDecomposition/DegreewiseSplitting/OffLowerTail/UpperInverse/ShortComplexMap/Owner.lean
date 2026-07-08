import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.OffLowerTail.UpperInverse.FullComponent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Components.Owner

/-!
# Off-lower-tail upper map in the evaluated short complex

This file connects the second map of the evaluated normalized truncation short
complex to the degree component of the concrete upper projection chain map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The second map of the evaluated normalized cochain-decomposition short
complex is the degree component of the concrete upper truncation projection. -/
theorem additiveCochainDecompositionDegreewiseUpperMap_eq_projection_component
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).g =
      (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
        cut
        complex).f degree :=
  rfl

/-- On a nonboundary upper-tail degree, the second map of the evaluated
normalized cochain-decomposition short complex is the inverse nonboundary
upper-truncation isomorphism. -/
theorem additiveCochainDecompositionDegreewiseUpperMap_of_not_boundary
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (degree : ℤ)
    (hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).g =
      (_root_.HomologicalComplex.truncGEXIso
        complex
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        hdegree
        hboundary).inv :=
  Eq.trans
    (TraceAnalyticMotivicTStructure
      .additiveCochainDecompositionDegreewiseUpperMap_eq_projection_component
        cut
        complex
        degree)
    (TraceAnalyticMotivicTStructure
      .additiveTruncGEProjectionMap_f_of_not_boundary
        cut
        complex
        tail
        degree
        hdegree
        hboundary)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
