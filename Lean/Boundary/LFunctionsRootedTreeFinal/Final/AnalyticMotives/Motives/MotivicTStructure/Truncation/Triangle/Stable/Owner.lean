import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Stable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.ConeComparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Triangulated.Owner

/-!
# Stable truncation triangles

This file sends the additive lower-inclusion mapping-cone triangle through the
Verdier quotient and proves that its image is distinguished in the stable
analytic motive category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The stable image of the additive lower-inclusion mapping-cone triangle. -/
def stableLowerInclusionTriangle
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    Triangle TraceAnalyticStableMotiveCategory :=
  TraceAnalyticStableMotiveCategory.quotientFunctor.mapTriangle.obj
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
      cut
      complex)

/-- The stable lower-inclusion triangle is distinguished because it is the
Verdier quotient image of an additive distinguished triangle. -/
theorem stableLowerInclusionTriangle_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
        cut
        complex ∈
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  TraceAnalyticStableMotiveCategory.quotientFunctor_map_distinguished
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle_distinguished
      cut
      complex)

/-- The first morphism of the stable lower-inclusion triangle is the Verdier
quotient image of the lower inclusion map. -/
theorem stableLowerInclusionTriangle_mor₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
      cut
      complex).mor₁ =
      TraceAnalyticMotivicTStructure.stableTruncLEInclusionMap
        cut
        complex :=
  congrArg
    (fun morphism =>
      TraceAnalyticStableMotiveCategory.quotientFunctor.map morphism)
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle_mor₁
      cut
      complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
