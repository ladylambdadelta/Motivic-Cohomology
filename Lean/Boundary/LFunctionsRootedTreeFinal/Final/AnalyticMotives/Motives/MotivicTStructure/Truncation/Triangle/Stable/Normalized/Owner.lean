import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Stable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Triangulated.Owner

/-!
# Normalized stable truncation triangle

This file sends the normalized additive lower-inclusion triangle through the
Verdier quotient and proves the resulting stable triangle is distinguished.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The stable image of the normalized lower-inclusion truncation triangle. -/
def stableNormalizedLowerInclusionTriangle
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    Triangle TraceAnalyticStableMotiveCategory :=
  TraceAnalyticStableMotiveCategory.quotientFunctor.mapTriangle.obj
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
      cut
      complex)

/-- The normalized stable lower-inclusion triangle is distinguished. -/
theorem stableNormalizedLowerInclusionTriangle_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
        cut
        complex ∈
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  TraceAnalyticStableMotiveCategory.quotientFunctor_map_distinguished
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure
      .additiveNormalizedLowerInclusionTriangle_distinguished cut complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
