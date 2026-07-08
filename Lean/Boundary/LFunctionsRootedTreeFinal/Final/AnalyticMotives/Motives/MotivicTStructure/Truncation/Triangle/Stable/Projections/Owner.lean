import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Owner

/-!
# Stable truncation triangle projections

This file exposes the vertices and first morphism of the stable lower-inclusion
triangle in terms of the named stable truncation objects and maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The first vertex of the stable lower-inclusion triangle is the lower
stable truncation. -/
theorem stableLowerInclusionTriangle_obj₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
      cut
      complex).obj₁ =
      TraceAnalyticMotivicTStructure.stableTruncLE cut complex :=
  rfl

/-- The second vertex of the stable lower-inclusion triangle is the stable
image of the original additive complex. -/
theorem stableLowerInclusionTriangle_obj₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
      cut
      complex).obj₂ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  rfl

/-- The first morphism of the stable lower-inclusion triangle is the stable
lower truncation inclusion map. -/
theorem stableLowerInclusionTriangle_firstMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
      cut
      complex).mor₁ =
      TraceAnalyticMotivicTStructure.stableTruncLEInclusionMap
        cut
        complex :=
  TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle_mor₁
    cut
    complex

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
