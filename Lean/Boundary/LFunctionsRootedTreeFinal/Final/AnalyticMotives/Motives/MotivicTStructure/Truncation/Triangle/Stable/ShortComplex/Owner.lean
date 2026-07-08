import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.ConeVertex.Owner

/-!
# Stable lower-inclusion truncation short complex

This file extracts the short complex attached to the stable lower-inclusion
distinguished triangle and exposes its object and morphism projections.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The short complex attached to the stable lower-inclusion distinguished
triangle. -/
def stableLowerInclusionShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    ShortComplex TraceAnalyticStableMotiveCategory :=
  shortComplexOfDistTriangle
    (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle_distinguished
      cut
      complex)

/-- The first object of the stable lower-inclusion short complex is the stable
lower truncation. -/
theorem stableLowerInclusionShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
      cut
      complex).X₁ =
      TraceAnalyticMotivicTStructure.stableTruncLE cut complex :=
  rfl

/-- The second object of the stable lower-inclusion short complex is the stable
image of the original complex. -/
theorem stableLowerInclusionShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
      cut
      complex).X₂ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  rfl

/-- The third object of the stable lower-inclusion short complex is the third
vertex of the stable lower-inclusion triangle. -/
theorem stableLowerInclusionShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
      cut
      complex).X₃ =
      (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
        cut
        complex).obj₃ :=
  rfl

/-- The third object of the stable lower-inclusion short complex is the named
stable cone vertex. -/
theorem stableLowerInclusionShortComplex_X₃_eq_coneVertex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
      cut
      complex).X₃ =
      TraceAnalyticMotivicTStructure.stableLowerInclusionConeVertex
        cut
        complex :=
  rfl

/-- The first map of the stable lower-inclusion short complex is the stable
lower truncation inclusion. -/
theorem stableLowerInclusionShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
      cut
      complex).f =
      TraceAnalyticMotivicTStructure.stableTruncLEInclusionMap
        cut
        complex :=
  TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle_mor₁
    cut
    complex

/-- The second map of the stable lower-inclusion short complex is the second
map of the stable lower-inclusion triangle. -/
theorem stableLowerInclusionShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
      cut
      complex).g =
      (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
        cut
        complex).mor₂ :=
  rfl

/-- The second map of the stable lower-inclusion short complex is the named
stable cone map. -/
theorem stableLowerInclusionShortComplex_g_eq_coneMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
      cut
      complex).g =
      TraceAnalyticMotivicTStructure.stableLowerInclusionConeMap
        cut
        complex :=
  rfl

/-- The stable lower-inclusion map followed by the stable cone map is zero. -/
theorem stableLowerInclusionShortComplex_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
      cut
      complex).f ≫
        (TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
          cut
          complex).g =
      0 :=
  (TraceAnalyticMotivicTStructure.stableLowerInclusionShortComplex
    cut
    complex).zero

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
