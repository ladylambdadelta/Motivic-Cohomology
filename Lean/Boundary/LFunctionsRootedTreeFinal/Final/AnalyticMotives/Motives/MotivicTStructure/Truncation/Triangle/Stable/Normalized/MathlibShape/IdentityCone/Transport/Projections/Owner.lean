import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.Owner

/-!
# Projection formulas for the transported cochain-decomposition triangle

This file exposes the vertices and morphisms of the transported stable
cochain-decomposition triangle in terms of the stable lower truncation, the
original stable object, the stable upper truncation, and the named truncation
maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The first vertex of the transported cochain-decomposition triangle is the
stable lower truncation at the paired lower cut. -/
theorem stableCochainDecompositionTransportedTriangle_raw_obj₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex).obj₁ =
      TraceAnalyticMotivicTStructure.stableTruncLE
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
        complex :=
  rfl

/-- The second vertex of the transported cochain-decomposition triangle is the
stable image of the original complex. -/
theorem stableCochainDecompositionTransportedTriangle_raw_obj₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex).obj₂ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  rfl

/-- The third vertex of the transported cochain-decomposition triangle is the
stable upper truncation at the cut. -/
theorem stableCochainDecompositionTransportedTriangle_raw_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex).obj₃ =
      TraceAnalyticMotivicTStructure.stableTruncGE cut complex :=
  rfl

/-- The first morphism of the transported cochain-decomposition triangle is the
stable cochain-decomposition lower-inclusion map. -/
theorem stableCochainDecompositionTransportedTriangle_raw_firstMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex).mor₁ =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).f :=
  rfl

/-- The second morphism of the transported cochain-decomposition triangle is
the stable cochain-decomposition upper-projection map. -/
theorem stableCochainDecompositionTransportedTriangle_raw_secondMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex).mor₂ =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).g :=
  rfl

/-- The third morphism of the transported cochain-decomposition triangle is the
transported connecting map. -/
theorem stableCochainDecompositionTransportedTriangle_raw_thirdMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex).mor₃ =
      TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedConnectingMap
        cut
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
