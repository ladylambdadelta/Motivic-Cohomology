import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.Projections.Owner

/-!
# Short complex of the transported stable cochain-decomposition triangle

Mathlib attaches a short complex to every distinguished triangle.  For the
transported cochain-decomposition triangle, this file records that the attached
short complex has the same vertices and first two maps as the named stable
cochain-decomposition short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The first object of Mathlib's short complex for the transported triangle
is the first object of the named stable cochain-decomposition short complex. -/
theorem transportedTriangleShortComplex_X₁_eq_stableCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (shortComplexOfDistTriangle
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex)
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_distinguished
          cut
          complex)).X₁ =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).X₁ :=
  rfl

/-- The middle object of Mathlib's short complex for the transported triangle
is the middle object of the named stable cochain-decomposition short complex. -/
theorem transportedTriangleShortComplex_X₂_eq_stableCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (shortComplexOfDistTriangle
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex)
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_distinguished
          cut
          complex)).X₂ =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).X₂ :=
  rfl

/-- The third object of Mathlib's short complex for the transported triangle
is the third object of the named stable cochain-decomposition short complex. -/
theorem transportedTriangleShortComplex_X₃_eq_stableCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (shortComplexOfDistTriangle
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex)
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_distinguished
          cut
          complex)).X₃ =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).X₃ :=
  rfl

/-- The first map of Mathlib's short complex for the transported triangle is
the first map of the named stable cochain-decomposition short complex. -/
theorem transportedTriangleShortComplex_f_eq_stableCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (shortComplexOfDistTriangle
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex)
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_distinguished
          cut
          complex)).f =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).f :=
  rfl

/-- The second map of Mathlib's short complex for the transported triangle is
the second map of the named stable cochain-decomposition short complex. -/
theorem transportedTriangleShortComplex_g_eq_stableCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (shortComplexOfDistTriangle
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex)
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_distinguished
          cut
          complex)).g =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).g :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
