import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.ShortComplex.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.YonedaExact.Owner

/-!
# Yoneda exactness for the named stable cochain-decomposition short complex

This file transports covariant preadditive Yoneda exactness from Mathlib's
short complex of the transported distinguished triangle to the named stable
cochain-decomposition short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- Covariant preadditive Yoneda exactness for the named stable
cochain-decomposition short complex, transported from the Mathlib short complex
of the transported distinguished triangle. -/
theorem stableCochainDecompositionShortComplex_coyoneda_exact_of_isIso_cochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)]
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  ShortComplex.exact_of_iso
    (((preadditiveCoyoneda.obj probe).mapShortComplex.mapIso
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionShortComplexIsoTransportedTriangleShortComplex
          cut
          complex)).symm)
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle_coyoneda_exact
        cut
        complex
        probe)

/-- Contravariant preadditive Yoneda exactness for the named stable
cochain-decomposition short complex, transported from the opposite of Mathlib's
short complex of the transported distinguished triangle. -/
theorem stableCochainDecompositionShortComplex_yoneda_exact_of_isIso_cochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)]
    (probe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  ShortComplex.exact_of_iso
    ((preadditiveYoneda.obj probe).mapShortComplex.mapIso
      (TraceAnalyticMotivicTStructure
        .transportedTriangleShortComplexOpIsoStableCochainDecompositionShortComplexOp
          cut
          complex))
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle_yoneda_exact
        cut
        complex
        probe)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
