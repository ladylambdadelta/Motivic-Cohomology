import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.Owner

/-!
# Yoneda exactness for the transported cochain-decomposition triangle

The transported cochain-decomposition triangle has the stable lower
truncation, original object, and stable upper truncation as vertices.  Since it
is distinguished, its Mathlib short complex is exact after both preadditive
Yoneda probes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- Covariant preadditive Yoneda exactness for the Mathlib short complex
attached to the transported stable cochain-decomposition triangle. -/
theorem stableCochainDecompositionTransportedTriangle_coyoneda_exact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)]
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((shortComplexOfDistTriangle
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex)
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_distinguished
          cut
          complex)).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory.coyonedaShortComplex_exact
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle cut complex)
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle_distinguished cut complex)
    probe

/-- Contravariant preadditive Yoneda exactness for the Mathlib short complex
attached to the transported stable cochain-decomposition triangle. -/
theorem stableCochainDecompositionTransportedTriangle_yoneda_exact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)]
    (probe : StableInfinityOwner.PresentedCategory) :
    ((shortComplexOfDistTriangle
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex)
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_distinguished
          cut
          complex)).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory.yonedaShortComplex_exact
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle cut complex)
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle_distinguished cut complex)
    probe

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
