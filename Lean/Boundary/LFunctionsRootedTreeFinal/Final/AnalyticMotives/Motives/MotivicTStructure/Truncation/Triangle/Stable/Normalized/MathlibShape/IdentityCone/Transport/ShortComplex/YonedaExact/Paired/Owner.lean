import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.ShortComplex.YonedaExact.Owner

/-!
# Paired Yoneda exactness for the named stable cochain-decomposition short complex

This file bundles the covariant and contravariant preadditive Yoneda exactness
theorems for the named stable cochain-decomposition short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The named stable cochain-decomposition short complex is exact after both
covariant and contravariant preadditive Yoneda probes, assuming the
cochain-level cone-to-upper comparison is an isomorphism. -/
theorem stableCochainDecompositionShortComplex_yonedaExact_pair_of_isIso_cochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)]
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).map
        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
      ((TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).op.map
          (preadditiveYoneda.obj rightProbe)).Exact :=
  And.intro
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionShortComplex_coyoneda_exact_of_isIso_cochainMap
        cut
        complex
        leftProbe)
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionShortComplex_yoneda_exact_of_isIso_cochainMap
        cut
        complex
        rightProbe)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
