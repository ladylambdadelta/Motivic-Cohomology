import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Rotations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.YonedaExact.Fiber.Comparison.Owner

/-!
# Fiber exactness as inverse-rotated cofiber exactness

This file exposes in the comparison-source namespace that the Yoneda exactness
witnesses for chosen fiber short complexes agree with the corresponding
inverse-rotated cofiber exactness witnesses.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- Covariant fiber exactness agrees with inverse-rotated cofiber exactness in
the comparison source. -/
theorem stableInfinityFiberCoyonedaShortComplex_exact_eq_invRotated
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDMgmComparisonSourceᵒᵖ) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberCoyonedaShortComplex_exact
          morphism
          probe =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityInvRotatedCofiberCoyonedaShortComplex_exact
          morphism
          probe :=
  traceAnalyticStableInfinityCategory_fiberCoyonedaShortComplex_exact_eq_invRotated
    morphism
    probe

/-- Contravariant fiber exactness agrees with inverse-rotated cofiber
exactness in the comparison source. -/
theorem stableInfinityFiberYonedaShortComplex_exact_eq_invRotated
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDMgmComparisonSource) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberYonedaShortComplex_exact
          morphism
          probe =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityInvRotatedCofiberYonedaShortComplex_exact
          morphism
          probe :=
  traceAnalyticStableInfinityCategory_fiberYonedaShortComplex_exact_eq_invRotated
    morphism
    probe

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
