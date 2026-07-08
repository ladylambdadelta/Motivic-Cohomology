import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.YonedaExact.Fiber.Owner

/-!
# Fiber short complexes in the analytic comparison source

This file exposes the short complex attached by the stable-infinity package to
a chosen comparison-source fiber triangle, together with its two Yoneda
exactness tests.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The short complex attached to the stable-infinity fiber triangle of a
comparison-source morphism. -/
def stableInfinityFiberShortComplex
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    ShortComplex TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.fiberShortComplex morphism

/-- The first map of the comparison-source fiber short complex is the chosen
stable-infinity fiber map. -/
theorem stableInfinityFiberShortComplex_f
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberShortComplex morphism).f =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.fiberMap morphism :=
  rfl

/-- The second map of the comparison-source fiber short complex is the
original morphism. -/
theorem stableInfinityFiberShortComplex_g
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberShortComplex morphism).g =
      morphism :=
  rfl

/-- The zero-composition certificate of the comparison-source fiber short
complex is the package-level fiber zero-composition law. -/
theorem stableInfinityFiberShortComplex_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberShortComplex morphism).zero =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.fiberMap_comp_morphism morphism :=
  rfl

/-- Covariant preadditive Yoneda exactness for comparison-source fiber short
complexes. -/
theorem stableInfinityFiberCoyonedaShortComplex_exact
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDMgmComparisonSourceᵒᵖ) :
    ((TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.fiberCoyonedaShortComplex_exact
      morphism
      probe

/-- Contravariant preadditive Yoneda exactness for comparison-source fiber
short complexes. -/
theorem stableInfinityFiberYonedaShortComplex_exact
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDMgmComparisonSource) :
    ((TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.fiberYonedaShortComplex_exact
      morphism
      probe

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
