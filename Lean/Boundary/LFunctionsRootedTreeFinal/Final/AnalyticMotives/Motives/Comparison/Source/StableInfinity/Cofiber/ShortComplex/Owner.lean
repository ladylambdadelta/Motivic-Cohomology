import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.YonedaExact.Owner

/-!
# Cofiber short complexes in the analytic comparison source

This file exposes the short complex attached by the stable-infinity package to
a chosen comparison-source cofiber triangle, together with its two Yoneda
exactness tests.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The short complex attached to the stable-infinity cofiber triangle of a
comparison-source morphism. -/
def stableInfinityCofiberShortComplex
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    ShortComplex TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.cofiberShortComplex morphism

/-- The first map of the comparison-source cofiber short complex is the
original morphism. -/
theorem stableInfinityCofiberShortComplex_f
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberShortComplex morphism).f =
      morphism :=
  rfl

/-- The second map of the comparison-source cofiber short complex is the
chosen stable-infinity cofiber cocone map. -/
theorem stableInfinityCofiberShortComplex_g
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberShortComplex morphism).g =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberCoconeMap morphism :=
  rfl

/-- The zero-composition certificate of the comparison-source cofiber short
complex is the package-level cofiber zero-composition law. -/
theorem stableInfinityCofiberShortComplex_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberShortComplex morphism).zero =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiber_morphism_comp_cocone
          morphism :=
  rfl

/-- Covariant preadditive Yoneda exactness for comparison-source cofiber
short complexes. -/
theorem stableInfinityCofiberCoyonedaShortComplex_exact
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDMgmComparisonSourceᵒᵖ) :
    ((TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.cofiberCoyonedaShortComplex_exact
      morphism
      probe

/-- Contravariant preadditive Yoneda exactness for comparison-source cofiber
short complexes. -/
theorem stableInfinityCofiberYonedaShortComplex_exact
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDMgmComparisonSource) :
    ((TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.cofiberYonedaShortComplex_exact
      morphism
      probe

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
