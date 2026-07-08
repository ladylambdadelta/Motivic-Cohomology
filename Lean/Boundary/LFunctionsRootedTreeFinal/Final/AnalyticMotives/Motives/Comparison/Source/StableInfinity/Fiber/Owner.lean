import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.ShortComplex.Owner

/-!
# Fiber triangles from the comparison-source stable infinity package

This file exposes the chosen fiber triangle supplied by the stable infinity
category of analytic motives directly in the comparison-source namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The stable-infinity fiber triangle attached to a comparison-source
morphism. -/
def stableInfinityFiberTriangle
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    Pretriangulated.Triangle TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.fiberTriangle morphism

/-- The first vertex of the stable-infinity fiber triangle is the chosen
stable-infinity fiber object. -/
theorem stableInfinityFiberTriangle_obj₁
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberTriangle morphism).obj₁ =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.fiberObject morphism :=
  rfl

/-- The second vertex of the stable-infinity fiber triangle is the source of
the original comparison-source morphism. -/
theorem stableInfinityFiberTriangle_obj₂
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberTriangle morphism).obj₂ =
      source :=
  rfl

/-- The third vertex of the stable-infinity fiber triangle is the target of
the original comparison-source morphism. -/
theorem stableInfinityFiberTriangle_obj₃
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberTriangle morphism).obj₃ =
      target :=
  rfl

/-- The first map of the stable-infinity fiber triangle is the chosen
stable-infinity fiber map. -/
theorem stableInfinityFiberTriangle_mor₁
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberTriangle morphism).mor₁ =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.fiberMap morphism :=
  rfl

/-- The second map of the stable-infinity fiber triangle is the original
comparison-source morphism. -/
theorem stableInfinityFiberTriangle_mor₂
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberTriangle morphism).mor₂ =
      morphism :=
  rfl

/-- The chosen stable-infinity fiber map composes with the original morphism
to zero. -/
theorem stableInfinityFiberMap_comp_morphism
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.fiberMap morphism ≫
        morphism =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.fiberMap_comp_morphism morphism

/-- The stable-infinity fiber triangle attached to a comparison-source
morphism is distinguished. -/
theorem stableInfinityFiberTriangle_distinguished
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle morphism ∈
      TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.fiberTriangle_distinguished morphism

/-- The chosen stable-infinity fiber triangle is the inverse rotation of the
chosen stable-infinity cofiber triangle. -/
theorem stableInfinityFiberTriangle_eq_invRotate_cofiber
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.stableInfinityFiberTriangle morphism =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle morphism).invRotate :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.fiberTriangle_eq_invRotate_cofiber morphism

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
