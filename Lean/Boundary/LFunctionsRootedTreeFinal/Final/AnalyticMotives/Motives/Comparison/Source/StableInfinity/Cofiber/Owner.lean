import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Owner

/-!
# Cofiber triangles from the comparison-source stable infinity package

This file exposes the chosen cofiber triangle supplied by the stable infinity
category of analytic motives directly in the comparison-source namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The stable-infinity cofiber triangle attached to a comparison-source
morphism. -/
def stableInfinityCofiberTriangle
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    Pretriangulated.Triangle TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.cofiberTriangle morphism

/-- The first vertex of the stable-infinity cofiber triangle is the source of
the original comparison-source morphism. -/
theorem stableInfinityCofiberTriangle_obj₁
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle morphism).obj₁ =
      source :=
  rfl

/-- The second vertex of the stable-infinity cofiber triangle is the target of
the original comparison-source morphism. -/
theorem stableInfinityCofiberTriangle_obj₂
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle morphism).obj₂ =
      target :=
  rfl

/-- The third vertex of the stable-infinity cofiber triangle is the chosen
stable-infinity cofiber object. -/
theorem stableInfinityCofiberTriangle_obj₃
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle morphism).obj₃ =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberObject morphism :=
  rfl

/-- The first map of the stable-infinity cofiber triangle is the original
comparison-source morphism. -/
theorem stableInfinityCofiberTriangle_mor₁
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle morphism).mor₁ =
      morphism :=
  rfl

/-- The second map of the stable-infinity cofiber triangle is the chosen
cofiber cocone map. -/
theorem stableInfinityCofiberTriangle_mor₂
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle morphism).mor₂ =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberCoconeMap morphism :=
  rfl

/-- The third map of the stable-infinity cofiber triangle is the chosen
cofiber boundary map. -/
theorem stableInfinityCofiberTriangle_mor₃
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle morphism).mor₃ =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberBoundary morphism :=
  rfl

/-- The original comparison-source morphism followed by the chosen cofiber
cocone map is zero. -/
theorem stableInfinityCofiber_morphism_comp_cocone
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    morphism ≫
        TraceAnalyticDMgmComparisonSource
          .stableInfinityCategory.cofiberCoconeMap morphism =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.cofiber_morphism_comp_cocone morphism

/-- The chosen cofiber cocone map followed by the chosen cofiber boundary map
is zero. -/
theorem stableInfinityCofiber_cocone_comp_boundary
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberCoconeMap morphism ≫
        TraceAnalyticDMgmComparisonSource
          .stableInfinityCategory.cofiberBoundary morphism =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.cofiber_cocone_comp_boundary morphism

/-- The chosen cofiber boundary map followed by the shifted original morphism
is zero. -/
theorem stableInfinityCofiber_boundary_comp_shift_morphism
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberBoundary morphism ≫
        morphism⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.cofiber_boundary_comp_shift_morphism
      morphism

/-- The stable-infinity cofiber triangle attached to a comparison-source
morphism is distinguished. -/
theorem stableInfinityCofiberTriangle_distinguished
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle morphism ∈
      TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.cofiberTriangle_distinguished morphism

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
