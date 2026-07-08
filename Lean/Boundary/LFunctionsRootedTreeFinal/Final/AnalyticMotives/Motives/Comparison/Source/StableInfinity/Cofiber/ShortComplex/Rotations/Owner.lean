import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.CofiberRotations.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.CofiberRotations.ZeroComposition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.YonedaExact.Owner

/-!
# Rotated cofiber short complexes in the analytic comparison source

This file exposes the short complexes attached to the rotated and
inverse-rotated stable-infinity cofiber triangles, together with their maps,
zero fields, and Yoneda exactness.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The short complex attached to the rotated stable-infinity cofiber
triangle of a comparison-source morphism. -/
def stableInfinityRotatedCofiberShortComplex
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    ShortComplex TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.rotatedCofiberShortComplex morphism

/-- The short complex attached to the inverse-rotated stable-infinity cofiber
triangle of a comparison-source morphism. -/
def stableInfinityInvRotatedCofiberShortComplex
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    ShortComplex TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.invRotatedCofiberShortComplex morphism

/-- The first map of the rotated cofiber short complex is the chosen cofiber
cocone map. -/
theorem stableInfinityRotatedCofiberShortComplex_f
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityRotatedCofiberShortComplex morphism).f =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberCoconeMap morphism :=
  rfl

/-- The second map of the rotated cofiber short complex is the chosen cofiber
boundary map. -/
theorem stableInfinityRotatedCofiberShortComplex_g
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityRotatedCofiberShortComplex morphism).g =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberBoundary morphism :=
  rfl

/-- The first map of the inverse-rotated cofiber short complex is the shifted
negative boundary followed by the unit comparison. -/
theorem stableInfinityInvRotatedCofiberShortComplex_f
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityInvRotatedCofiberShortComplex morphism).f =
      -((TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv TraceAnalyticDMgmComparisonSource
          (1 : ℤ)).unitIso.inv.app _ :=
  rfl

/-- The second map of the inverse-rotated cofiber short complex is the
original morphism. -/
theorem stableInfinityInvRotatedCofiberShortComplex_g
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityInvRotatedCofiberShortComplex morphism).g =
      morphism :=
  rfl

/-- The zero field of the rotated cofiber short complex is supplied by the
rotated cofiber triangle distinguishedness. -/
theorem stableInfinityRotatedCofiberShortComplex_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityRotatedCofiberShortComplex morphism).zero =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.distinguishedTriangle_mor₁_comp_mor₂
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCategory.rotatedCofiberTriangle morphism)
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCategory.rotatedCofiberTriangle_distinguished
            morphism) :=
  rfl

/-- The zero field of the inverse-rotated cofiber short complex is supplied by
the inverse-rotated cofiber triangle distinguishedness. -/
theorem stableInfinityInvRotatedCofiberShortComplex_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityInvRotatedCofiberShortComplex morphism).zero =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.distinguishedTriangle_mor₁_comp_mor₂
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCategory.invRotatedCofiberTriangle morphism)
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCategory.invRotatedCofiberTriangle_distinguished
            morphism) :=
  rfl

/-- Covariant preadditive Yoneda exactness for rotated cofiber short
complexes. -/
theorem stableInfinityRotatedCofiberCoyonedaShortComplex_exact
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDMgmComparisonSourceᵒᵖ) :
    ((TraceAnalyticDMgmComparisonSource
      .stableInfinityRotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.rotatedCofiberCoyonedaShortComplex_exact
      morphism
      probe

/-- Contravariant preadditive Yoneda exactness for rotated cofiber short
complexes. -/
theorem stableInfinityRotatedCofiberYonedaShortComplex_exact
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDMgmComparisonSource) :
    ((TraceAnalyticDMgmComparisonSource
      .stableInfinityRotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.rotatedCofiberYonedaShortComplex_exact
      morphism
      probe

/-- Covariant preadditive Yoneda exactness for inverse-rotated cofiber short
complexes. -/
theorem stableInfinityInvRotatedCofiberCoyonedaShortComplex_exact
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDMgmComparisonSourceᵒᵖ) :
    ((TraceAnalyticDMgmComparisonSource
      .stableInfinityInvRotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.invRotatedCofiberCoyonedaShortComplex_exact
      morphism
      probe

/-- Contravariant preadditive Yoneda exactness for inverse-rotated cofiber
short complexes. -/
theorem stableInfinityInvRotatedCofiberYonedaShortComplex_exact
    {source target : TraceAnalyticDMgmComparisonSource}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDMgmComparisonSource) :
    ((TraceAnalyticDMgmComparisonSource
      .stableInfinityInvRotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCategory.invRotatedCofiberYonedaShortComplex_exact
      morphism
      probe

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
