import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.CofiberTriangle.Owner

/-!
# Cocone field for degreewise bounded cofiber-bounded morphisms

This file gives the Mathlib `Pretriangulated.distinguished_cocone_triangle`
field shape for a morphism whose chosen stable-infinity cofiber is
degreewise bounded.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A cofiber-bounded morphism in the degreewise bounded stable source has a
degreewise bounded distinguished cocone triangle. -/
theorem distinguished_cocone_triangle_of_cofiberBounded
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target)
    (cofiberBounded :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism)) :
    ∃ (cofiber :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
      (coconeMap : target ⟶ cofiber)
      (boundaryMap :
        cofiber ⟶
          source⟦(1 : ℤ)⟧),
      Triangle.mk morphism coconeMap boundaryMap ∈
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .distinguishedTriangles :=
  Exists.intro
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberObject morphism cofiberBounded)
    (Exists.intro
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberCoconeMap
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .inclusion.map morphism))
      (Exists.intro
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCategory.cofiberBoundary
            (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
              .inclusion.map morphism))
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .cofiberTriangle_distinguished morphism cofiberBounded)))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
