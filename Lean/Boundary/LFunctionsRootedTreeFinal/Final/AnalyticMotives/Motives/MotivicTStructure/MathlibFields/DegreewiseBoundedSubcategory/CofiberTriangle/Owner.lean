import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.DistinguishedTriangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Bounded.MorphismProperty.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Owner

/-!
# Chosen cofiber triangles in the degreewise bounded source

This file packages the chosen stable-infinity cofiber triangle of a morphism
between degreewise bounded stable source objects, assuming the chosen cofiber
vertex satisfies the already-defined degreewise bounded cofiber morphism
property.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The chosen cofiber object of a degreewise-bounded morphism, packaged as a
degreewise bounded stable source object. -/
def cofiberObject
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target)
    (cofiberBounded :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism)) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable where
  obj :=
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map morphism)).obj₃
  property := cofiberBounded

/-- The ambient object of the packaged chosen cofiber is the third vertex of
the chosen stable-infinity cofiber triangle. -/
theorem cofiberObject_object
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target)
    (cofiberBounded :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberObject morphism cofiberBounded).object =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism)).obj₃ :=
  rfl

/-- The chosen stable-infinity cofiber triangle of a cofiber-bounded morphism
between degreewise bounded objects has all vertices in the degreewise bounded
source and is ambient distinguished. -/
theorem exists_ambientCofiberTriangle_of_cofiberBounded
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target)
    (cofiberBounded :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism)) :
    ∃ cofiber :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable,
      cofiber.object =
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangle
            (TraceAnalyticDMgmComparisonSource
              .DegreewiseBoundedStable.inclusion.map morphism)).obj₃ ∧
        Triangle.mk
            (TraceAnalyticDMgmComparisonSource
              .DegreewiseBoundedStable.inclusion.map morphism)
            (TraceAnalyticDMgmComparisonSource
              .stableInfinityCategory.cofiberCoconeMap
                (TraceAnalyticDMgmComparisonSource
                  .DegreewiseBoundedStable.inclusion.map morphism))
            (TraceAnalyticDMgmComparisonSource
              .stableInfinityCategory.cofiberBoundary
                (TraceAnalyticDMgmComparisonSource
                  .DegreewiseBoundedStable.inclusion.map morphism)) ∈
          TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Exists.intro
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cofiberObject morphism cofiberBounded)
    (And.intro
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cofiberObject_object morphism cofiberBounded)
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle_distinguished
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism)))

/-- The chosen cofiber triangle of a cofiber-bounded morphism, internalized as
a triangle in the degreewise bounded stable source. -/
def cofiberTriangle
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target)
    (cofiberBounded :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism)) :
    Triangle TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  Triangle.mk
    morphism
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCategory.cofiberCoconeMap
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map morphism))
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCategory.cofiberBoundary
        (TraceAnalyticDMgmComparisonSource
          .DegreewiseBoundedStable.inclusion.map morphism))

/-- The internal degreewise bounded cofiber triangle maps to the chosen
ambient stable-infinity cofiber triangle. -/
theorem cofiberTriangle_ambient
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target)
    (cofiberBounded :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism)) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .ambientTriangle
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .cofiberTriangle morphism cofiberBounded) =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism) :=
  rfl

/-- The internal cofiber triangle of a cofiber-bounded morphism is
distinguished in the degreewise bounded source. -/
theorem cofiberTriangle_distinguished
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target)
    (cofiberBounded :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms
          (TraceAnalyticDMgmComparisonSource
            .DegreewiseBoundedStable.inclusion.map morphism)) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .distinguishedTriangles
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .cofiberTriangle morphism cofiberBounded) :=
  TraceAnalyticDMgmComparisonSource
    .stableInfinityCofiberTriangle_distinguished
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .inclusion.map morphism)

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
