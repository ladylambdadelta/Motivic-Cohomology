import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Bounded.MorphismProperty.Owner

/-!
# Rotation comparison for bounded stable-infinity morphism properties

This file relates the cofiber-bounded and fiber-bounded morphism properties
using the inverse-rotation comparison supplied by the stable-infinity category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- A morphism with bounded chosen stable-infinity cofiber has bounded chosen
stable-infinity fiber. -/
theorem fiberDegreewiseIsoClosureBoundedMorphisms_of_cofiber
    {source target : TraceAnalyticDMgmComparisonSource}
    {morphism : source ⟶ target}
    (cofiberBounded :
      TraceAnalyticDMgmComparisonSource
        .cofiberDegreewiseIsoClosureBoundedMorphisms morphism) :
    TraceAnalyticDMgmComparisonSource
      .fiberDegreewiseIsoClosureBoundedMorphisms morphism :=
  Eq.subst
    (motive := fun triangle =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject triangle.obj₁)
    (Eq.symm
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle_eq_invRotate_cofiber morphism))
    (TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject_shift
        cofiberBounded
        (-1 : ℤ))

/-- Bounded analytic source maps have bounded chosen stable-infinity fibers by
rotation from their bounded chosen stable-infinity cofibers. -/
theorem sourceStableWeightBoundedMap_mem_fiberDegreewiseIsoClosureBoundedMorphisms_of_cofiber
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource
      .fiberDegreewiseIsoClosureBoundedMorphisms
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) :=
  TraceAnalyticDMgmComparisonSource
    .fiberDegreewiseIsoClosureBoundedMorphisms_of_cofiber
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
          hom)

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
