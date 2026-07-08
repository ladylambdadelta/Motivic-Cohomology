import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.PretriangulatedFields.Cocone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Bounded.MorphismProperty.Owner

/-!
# Cocone field for bounded analytic source maps

Bounded analytic source maps have degreewise bounded chosen stable-infinity
cofibers.  This file packages those maps inside the degreewise bounded stable
source and applies the cofiber-bounded cocone theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A bounded analytic source complex, packaged as an object of the
degreewise bounded stable source. -/
def sourceWeightBoundedObject
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable where
  obj :=
    TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject complex
  property :=
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject_of_sourceStableWeightBoundedObject
        complex

/-- The ambient object of a packaged bounded analytic source complex is its
stable comparison-source object. -/
theorem sourceWeightBoundedObject_object
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .sourceWeightBoundedObject complex).object =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
        complex :=
  rfl

/-- A bounded analytic source map, packaged as a morphism in the degreewise
bounded stable source. -/
def sourceWeightBoundedMap
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .sourceWeightBoundedObject source ⟶
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .sourceWeightBoundedObject target :=
  TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom

/-- The ambient morphism of a packaged bounded analytic source map is the
stable comparison-source map. -/
theorem sourceWeightBoundedMap_eq_ambient
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .sourceWeightBoundedMap hom =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom :=
  rfl

/-- Bounded analytic source maps have degreewise bounded distinguished
cocone triangles. -/
theorem distinguished_cocone_triangle_of_sourceWeightBoundedMap
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    ∃ (cofiber :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
      (coconeMap :
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .sourceWeightBoundedObject target ⟶ cofiber)
      (boundaryMap :
        cofiber ⟶
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .sourceWeightBoundedObject source)⟦(1 : ℤ)⟧),
      Triangle.mk
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .sourceWeightBoundedMap hom)
          coconeMap
          boundaryMap ∈
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .distinguishedTriangles :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .distinguished_cocone_triangle_of_cofiberBounded
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .sourceWeightBoundedMap hom)
      (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        .sourceStableWeightBoundedMap_mem_cofiberDegreewiseIsoClosureBoundedMorphisms
          hom)

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
