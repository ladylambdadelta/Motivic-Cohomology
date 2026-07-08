import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Monotone.Homotopy.Owner

/-!
# Bounded homotopy source weights for analytic comparison

This file exposes the image of bounded additive analytic complexes and bounded
chain maps in the additive analytic homotopy category under comparison-facing
names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Comparison-facing homotopy object represented by a bounded additive analytic
complex. -/
def TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject complex

/-- The comparison-facing bounded homotopy object is the ordinary homotopy image
of the underlying complex. -/
theorem TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject_eq
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject complex =
      TraceAnalyticAdditiveHomotopyCategory.objectOf complex.complex :=
  TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject_eq complex

/-- Comparison-facing homotopy morphism represented by a bounded chain map. -/
def TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject source ⟶
      TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject target :=
  TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap hom

/-- The comparison-facing bounded homotopy map is the ordinary homotopy image of
the underlying chain map. -/
theorem TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom =
      TraceAnalyticAdditiveHomotopyCategory.mapOf hom :=
  TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap_eq hom

/-- The comparison-facing bounded homotopy map of an identity bounded chain map
is identity. -/
theorem TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap_id
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.id
          complex) =
      𝟙
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) :=
  TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap_id complex

/-- The comparison-facing bounded homotopy map of a composite bounded chain map
is the composite homotopy morphism. -/
theorem TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap_comp
    {bound : Nat}
    {first second third :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (left :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        first
        second)
    (right :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        second
        third) :
    TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.comp
          left
          right) =
      TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap left ≫
        TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap right :=
  TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap_comp left right

/-- Rebounding a comparison-source bounded complex preserves its homotopy
object. -/
theorem TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject_rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy lower) :
    TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
        (complex.rebound bound_le) =
      TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
        complex :=
  TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject_rebound
    bound_le
    complex

/-- Rebounding a comparison-source bounded chain map preserves its homotopy
morphism. -/
theorem TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap_rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy lower}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap
        (hom.rebound bound_le) =
      TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom :=
  TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap_rebound
    bound_le
    hom

end AnalyticMotives
end LFunctions
end Boundary
