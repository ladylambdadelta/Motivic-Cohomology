import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Homotopy.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Shift.Owner

/-!
# Shifted bounded source weights for analytic comparison

This file exposes shifts of bounded additive-homotopy source objects and maps
under comparison-facing names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Shift a comparison-source bounded homotopy object. -/
def TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObject
    complex
    degree

/-- Shifted comparison-source bounded homotopy objects are shifted ordinary
bounded homotopy objects. -/
theorem TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject_eq
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
        complex
        degree =
      TraceAnalyticAdditiveHomotopyCategory.shiftedObject
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex)
        degree :=
  TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObject_eq
    complex
    degree

/-- Shift a comparison-source bounded homotopy map. -/
def TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
        source
        degree ⟶
      TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
        target
        degree :=
  TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap
    hom
    degree

/-- Shifted comparison-source bounded homotopy maps are shifted ordinary
bounded homotopy maps. -/
theorem TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
        hom
        degree =
      TraceAnalyticAdditiveHomotopyCategory.shiftedMap
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom)
        degree :=
  TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap_eq
    hom
    degree

/-- Shifting the identity map of a bounded representative gives the identity on
the shifted comparison-source bounded object. -/
theorem TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap_id
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.id
          complex)
        degree =
      𝟙
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) :=
  TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap_id
    complex
    degree

/-- Shifting a composite of bounded-representative maps gives the composite of
the shifted comparison-source maps. -/
theorem TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap_comp
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
        third)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.comp
          left
          right)
        degree =
      TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
          left
          degree ≫
        TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
          right
          degree :=
  TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap_comp
    left
    right
    degree

end AnalyticMotives
end LFunctions
end Boundary
