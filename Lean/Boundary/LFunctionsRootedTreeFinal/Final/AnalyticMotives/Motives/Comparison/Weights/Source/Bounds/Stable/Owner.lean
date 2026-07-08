import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Shift.Owner

/-!
# Stable bounded source weights for analytic comparison

This file sends bounded additive-homotopy representatives through the stable
analytic Verdier quotient, producing concrete bounded representative objects
and maps in the analytic comparison source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Stable comparison-source object represented by a bounded additive analytic
complex. -/
def TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
      complex)

/-- Stable bounded objects are the comparison-source quotient images of bounded
homotopy objects. -/
theorem TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject_eq
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject complex =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) :=
  rfl

/-- Stable comparison-source morphism represented by a bounded chain map. -/
def TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject source ⟶
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject target :=
  TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom)

/-- Stable bounded maps are the comparison-source quotient images of bounded
homotopy maps. -/
theorem TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap hom) :=
  rfl

/-- The stable bounded map of an identity bounded chain map is identity. -/
theorem TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap_id
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.id
          complex) =
      𝟙
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex) :=
  Eq.trans
    (congrArg
      (fun hom =>
        TraceAnalyticDMgmComparisonSource.mapOf hom)
      (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap_id
        complex))
    (TraceAnalyticDMgmComparisonSource.quotientFunctor.map_id
      (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
        complex))

/-- The stable bounded map of a composite bounded chain map is the composite of
stable bounded maps. -/
theorem TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap_comp
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
    TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.comp
          left
          right) =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap left ≫
        TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap right :=
  Eq.trans
    (congrArg
      (fun hom =>
        TraceAnalyticDMgmComparisonSource.mapOf hom)
      (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap_comp
        left
        right))
    (TraceAnalyticDMgmComparisonSource.quotientFunctor.map_comp
      (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap left)
      (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap right))

/-- Stable comparison-source object represented by a shifted bounded additive
analytic complex. -/
def TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
      complex
      degree)

/-- Stable shifted bounded objects are quotient images of shifted bounded
homotopy objects. -/
theorem TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject_eq
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) :=
  rfl

/-- Stable comparison-source map represented by a shifted bounded chain map. -/
def TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        source
        degree ⟶
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        target
        degree :=
  TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
      hom
      degree)

/-- Stable shifted bounded maps are quotient images of shifted bounded homotopy
maps. -/
theorem TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
        hom
        degree =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
          hom
          degree) :=
  rfl

/-- The stable shifted bounded map of an identity bounded chain map is
identity. -/
theorem TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap_id
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.id
          complex)
        degree =
      𝟙
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) :=
  Eq.trans
    (congrArg
      (fun hom =>
        TraceAnalyticDMgmComparisonSource.mapOf hom)
      (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap_id
        complex
        degree))
    (TraceAnalyticDMgmComparisonSource.quotientFunctor.map_id
      (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
        complex
        degree))

/-- The stable shifted bounded map of a composite bounded chain map is the
composite of the shifted stable bounded maps. -/
theorem TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap_comp
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
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
        (TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.comp
          left
          right)
        degree =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
          left
          degree ≫
        TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
          right
          degree :=
  Eq.trans
    (congrArg
      (fun hom =>
        TraceAnalyticDMgmComparisonSource.mapOf hom)
      (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap_comp
        left
        right
        degree))
    (TraceAnalyticDMgmComparisonSource.quotientFunctor.map_comp
      (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
        left
        degree)
      (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
        right
        degree))

/-- Rebounding a bounded representative preserves its stable comparison-source
object. -/
theorem TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject_rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy lower) :
    TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
        (complex.rebound bound_le) =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
        complex :=
  congrArg
    TraceAnalyticDMgmComparisonSource.objectOf
    (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject_rebound
      bound_le
      complex)

/-- Rebounding a bounded chain map preserves its stable comparison-source
morphism. -/
theorem TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap_rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy lower}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap
        (hom.rebound bound_le) =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom :=
  congrArg
    TraceAnalyticDMgmComparisonSource.mapOf
    (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap_rebound
      bound_le
      hom)

/-- Rebounding a bounded representative preserves its shifted stable
comparison-source object. -/
theorem TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject_rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy lower)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        (complex.rebound bound_le)
        degree =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  congrArg
    TraceAnalyticDMgmComparisonSource.objectOf
    (Eq.trans
      (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject_eq
        (complex.rebound bound_le)
        degree)
      (Eq.trans
        (congrArg
          (fun object =>
            TraceAnalyticAdditiveHomotopyCategory.shiftedObject
              object
              degree)
          (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject_rebound
            bound_le
            complex))
        (Eq.symm
          (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject_eq
            complex
            degree))))

/-- Rebounding a bounded chain map preserves its shifted stable
comparison-source morphism. -/
theorem TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap_rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy lower}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
        (hom.rebound bound_le)
        degree =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
        hom
        degree :=
  congrArg
    TraceAnalyticDMgmComparisonSource.mapOf
    (Eq.trans
      (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap_eq
        (hom.rebound bound_le)
        degree)
      (Eq.trans
        (congrArg
          (fun map =>
            TraceAnalyticAdditiveHomotopyCategory.shiftedMap
              map
              degree)
          (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyMap_rebound
            bound_le
            hom))
        (Eq.symm
          (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap_eq
            hom
            degree))))

end AnalyticMotives
end LFunctions
end Boundary
