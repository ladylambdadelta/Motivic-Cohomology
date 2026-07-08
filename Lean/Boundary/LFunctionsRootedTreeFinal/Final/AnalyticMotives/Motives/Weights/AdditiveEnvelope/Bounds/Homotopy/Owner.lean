import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Maps.Owner

/-!
# Bounded-weight objects in the additive analytic homotopy category

A bounded additive analytic complex determines an object of the additive
analytic homotopy category by applying the standard homotopy quotient functor.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The homotopy-category object represented by a bounded additive analytic complex. -/
def TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.objectOf complex.complex

/-- A chain map between bounded complexes maps to a homotopy-category morphism. -/
def TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject source ⟶
      TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject target :=
  TraceAnalyticAdditiveHomotopyCategory.mapOf hom

/-- The bounded homotopy object is the ordinary homotopy image of the underlying complex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject_eq
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound) :
    TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject complex =
      TraceAnalyticAdditiveHomotopyCategory.objectOf complex.complex :=
  rfl

/-- The bounded homotopy map is the ordinary homotopy image of the underlying chain map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap hom =
      TraceAnalyticAdditiveHomotopyCategory.mapOf hom :=
  rfl

/-- The bounded homotopy map of an identity chain map is the identity morphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap_id
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound) :
    TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap
        (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id complex) =
      𝟙 (TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject complex) :=
  TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.map_id
    complex.complex

/-- The bounded homotopy map of a composite chain map is the composite homotopy map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap_comp
    {bound : Nat}
    {first second third :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (left :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom first second)
    (right :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom second third) :
    TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap
        (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp left right) =
      TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap left ≫
        TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap right :=
  TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.map_comp
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
