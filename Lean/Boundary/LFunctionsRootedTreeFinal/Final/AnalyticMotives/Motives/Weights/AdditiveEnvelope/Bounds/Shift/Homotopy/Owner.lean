import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Shift.Functoriality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Homotopy.Owner

/-!
# Shifts of bounded-weight homotopy objects

Bounded additive analytic complexes determine homotopy-category objects, and
the inherited integer shift functors act on those objects and their maps.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Shift the homotopy-category object represented by a bounded complex. -/
def TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObject
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.shiftedObject
    (TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject complex)
    degree

/-- Shift the homotopy-category map represented by a bounded-complex chain map. -/
def TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObject
        source
        degree ⟶
      TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObject
        target
        degree :=
  TraceAnalyticAdditiveHomotopyCategory.shiftedMap
    (TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap hom)
    degree

/-- Shifted bounded objects are shifted ordinary bounded homotopy objects. -/
theorem TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObject_eq
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObject
        complex
        degree =
      TraceAnalyticAdditiveHomotopyCategory.shiftedObject
        (TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject complex)
        degree :=
  rfl

/-- Shifted bounded maps are shifted ordinary bounded homotopy maps. -/
theorem TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap hom degree =
      TraceAnalyticAdditiveHomotopyCategory.shiftedMap
        (TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap hom)
        degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
