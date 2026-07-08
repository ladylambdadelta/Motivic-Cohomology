import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Maps.Owner

/-!
# Shifts of bounded additive analytic chain maps

The cochain shift functor sends a bounded chain map to a bounded chain map
between the shifted bounded source and target complexes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Shift a bounded chain map between shifted bounded complexes. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.shift
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom
      (source.shift shift)
      (target.shift shift) :=
  (CochainComplex.shiftFunctor TraceAnalyticAdditiveCategoryObject shift).map
    hom

/-- The shifted bounded map is the Mathlib shifted chain map. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.shift_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    hom.shift shift =
      (CochainComplex.shiftFunctor TraceAnalyticAdditiveCategoryObject shift).map
        hom :=
  rfl

/-- The component of a shifted bounded map is the original component in the reindexed degree. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.shift_f
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift degree : ℤ) :
    (hom.shift shift).f degree =
      hom.f (degree + shift) :=
  rfl

/-- Shifting the identity bounded map is the identity on the shifted bounded complex. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.shift_id
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (shift : ℤ) :
    (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id complex).shift shift =
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id
        (complex.shift shift) :=
  rfl

/-- Shifting a composite bounded map gives the composite of shifted bounded maps. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.shift_comp
    {bound : Nat}
    {first second third :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (left :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom first second)
    (right :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom second third)
    (shift : ℤ) :
    (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp left right).shift
        shift =
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp
        (left.shift shift)
        (right.shift shift) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
