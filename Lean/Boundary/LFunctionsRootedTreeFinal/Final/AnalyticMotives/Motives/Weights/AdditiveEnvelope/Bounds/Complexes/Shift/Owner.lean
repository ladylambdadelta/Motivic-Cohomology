import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Owner

/-!
# Shifts of bounded additive analytic complexes

The cochain shift of a bounded additive analytic complex is bounded by the same
numeric weight bound, since the object in degree `i` is the original object in
degree `i + n`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Shift a bounded additive analytic complex without changing its numeric weight bound. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shift
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (shift : ℤ) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound :=
  ⟨(CochainComplex.shiftFunctor TraceAnalyticAdditiveCategoryObject shift).obj
      complex.complex,
    fun degree => complex.degreeWeight_le (degree + shift)⟩

/-- The shifted bounded complex has the Mathlib shifted complex underneath. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shift_complex
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (shift : ℤ) :
    (complex.shift shift).complex =
      (CochainComplex.shiftFunctor TraceAnalyticAdditiveCategoryObject shift).obj
        complex.complex :=
  rfl

/-- The object in a shifted degree is the original object in degree `degree + shift`. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shift_objectAt
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (shift degree : ℤ) :
    (complex.shift shift).complex.objectAt degree =
      complex.complex.objectAt (degree + shift) :=
  rfl

/-- The shifted bounded complex has the original degree weight at degree `degree + shift`. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shift_degreeWeight
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (shift degree : ℤ) :
    (complex.shift shift).complex.degreeWeight degree =
      complex.complex.degreeWeight (degree + shift) :=
  rfl

/-- Shifted bounded degree objects have the original reindexed object underneath. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shift_degreeObject_object
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (shift degree : ℤ) :
    ((complex.shift shift).degreeObject degree).object =
      (complex.degreeObject (degree + shift)).object :=
  rfl

/-- The shifted bounded degree object satisfies the same numeric bound. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shift_degreeObject_weightLevel_le
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (shift degree : ℤ) :
    ((complex.shift shift).degreeObject degree).object.weightLevel ≤ bound :=
  ((complex.shift shift).degreeObject degree).weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
