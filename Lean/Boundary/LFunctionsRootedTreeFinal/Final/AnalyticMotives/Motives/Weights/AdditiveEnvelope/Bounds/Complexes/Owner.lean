import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Complexes.Owner

/-!
# Bounded-weight additive analytic complexes

An additive analytic complex is bounded by `bound` when every degree object has
weight level at most `bound`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- An additive analytic complex is degreewise bounded by a weight level. -/
def TraceAnalyticAdditiveCochainComplex.IsWeightBoundedBy
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bound : Nat) :
    Prop :=
  (degree : ℤ) →
    complex.degreeWeight degree ≤ bound

/-- Additive analytic complexes whose every degree has weight at most `bound`. -/
abbrev TraceAnalyticAdditiveCochainComplex.WeightBoundedBy
    (bound : Nat) :=
  { complex : TraceAnalyticAdditiveCochainComplex //
      complex.IsWeightBoundedBy bound }

/-- The underlying complex of a bounded additive analytic complex. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.complex
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound) :
    TraceAnalyticAdditiveCochainComplex :=
  complex.val

/-- A bounded additive analytic complex supplies a degreewise weight bound. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.degreeWeight_le
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    complex.complex.degreeWeight degree ≤ bound :=
  complex.property degree

/-- The degree object of a bounded complex is a bounded finite trace family. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.degreeObject
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject.BoundedBy bound :=
  ⟨complex.complex.objectAt degree,
    Eq.subst
      (motive := fun weight =>
        weight ≤ bound)
      (TraceAnalyticAdditiveCochainComplex.degreeWeight_eq
        complex.complex
        degree)
      (complex.degreeWeight_le degree)⟩

/-- The bounded degree object has the underlying object of the complex in that degree. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.degreeObject_object
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    (complex.degreeObject degree).object =
      complex.complex.objectAt degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
