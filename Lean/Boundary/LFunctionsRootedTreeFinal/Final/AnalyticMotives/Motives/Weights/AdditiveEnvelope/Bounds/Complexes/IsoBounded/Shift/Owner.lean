import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.Owner

/-!
# Shifts of degreewise iso-bounded additive analytic complexes

Degreewise iso-boundedness is stable under cochain shift.  The witness in
shifted degree `i` is the original witness in degree `i + n`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Shift a degreewise iso-bounded additive analytic complex by reindexing degrees. -/
def TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy.shift
    {complex : TraceAnalyticAdditiveCochainComplex}
    {bound : Nat}
    (isoBounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
        complex
        bound)
    (shift : ℤ) :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
      ((CochainComplex.shiftFunctor TraceAnalyticAdditiveCategoryObject shift).obj
        complex)
      bound where
  degreeIsoBounded degree := isoBounded.degreeObject (degree + shift)

/-- The shifted iso-bounded witness in degree `i` is the old witness in degree `i + n`. -/
theorem TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy.shift_degreeObject
    {complex : TraceAnalyticAdditiveCochainComplex}
    {bound : Nat}
    (isoBounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
        complex
        bound)
    (shift degree : ℤ) :
    (isoBounded.shift shift).degreeObject degree =
      isoBounded.degreeObject (degree + shift) :=
  rfl

/-- The shifted iso-bounded representative satisfies the same numeric bound. -/
theorem TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy.shift_degreeObject_weightLevel_le
    {complex : TraceAnalyticAdditiveCochainComplex}
    {bound : Nat}
    (isoBounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
        complex
        bound)
    (shift degree : ℤ) :
    ((isoBounded.shift shift).degreeObject degree).boundedRepresentative.object.weightLevel ≤
      bound :=
  (isoBounded.degreeObject (degree + shift)).representative_weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
