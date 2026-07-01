import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.TensorAction.Owner

/-!
# Inverting the analytic Tate object

This file owns Tate stabilization by inverting the analytic Tate object under
its tensor action.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Inversion data for the analytic Tate action.  It records an inverse shift
operation together with the left and right comparison objects produced by
composing the Tate action and inverse shift.
-/
structure AnalyticTateInversion
    {T : AnalyticTateObject}
    (A : AnalyticTateTensorAction T) where
  inverse :
    IntervalLocalAnalyticPresheaf → IntervalLocalAnalyticPresheaf
  leftComparison :
    (F : IntervalLocalAnalyticPresheaf) →
      A.tensor (inverse F) = F
  rightComparison :
    (F : IntervalLocalAnalyticPresheaf) →
      inverse (A.tensor F) = F

namespace AnalyticTateInversion

/-- The inverse Tate shift selected by Tate-inversion data. -/
def inverseObject {T : AnalyticTateObject}
    {A : AnalyticTateTensorAction T}
    (I : AnalyticTateInversion A)
    (F : IntervalLocalAnalyticPresheaf) :
    IntervalLocalAnalyticPresheaf :=
  I.inverse F

/-- The Tate tensor of the inverse shift. -/
def tensorInverseObject {T : AnalyticTateObject}
    {A : AnalyticTateTensorAction T}
    (I : AnalyticTateInversion A)
    (F : IntervalLocalAnalyticPresheaf) :
    IntervalLocalAnalyticPresheaf :=
  A.tensorObject (I.inverseObject F)

/-- The inverse shift of a Tate tensor. -/
def inverseTensorObject {T : AnalyticTateObject}
    {A : AnalyticTateTensorAction T}
    (I : AnalyticTateInversion A)
    (F : IntervalLocalAnalyticPresheaf) :
    IntervalLocalAnalyticPresheaf :=
  I.inverseObject (A.tensorObject F)

/-- The left inverse comparison for Tate inversion. -/
theorem leftComparison_eq {T : AnalyticTateObject}
    {A : AnalyticTateTensorAction T}
    (I : AnalyticTateInversion A)
    (F : IntervalLocalAnalyticPresheaf) :
    A.tensor (I.inverse F) = F :=
  I.leftComparison F

/-- The Tate tensor of the inverse shift agrees with the original object. -/
theorem tensorInverse_eq {T : AnalyticTateObject}
    {A : AnalyticTateTensorAction T}
    (I : AnalyticTateInversion A)
    (F : IntervalLocalAnalyticPresheaf) :
    I.tensorInverseObject F = F :=
  I.leftComparison F

/-- The right inverse comparison for Tate inversion. -/
theorem rightComparison_eq {T : AnalyticTateObject}
    {A : AnalyticTateTensorAction T}
    (I : AnalyticTateInversion A)
    (F : IntervalLocalAnalyticPresheaf) :
    I.inverse (A.tensor F) = F :=
  I.rightComparison F

/-- The inverse shift of a Tate tensor agrees with the original object. -/
theorem inverseTensor_eq {T : AnalyticTateObject}
    {A : AnalyticTateTensorAction T}
    (I : AnalyticTateInversion A)
    (F : IntervalLocalAnalyticPresheaf) :
    I.inverseTensorObject F = F :=
  I.rightComparison F

end AnalyticTateInversion

end AnalyticMotives
end LFunctions
end Boundary
