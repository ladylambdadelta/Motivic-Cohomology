import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.TateObject.Owner

/-!
# Tensor action of the analytic Tate object

This file owns the tensor action by the analytic Tate object.  Tate inversion
is downstream from this action.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Tensor action by an analytic Tate object on interval-local analytic presheaves.
This records the action on objects; coherence and monoidal localization belong
to later owner theorems.
-/
structure AnalyticTateTensorAction
    (T : AnalyticTateObject) where
  tensor :
    IntervalLocalAnalyticPresheaf → IntervalLocalAnalyticPresheaf

namespace AnalyticTateTensorAction

/-- Tensor an interval-local presheaf by the selected analytic Tate object. -/
def tensorObject {T : AnalyticTateObject}
    (A : AnalyticTateTensorAction T)
    (F : IntervalLocalAnalyticPresheaf) :
    IntervalLocalAnalyticPresheaf :=
  A.tensor F

/-- The descent-local presheaf underlying a Tate tensor result. -/
def tensorDescentLocal {T : AnalyticTateObject}
    (A : AnalyticTateTensorAction T)
    (F : IntervalLocalAnalyticPresheaf) :
    DescentLocalAnalyticPresheaf :=
  (A.tensorObject F).descentLocal

/-- The interval-locality data underlying a Tate tensor result. -/
def tensorLocality {T : AnalyticTateObject}
    (A : AnalyticTateTensorAction T)
    (F : IntervalLocalAnalyticPresheaf) :
    IntervalLocalObject (A.tensorObject F).descentLocal :=
  (A.tensorObject F).intervalLocality

end AnalyticTateTensorAction

end AnalyticMotives
end LFunctions
end Boundary
