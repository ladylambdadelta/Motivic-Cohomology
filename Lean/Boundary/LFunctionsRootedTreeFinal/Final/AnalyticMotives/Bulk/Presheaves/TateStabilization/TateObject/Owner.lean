import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.Owner

/-!
# Analytic Tate object

This file owns the analytic Tate object after descent and interval
localization.  Tensor action and inversion are downstream.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
An analytic Tate object in the interval-local presheaf layer.  It is kept as a
selected interval-local object with a Tate name, not as a trace-weight label.
-/
structure AnalyticTateObject where
  carrier : IntervalLocalAnalyticPresheaf

namespace AnalyticTateObject

/-- The interval-local carrier of an analytic Tate object. -/
def underlying (T : AnalyticTateObject) :
    IntervalLocalAnalyticPresheaf :=
  T.carrier

/-- The descent-local presheaf underlying an analytic Tate object. -/
def descentLocal (T : AnalyticTateObject) :
    DescentLocalAnalyticPresheaf :=
  T.carrier.descentLocal

/-- The interval-locality data underlying an analytic Tate object. -/
def intervalLocality (T : AnalyticTateObject) :
    IntervalLocalObject T.carrier.descentLocal :=
  T.carrier.intervalLocality

end AnalyticTateObject

end AnalyticMotives
end LFunctions
end Boundary
