import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.IntervalObject.Owner

/-!
# Interval admissibility data

This file owns the selected analytic interval object.  The final interval
comparison with `A1` is downstream from the category construction.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Interval data selected for an analytic bulk core. -/
structure IntervalAdmissibility (X : AnalyticBulkCore) where
  interval : AnalyticIntervalObject X

namespace IntervalAdmissibility

/-- The selected interval object. -/
def data {X : AnalyticBulkCore}
    (I : IntervalAdmissibility X) :
    AnalyticIntervalObject X :=
  I.interval

end IntervalAdmissibility

end AnalyticMotives
end LFunctions
end Boundary
