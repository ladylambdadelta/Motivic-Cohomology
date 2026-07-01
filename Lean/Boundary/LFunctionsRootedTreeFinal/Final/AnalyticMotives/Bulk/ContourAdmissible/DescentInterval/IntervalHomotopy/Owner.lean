import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.IntervalObject.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.DescentCovers.Owner

/-!
# Interval homotopy for analytic bulks

This file owns interval-homotopy data after the interval object and descent
cover calculus have been fixed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
An interval homotopy between paired maps of analytic bulk cores.  The homotopy
is a map out of the chosen interval core whose endpoint restrictions recover
the two maps.
-/
structure AnalyticIntervalHomotopy {X Y : AnalyticBulkCore}
    (I : AnalyticIntervalObject X)
    (f g : AnalyticBulkCoreHom X Y) where
  homotopyMap : AnalyticBulkCoreHom I.intervalCore Y
  zero_commutes :
    AnalyticBulkCoreHom.comp I.zero homotopyMap = f
  one_commutes :
    AnalyticBulkCoreHom.comp I.one homotopyMap = g

namespace AnalyticIntervalHomotopy

/-- The map out of the interval core carried by an interval homotopy. -/
def map {X Y : AnalyticBulkCore} {I : AnalyticIntervalObject X}
    {f g : AnalyticBulkCoreHom X Y}
    (H : AnalyticIntervalHomotopy I f g) :
    AnalyticBulkCoreHom I.intervalCore Y :=
  H.homotopyMap

/-- The zero endpoint equation of an interval homotopy. -/
theorem zero_endpoint {X Y : AnalyticBulkCore} {I : AnalyticIntervalObject X}
    {f g : AnalyticBulkCoreHom X Y}
    (H : AnalyticIntervalHomotopy I f g) :
    AnalyticBulkCoreHom.comp I.zero H.homotopyMap = f :=
  H.zero_commutes

/-- The one endpoint equation of an interval homotopy. -/
theorem one_endpoint {X Y : AnalyticBulkCore} {I : AnalyticIntervalObject X}
    {f g : AnalyticBulkCoreHom X Y}
    (H : AnalyticIntervalHomotopy I f g) :
    AnalyticBulkCoreHom.comp I.one H.homotopyMap = g :=
  H.one_commutes

end AnalyticIntervalHomotopy

end AnalyticMotives
end LFunctions
end Boundary
