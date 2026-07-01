import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.IntervalObject.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.Owner

/-!
# Interval object for presheaf localization

This file owns the interval object as seen by descent-local transfer
presheaves.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A presheaf-level interval object for a descent-local analytic presheaf.  It
uses the interval object attached to the target contour-admissible bulk rather
than choosing a concrete analytic interval model.
-/
structure PresheafIntervalObject
    (F : DescentLocalAnalyticPresheaf) where
  target : ContourAdmissibleBulk
  interval : AnalyticIntervalObject target.core

namespace PresheafIntervalObject

/-- The target bulk over which the interval object lives. -/
def targetBulk {F : DescentLocalAnalyticPresheaf}
    (I : PresheafIntervalObject F) : ContourAdmissibleBulk :=
  I.target

/-- The object-level interval selected for presheaf interval localization. -/
def objectInterval {F : DescentLocalAnalyticPresheaf}
    (I : PresheafIntervalObject F) :
    AnalyticIntervalObject I.target.core :=
  I.interval

/-- The interval core used by a presheaf-level interval object. -/
def intervalCore {F : DescentLocalAnalyticPresheaf}
    (I : PresheafIntervalObject F) :
    AnalyticBulkCore :=
  I.interval.intervalCore

/-- The zero endpoint of a presheaf-level interval object. -/
def zeroEndpoint {F : DescentLocalAnalyticPresheaf}
    (I : PresheafIntervalObject F) :
    AnalyticBulkCoreHom I.target.core I.interval.intervalCore :=
  I.interval.zero

/-- The one endpoint of a presheaf-level interval object. -/
def oneEndpoint {F : DescentLocalAnalyticPresheaf}
    (I : PresheafIntervalObject F) :
    AnalyticBulkCoreHom I.target.core I.interval.intervalCore :=
  I.interval.one

/-- The projection from a presheaf-level interval object. -/
def projection {F : DescentLocalAnalyticPresheaf}
    (I : PresheafIntervalObject F) :
    AnalyticBulkCoreHom I.interval.intervalCore I.target.core :=
  I.interval.projection

/-- The zero endpoint followed by projection is the identity. -/
theorem zero_projection {F : DescentLocalAnalyticPresheaf}
    (I : PresheafIntervalObject F) :
    AnalyticBulkCoreHom.comp I.interval.zero I.interval.projection =
      AnalyticBulkCoreHom.id I.target.core :=
  I.interval.zero_projection

/-- The one endpoint followed by projection is the identity. -/
theorem one_projection {F : DescentLocalAnalyticPresheaf}
    (I : PresheafIntervalObject F) :
    AnalyticBulkCoreHom.comp I.interval.one I.interval.projection =
      AnalyticBulkCoreHom.id I.target.core :=
  I.interval.one_projection

end PresheafIntervalObject

end AnalyticMotives
end LFunctions
end Boundary
