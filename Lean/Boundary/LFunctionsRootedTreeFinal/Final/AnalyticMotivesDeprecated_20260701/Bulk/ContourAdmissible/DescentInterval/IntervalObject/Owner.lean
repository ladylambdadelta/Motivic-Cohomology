import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Owner

/-!
# Analytic interval objects

This file owns the interval-object interface for analytic bulks.  It records
the interval as part of the analytic bulk calculus without choosing a concrete
model too early.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A relative analytic interval object over a bulk core.  The projection retracts
both endpoints back to the source core, matching the role of an interval before
a concrete analytic model is chosen.
-/
structure AnalyticIntervalObject (X : AnalyticBulkCore) where
  intervalCore : AnalyticBulkCore
  zero : AnalyticBulkCoreHom X intervalCore
  one : AnalyticBulkCoreHom X intervalCore
  projection : AnalyticBulkCoreHom intervalCore X
  zero_projection :
    AnalyticBulkCoreHom.comp zero projection = AnalyticBulkCoreHom.id X
  one_projection :
    AnalyticBulkCoreHom.comp one projection = AnalyticBulkCoreHom.id X

namespace AnalyticIntervalObject

/-- The core carrying a relative analytic interval. -/
def core {X : AnalyticBulkCore} (I : AnalyticIntervalObject X) :
    AnalyticBulkCore :=
  I.intervalCore

/-- The zero endpoint of a relative analytic interval. -/
def zeroEndpoint {X : AnalyticBulkCore} (I : AnalyticIntervalObject X) :
    AnalyticBulkCoreHom X I.intervalCore :=
  I.zero

/-- The one endpoint of a relative analytic interval. -/
def oneEndpoint {X : AnalyticBulkCore} (I : AnalyticIntervalObject X) :
    AnalyticBulkCoreHom X I.intervalCore :=
  I.one

end AnalyticIntervalObject

end AnalyticMotives
end LFunctions
end Boundary
