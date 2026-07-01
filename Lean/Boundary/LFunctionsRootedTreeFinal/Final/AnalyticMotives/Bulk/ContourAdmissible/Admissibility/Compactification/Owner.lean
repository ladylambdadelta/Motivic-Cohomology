import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Compactification.Owner

/-!
# Compactification admissibility data

This file owns the compactification component of a contour-admissible analytic
bulk.  It is a data layer over the concrete compactification owner, not a
predicate standing in for missing theorems.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compactification data selected for an analytic bulk core. -/
structure CompactificationAdmissibility (X : AnalyticBulkCore) where
  compactification : AnalyticBulkCompactification X

namespace CompactificationAdmissibility

/-- The selected compactification. -/
def data {X : AnalyticBulkCore}
    (A : CompactificationAdmissibility X) :
    AnalyticBulkCompactification X :=
  A.compactification

/-- The compactified target core. -/
def target {X : AnalyticBulkCore}
    (A : CompactificationAdmissibility X) :
    AnalyticBulkCore :=
  A.compactification.target

/-- The open map into the compactification. -/
def openMap {X : AnalyticBulkCore}
    (A : CompactificationAdmissibility X) :
    AnalyticBulkCoreHom X A.target :=
  A.compactification.inclusion

end CompactificationAdmissibility

end AnalyticMotives
end LFunctions
end Boundary
