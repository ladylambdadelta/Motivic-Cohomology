import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Compactification.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Boundary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Contour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Residue.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Interval.Owner

/-!
# Admissibility package for contour bulks

This owner assembles the selected compactification, boundary, contour,
residue, descent, and interval components.  It is a library-development
checkpoint between the small analytic bulk core and the full category object.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Structured admissibility data selected for an analytic bulk core. -/
structure ContourBulkAdmissibility (X : AnalyticBulkCore) where
  compactification : CompactificationAdmissibility X
  boundary : BoundaryAdmissibility compactification
  contour : ContourSystemAdmissibility boundary
  residue : ResidueLedgerAdmissibility contour
  descent : DescentAdmissibility contour
  interval : IntervalAdmissibility X

namespace ContourBulkAdmissibility

/-- The full boundary system selected by admissibility data. -/
def boundarySystem {X : AnalyticBulkCore}
    (A : ContourBulkAdmissibility X) :
    AnalyticBoundarySystem X :=
  A.boundary.system

/-- The full contour system selected by admissibility data. -/
def contourSystem {X : AnalyticBulkCore}
    (A : ContourBulkAdmissibility X) :
    AnalyticContourSystem A.boundary.system :=
  A.contour.system

/-- The full residue ledger selected by admissibility data. -/
def residueLedger {X : AnalyticBulkCore}
    (A : ContourBulkAdmissibility X) :
    AnalyticResidueLedger A.contour.system :=
  A.residue.ledger

end ContourBulkAdmissibility

end AnalyticMotives
end LFunctions
end Boundary
