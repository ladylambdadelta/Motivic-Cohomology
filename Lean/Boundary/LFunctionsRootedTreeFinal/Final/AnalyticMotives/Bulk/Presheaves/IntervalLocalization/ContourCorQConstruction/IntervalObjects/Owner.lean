import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.ContourCorQConstruction.Owner

/-!
# Constructed interval objects

This owner exposes the interval object attached to a contour-admissible bulk as
seen by constructed `ContourCor_Q` descent-local presheaves.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A bulk interval object as seen by a constructed descent-local presheaf. -/
structure ConstructedPresheafIntervalObject
    (F : ConstructedDescentLocalAnalyticPresheaf) where
  target : ContourAdmissibleBulk
  interval : AnalyticIntervalObject target.core

namespace ConstructedPresheafIntervalObject

/-- Build the constructed presheaf interval from a bulk's selected interval. -/
def selected
    (F : ConstructedDescentLocalAnalyticPresheaf)
    (X : ContourAdmissibleBulk) :
    ConstructedPresheafIntervalObject F where
  target := X
  interval := X.intervalObject

/-- The target bulk of a constructed presheaf interval object. -/
def targetBulk {F : ConstructedDescentLocalAnalyticPresheaf}
    (I : ConstructedPresheafIntervalObject F) :
    ContourAdmissibleBulk :=
  I.target

/-- The object-level analytic interval. -/
def objectInterval {F : ConstructedDescentLocalAnalyticPresheaf}
    (I : ConstructedPresheafIntervalObject F) :
    AnalyticIntervalObject I.target.core :=
  I.interval

/-- The core of the interval object. -/
def intervalCore {F : ConstructedDescentLocalAnalyticPresheaf}
    (I : ConstructedPresheafIntervalObject F) :
    AnalyticBulkCore :=
  I.interval.intervalCore

/-- The zero endpoint of the constructed interval object. -/
def zeroEndpoint {F : ConstructedDescentLocalAnalyticPresheaf}
    (I : ConstructedPresheafIntervalObject F) :
    AnalyticBulkCoreHom I.target.core I.interval.intervalCore :=
  I.interval.zero

/-- The one endpoint of the constructed interval object. -/
def oneEndpoint {F : ConstructedDescentLocalAnalyticPresheaf}
    (I : ConstructedPresheafIntervalObject F) :
    AnalyticBulkCoreHom I.target.core I.interval.intervalCore :=
  I.interval.one

/-- The projection from the constructed interval object. -/
def projection {F : ConstructedDescentLocalAnalyticPresheaf}
    (I : ConstructedPresheafIntervalObject F) :
    AnalyticBulkCoreHom I.interval.intervalCore I.target.core :=
  I.interval.projection

/-- The selected interval object has the selected target bulk. -/
theorem selected_targetBulk
    (F : ConstructedDescentLocalAnalyticPresheaf)
    (X : ContourAdmissibleBulk) :
    (selected F X).targetBulk = X :=
  rfl

end ConstructedPresheafIntervalObject

end AnalyticMotives
end LFunctions
end Boundary
