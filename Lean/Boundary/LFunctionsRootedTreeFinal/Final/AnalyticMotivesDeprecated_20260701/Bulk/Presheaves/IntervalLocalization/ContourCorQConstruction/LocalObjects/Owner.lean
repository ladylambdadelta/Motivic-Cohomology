import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.ContourCorQConstruction.ProjectionRetractions.Owner

/-!
# Constructed interval-local objects

This owner records interval-locality data for constructed descent-local
`ContourCor_Q` presheaves at the level currently supplied by the bulk interval
calculus: endpoint projection retractions.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Constructed interval-locality data over one chosen interval object. -/
structure ConstructedIntervalLocalObject
    (F : ConstructedDescentLocalAnalyticPresheaf) where
  interval : ConstructedPresheafIntervalObject F
  retraction : ConstructedIntervalProjectionRetraction interval

namespace ConstructedIntervalLocalObject

/-- Build interval-locality from the selected interval of a bulk. -/
def selected
    (F : ConstructedDescentLocalAnalyticPresheaf)
    (X : ContourAdmissibleBulk) :
    ConstructedIntervalLocalObject F where
  interval := ConstructedPresheafIntervalObject.selected F X
  retraction :=
    ConstructedIntervalProjectionRetraction.fromInterval
      (ConstructedPresheafIntervalObject.selected F X)

/-- The interval object carried by constructed interval-locality. -/
def intervalObject {F : ConstructedDescentLocalAnalyticPresheaf}
    (L : ConstructedIntervalLocalObject F) :
    ConstructedPresheafIntervalObject F :=
  L.interval

/-- The projection-retraction data carried by constructed interval-locality. -/
def projectionRetraction {F : ConstructedDescentLocalAnalyticPresheaf}
    (L : ConstructedIntervalLocalObject F) :
    ConstructedIntervalProjectionRetraction L.interval :=
  L.retraction

/-- The zero endpoint followed by projection is the identity. -/
theorem zero_projection_eq {F : ConstructedDescentLocalAnalyticPresheaf}
    (L : ConstructedIntervalLocalObject F) :
    AnalyticBulkCoreHom.comp
        L.intervalObject.zeroEndpoint L.intervalObject.projection =
      AnalyticBulkCoreHom.id L.intervalObject.target.core :=
  ConstructedIntervalProjectionRetraction.zero_projection_eq
    L.projectionRetraction

/-- The one endpoint followed by projection is the identity. -/
theorem one_projection_eq {F : ConstructedDescentLocalAnalyticPresheaf}
    (L : ConstructedIntervalLocalObject F) :
    AnalyticBulkCoreHom.comp
        L.intervalObject.oneEndpoint L.intervalObject.projection =
      AnalyticBulkCoreHom.id L.intervalObject.target.core :=
  ConstructedIntervalProjectionRetraction.one_projection_eq
    L.projectionRetraction

end ConstructedIntervalLocalObject

/-- A constructed descent-local presheaf equipped with interval-locality. -/
structure ConstructedIntervalLocalAnalyticPresheaf where
  descentLocal : ConstructedDescentLocalAnalyticPresheaf
  intervalLocality : ConstructedIntervalLocalObject descentLocal

namespace ConstructedIntervalLocalAnalyticPresheaf

/-- The underlying constructed descent-local presheaf. -/
def underlying (F : ConstructedIntervalLocalAnalyticPresheaf) :
    ConstructedDescentLocalAnalyticPresheaf :=
  F.descentLocal

/-- The constructed interval-locality data. -/
def locality (F : ConstructedIntervalLocalAnalyticPresheaf) :
    ConstructedIntervalLocalObject F.descentLocal :=
  F.intervalLocality

end ConstructedIntervalLocalAnalyticPresheaf

end AnalyticMotives
end LFunctions
end Boundary
