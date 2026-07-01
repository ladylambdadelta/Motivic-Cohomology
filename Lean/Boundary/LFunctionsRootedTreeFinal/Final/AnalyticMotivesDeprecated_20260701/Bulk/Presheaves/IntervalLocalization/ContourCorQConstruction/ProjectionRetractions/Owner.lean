import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.ContourCorQConstruction.IntervalObjects.Owner

/-!
# Constructed interval projection retractions

This owner records the concrete endpoint-projection equations supplied by the
bulk interval object.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projection-retraction data for a constructed presheaf interval object. -/
structure ConstructedIntervalProjectionRetraction
    {F : ConstructedDescentLocalAnalyticPresheaf}
    (I : ConstructedPresheafIntervalObject F) where
  zero_projection :
    AnalyticBulkCoreHom.comp I.zeroEndpoint I.projection =
      AnalyticBulkCoreHom.id I.target.core
  one_projection :
    AnalyticBulkCoreHom.comp I.oneEndpoint I.projection =
      AnalyticBulkCoreHom.id I.target.core

namespace ConstructedIntervalProjectionRetraction

/-- The projection-retraction data supplied by the interval object itself. -/
def fromInterval {F : ConstructedDescentLocalAnalyticPresheaf}
    (I : ConstructedPresheafIntervalObject F) :
    ConstructedIntervalProjectionRetraction I where
  zero_projection := I.interval.zero_projection
  one_projection := I.interval.one_projection

/-- The zero endpoint followed by projection is the identity. -/
theorem zero_projection_eq {F : ConstructedDescentLocalAnalyticPresheaf}
    {I : ConstructedPresheafIntervalObject F}
    (R : ConstructedIntervalProjectionRetraction I) :
    AnalyticBulkCoreHom.comp I.zeroEndpoint I.projection =
      AnalyticBulkCoreHom.id I.target.core :=
  R.zero_projection

/-- The one endpoint followed by projection is the identity. -/
theorem one_projection_eq {F : ConstructedDescentLocalAnalyticPresheaf}
    {I : ConstructedPresheafIntervalObject F}
    (R : ConstructedIntervalProjectionRetraction I) :
    AnalyticBulkCoreHom.comp I.oneEndpoint I.projection =
      AnalyticBulkCoreHom.id I.target.core :=
  R.one_projection

end ConstructedIntervalProjectionRetraction

end AnalyticMotives
end LFunctions
end Boundary
