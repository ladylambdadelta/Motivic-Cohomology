import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.SourceTarget.Owner

/-!
# Cycle-like analytic support data

This file owns the cycle-like support data inside source-target products.
Properness, finiteness, and contour transport are downstream from this support
data.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Cycle-like support data inside a source-target product.  This is the analytic
analogue of placing a finite-correspondence support inside `X × Y`; finiteness
and properness are added in the next owner layer.
-/
structure AnalyticCycleLikeSupport {X Y : ContourAdmissibleBulk}
    (P : AnalyticSourceTargetProduct X Y) where
  supportCore : AnalyticBulkCore
  supportMap : AnalyticBulkCoreHom supportCore P.product

namespace AnalyticCycleLikeSupport

/-- The core underlying a cycle-like support. -/
def core {X Y : ContourAdmissibleBulk}
    {P : AnalyticSourceTargetProduct X Y}
    (Z : AnalyticCycleLikeSupport P) : AnalyticBulkCore :=
  Z.supportCore

/-- The map from a cycle-like support into the source-target product. -/
def mapToProduct {X Y : ContourAdmissibleBulk}
    {P : AnalyticSourceTargetProduct X Y}
    (Z : AnalyticCycleLikeSupport P) :
    AnalyticBulkCoreHom Z.supportCore P.product :=
  Z.supportMap

/-- The induced map from a cycle-like support to the source bulk core. -/
def mapToSource {X Y : ContourAdmissibleBulk}
    {P : AnalyticSourceTargetProduct X Y}
    (Z : AnalyticCycleLikeSupport P) :
    AnalyticBulkCoreHom Z.supportCore X.core :=
  AnalyticBulkCoreHom.comp Z.supportMap P.sourceProjection

/-- The induced map from a cycle-like support to the target bulk core. -/
def mapToTarget {X Y : ContourAdmissibleBulk}
    {P : AnalyticSourceTargetProduct X Y}
    (Z : AnalyticCycleLikeSupport P) :
    AnalyticBulkCoreHom Z.supportCore Y.core :=
  AnalyticBulkCoreHom.comp Z.supportMap P.targetProjection

end AnalyticCycleLikeSupport

end AnalyticMotives
end LFunctions
end Boundary
