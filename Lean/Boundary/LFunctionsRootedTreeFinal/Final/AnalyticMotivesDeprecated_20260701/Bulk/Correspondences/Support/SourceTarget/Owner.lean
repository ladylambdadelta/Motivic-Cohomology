import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Products.Owner

/-!
# Source-target products for correspondence supports

This file owns the source-target product stage for analytic correspondence
supports.  Cycle-like support data is downstream from these products.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Source-target product data for two contour-admissible bulks.  The product is
taken at the bulk-core level and is used as the ambient core for cycle-like
correspondence supports.
-/
structure AnalyticSourceTargetProduct
    (X Y : ContourAdmissibleBulk) where
  productData : AnalyticBulkCoreProduct X.core Y.core

namespace AnalyticSourceTargetProduct

/-- The product core for a source-target pair. -/
def product {X Y : ContourAdmissibleBulk}
    (P : AnalyticSourceTargetProduct X Y) : AnalyticBulkCore :=
  P.productData.product

/-- Projection from the source-target product to the source bulk core. -/
def sourceProjection {X Y : ContourAdmissibleBulk}
    (P : AnalyticSourceTargetProduct X Y) :
    AnalyticBulkCoreHom P.product X.core :=
  P.productData.fst

/-- Projection from the source-target product to the target bulk core. -/
def targetProjection {X Y : ContourAdmissibleBulk}
    (P : AnalyticSourceTargetProduct X Y) :
    AnalyticBulkCoreHom P.product Y.core :=
  P.productData.snd

end AnalyticSourceTargetProduct

end AnalyticMotives
end LFunctions
end Boundary
