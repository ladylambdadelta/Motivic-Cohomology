import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Maps.Owner
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Products of analytic bulk cores

This file owns product objects for analytic bulk cores.  Product data is needed
before support objects for contour-compatible correspondences can live over
source-target products.

Foundational source: mathlib's binary product API supplies the categorical
shape used by correspondence supports.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Product data for analytic bulk cores.  This records the source-target product
object and its two projections at the paired-map level.  The universal property
belongs here only after the ordinary map category has been promoted from paired
maps to the chosen compatible-map category.
-/
structure AnalyticBulkCoreProduct (X Y : AnalyticBulkCore) where
  product : AnalyticBulkCore
  fst : AnalyticBulkCoreHom product X
  snd : AnalyticBulkCoreHom product Y

namespace AnalyticBulkCoreProduct

/-- The first projection of analytic bulk core product data. -/
def left {X Y : AnalyticBulkCore} (P : AnalyticBulkCoreProduct X Y) :
    AnalyticBulkCoreHom P.product X :=
  P.fst

/-- The second projection of analytic bulk core product data. -/
def right {X Y : AnalyticBulkCore} (P : AnalyticBulkCoreProduct X Y) :
    AnalyticBulkCoreHom P.product Y :=
  P.snd

end AnalyticBulkCoreProduct

end AnalyticMotives
end LFunctions
end Boundary
