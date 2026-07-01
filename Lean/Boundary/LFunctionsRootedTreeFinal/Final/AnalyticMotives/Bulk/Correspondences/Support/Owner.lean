import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.SourceTarget.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.CycleLike.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.Finiteness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.Composition.Owner

/-!
# Analytic correspondence supports

Correspondence supports own the finite/proper analytic support relation between
two contour-admissible bulks.  Contour transport and residue compatibility are
separate layers so composition can be proved one component at a time.

Dependency order: source-target products, cycle-like supports, proper/finite
conditions, then support composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A finite/proper analytic correspondence support from `X` to `Y`.  Transport of
contours and residue compatibility are intentionally not fields here; they are
separate owner layers so the composition proof can be built component by
component.
-/
structure AnalyticCorrespondenceSupport
    (X Y : ContourAdmissibleBulk) where
  sourceTarget : AnalyticSourceTargetProduct X Y
  cycleLike : AnalyticCycleLikeSupport sourceTarget
  finiteness : AnalyticSupportFiniteness cycleLike

namespace AnalyticCorrespondenceSupport

/-- The source-target product data underlying a correspondence support. -/
def sourceTargetData {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    AnalyticSourceTargetProduct X Y :=
  S.sourceTarget

/-- The cycle-like support data underlying a correspondence support. -/
def cycleLikeData {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    AnalyticCycleLikeSupport S.sourceTarget :=
  S.cycleLike

/-- The proper/finite data underlying a correspondence support. -/
def finitenessData {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    AnalyticSupportFiniteness S.cycleLike :=
  S.finiteness

/-- The source-target product core of an analytic correspondence support. -/
def productCore {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) : AnalyticBulkCore :=
  S.sourceTarget.product

/-- The support core of an analytic correspondence support. -/
def supportCore {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) : AnalyticBulkCore :=
  S.cycleLike.supportCore

/-- The map from the support core into the source-target product core. -/
def mapToProduct {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    AnalyticBulkCoreHom S.supportCore S.productCore :=
  S.cycleLike.mapToProduct

/-- The induced map from a correspondence support to its source bulk core. -/
def mapToSource {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    AnalyticBulkCoreHom S.supportCore X.core :=
  AnalyticCycleLikeSupport.mapToSource S.cycleLike

/-- The induced map from a correspondence support to its target bulk core. -/
def mapToTarget {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    AnalyticBulkCoreHom S.supportCore Y.core :=
  AnalyticCycleLikeSupport.mapToTarget S.cycleLike

/-- The support map over the source is proper. -/
theorem proper_over_source {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    AlgebraicGeometry.IsProper (S.mapToSource).baseMap :=
  AnalyticSupportFiniteness.proper_source S.finiteness

/-- The support map over the target is finite. -/
theorem finite_over_target {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) :
    AlgebraicGeometry.IsFinite (S.mapToTarget).baseMap :=
  AnalyticSupportFiniteness.finite_target S.finiteness

end AnalyticCorrespondenceSupport

end AnalyticMotives
end LFunctions
end Boundary
