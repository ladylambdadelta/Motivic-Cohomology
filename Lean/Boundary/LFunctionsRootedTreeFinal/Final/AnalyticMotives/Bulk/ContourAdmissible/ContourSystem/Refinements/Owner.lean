import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Deformations.Owner

/-!
# Contour refinements on analytic bulks

This file owns refinement data for contour systems.  Refinement covers are one
source of the conservative contour descent topology.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A refinement of one contour chain by another.  The domain map from the refined
chain to the coarse chain must commute with their maps into the compactified
bulk.
-/
structure AnalyticContourRefinement {X : AnalyticBulkCore}
    {B : AnalyticBoundarySystem X}
    (refined coarse : AnalyticContourChain B) where
  domainMap : AnalyticBulkCoreHom refined.domain coarse.domain
  commutes :
    AnalyticBulkCoreHom.comp domainMap coarse.compactifiedMap =
      refined.compactifiedMap

namespace AnalyticContourRefinement

/-- Reflexive refinement of a contour chain. -/
def refl {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    (C : AnalyticContourChain B) :
    AnalyticContourRefinement C C where
  domainMap := AnalyticBulkCoreHom.id C.domain
  commutes := AnalyticBulkCoreHom.id_comp C.compactifiedMap

/-- The domain map carried by a contour refinement. -/
def map {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {refined coarse : AnalyticContourChain B}
    (R : AnalyticContourRefinement refined coarse) :
    AnalyticBulkCoreHom refined.domain coarse.domain :=
  R.domainMap

/-- The defining commutative triangle for a contour refinement. -/
theorem map_commutes {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {refined coarse : AnalyticContourChain B}
    (R : AnalyticContourRefinement refined coarse) :
    AnalyticBulkCoreHom.comp R.domainMap coarse.compactifiedMap =
      refined.compactifiedMap :=
  R.commutes

/-- The map of a reflexive refinement is the identity map. -/
theorem refl_map {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    (C : AnalyticContourChain B) :
    (refl C).map = AnalyticBulkCoreHom.id C.domain :=
  rfl

end AnalyticContourRefinement

end AnalyticMotives
end LFunctions
end Boundary
