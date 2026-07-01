import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Exhaustions.Owner

/-!
# Contour deformations on analytic bulks

This file owns deformation data for contour systems.  Transport along
correspondences must later respect these deformations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A deformation between two contour chains, represented by a sweep core whose two
endpoint maps recover the source and target chains inside the compactification.
-/
structure AnalyticContourDeformation {X : AnalyticBulkCore}
    {B : AnalyticBoundarySystem X}
    (source target : AnalyticContourChain B) where
  sweep : AnalyticBulkCore
  sourceEndpoint : AnalyticBulkCoreHom source.domain sweep
  targetEndpoint : AnalyticBulkCoreHom target.domain sweep
  sweepMap : AnalyticBulkCoreHom sweep B.compactification.compactified
  source_commutes :
    AnalyticBulkCoreHom.comp sourceEndpoint sweepMap = source.compactifiedMap
  target_commutes :
    AnalyticBulkCoreHom.comp targetEndpoint sweepMap = target.compactifiedMap

namespace AnalyticContourDeformation

/-- The sweep core underlying a contour deformation. -/
def sweepCore {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {source target : AnalyticContourChain B}
    (D : AnalyticContourDeformation source target) : AnalyticBulkCore :=
  D.sweep

/-- The source endpoint commutative triangle of a contour deformation. -/
theorem source_triangle {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {source target : AnalyticContourChain B}
    (D : AnalyticContourDeformation source target) :
    AnalyticBulkCoreHom.comp D.sourceEndpoint D.sweepMap = source.compactifiedMap :=
  D.source_commutes

/-- The target endpoint commutative triangle of a contour deformation. -/
theorem target_triangle {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {source target : AnalyticContourChain B}
    (D : AnalyticContourDeformation source target) :
    AnalyticBulkCoreHom.comp D.targetEndpoint D.sweepMap = target.compactifiedMap :=
  D.target_commutes

end AnalyticContourDeformation

end AnalyticMotives
end LFunctions
end Boundary
