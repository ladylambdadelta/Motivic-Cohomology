import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Faces.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Chains.Owner

/-!
# Residue maps for analytic bulks

This file owns boundary residue maps from bulk contour chains to contour chains
on boundary faces.  These maps are categorical boundary data, not scalar trace
contributions.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A categorical residue of a contour chain along a boundary face.  The residue is
represented by a core mapping both to the contour domain and to the boundary
stratum, with the two induced maps into the compactification agreeing.
-/
structure AnalyticResidueMap {X : AnalyticBulkCore}
    {B : AnalyticBoundarySystem X}
    (C : AnalyticContourChain B)
    (F : AnalyticBoundaryFace B.compactification) where
  residueCore : AnalyticBulkCore
  toContourDomain : AnalyticBulkCoreHom residueCore C.domain
  toFaceStratum : AnalyticBulkCoreHom residueCore F.stratum
  commutes :
    AnalyticBulkCoreHom.comp toContourDomain C.compactifiedMap =
      AnalyticBulkCoreHom.comp toFaceStratum F.inclusion

namespace AnalyticResidueMap

/-- The core carrying a categorical residue. -/
def core {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {C : AnalyticContourChain B} {F : AnalyticBoundaryFace B.compactification}
    (R : AnalyticResidueMap C F) : AnalyticBulkCore :=
  R.residueCore

/-- The defining commutative square for a categorical residue. -/
theorem square_commutes {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {C : AnalyticContourChain B} {F : AnalyticBoundaryFace B.compactification}
    (R : AnalyticResidueMap C F) :
    AnalyticBulkCoreHom.comp R.toContourDomain C.compactifiedMap =
      AnalyticBulkCoreHom.comp R.toFaceStratum F.inclusion :=
  R.commutes

end AnalyticResidueMap

end AnalyticMotives
end LFunctions
end Boundary
