import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Deformations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.Pushforward.Owner

/-!
# Deformation compatibility for contour transport

This file owns compatibility between correspondence contour pushforward and
allowed contour deformations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Compatibility of contour pushforward with the chosen deformation calculus.
Every source deformation is sent to a target deformation between the pushed
stages.
-/
structure AnalyticTransportDeformationCompatibility
    {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (P : AnalyticContourPushforward S) where
  deformationMap :
    {s t : X.contour.exhaustion.Stage} →
      X.contour.DeformationIndex s t →
        Y.contour.DeformationIndex (P.stageMap s) (P.stageMap t)

namespace AnalyticTransportDeformationCompatibility

/-- The target deformation index induced by a source deformation index. -/
def mapDeformation {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    {P : AnalyticContourPushforward S}
    (D : AnalyticTransportDeformationCompatibility P)
    {s t : X.contour.exhaustion.Stage}
    (d : X.contour.DeformationIndex s t) :
    Y.contour.DeformationIndex (P.stageMap s) (P.stageMap t) :=
  D.deformationMap d

end AnalyticTransportDeformationCompatibility

end AnalyticMotives
end LFunctions
end Boundary
