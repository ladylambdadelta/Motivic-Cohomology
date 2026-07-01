import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Chains.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.Owner

/-!
# Contour pushforward along correspondence supports

This file owns the contour-chain pushforward associated to an analytic
correspondence support.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Contour-stage pushforward along an analytic correspondence support.  A source
contour stage is assigned a target contour stage, keeping transport inside the
admissible contour systems rather than producing a scalar trace.
-/
structure AnalyticContourPushforward {X Y : ContourAdmissibleBulk}
    (S : AnalyticCorrespondenceSupport X Y) where
  stageMap :
    X.contour.exhaustion.Stage → Y.contour.exhaustion.Stage
  chainMap :
    (s : X.contour.exhaustion.Stage) →
      AnalyticBulkCoreHom
        (X.contour.exhaustion.chain s).domain
        (Y.contour.exhaustion.chain (stageMap s)).domain

namespace AnalyticContourPushforward

/-- The target contour stage assigned to a source contour stage. -/
def stageAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (P : AnalyticContourPushforward S)
    (s : X.contour.exhaustion.Stage) : Y.contour.exhaustion.Stage :=
  P.stageMap s

/-- The target contour chain assigned to a source contour stage. -/
def chainAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (P : AnalyticContourPushforward S)
    (s : X.contour.exhaustion.Stage) :
    AnalyticContourChain Y.boundary :=
  Y.contour.exhaustion.chain (P.stageMap s)

/-- The map of contour-chain domains assigned to a source contour stage. -/
def chainMapAt {X Y : ContourAdmissibleBulk}
    {S : AnalyticCorrespondenceSupport X Y}
    (P : AnalyticContourPushforward S)
    (s : X.contour.exhaustion.Stage) :
    AnalyticBulkCoreHom
      (X.contour.exhaustion.chain s).domain
      (Y.contour.exhaustion.chain (P.stageMap s)).domain :=
  P.chainMap s

end AnalyticContourPushforward

end AnalyticMotives
end LFunctions
end Boundary
