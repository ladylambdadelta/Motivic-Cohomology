import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.Owner

/-!
# Composition of contour transport

This file owns the transport-level composition data for contour-compatible
analytic correspondences.  It is downstream from pushforward, deformation
compatibility, and boundary compatibility, and upstream from full
correspondence composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Composition data for contour transport.  It records the two input transports
and a chosen composite transport over a chosen composite support.
-/
structure AnalyticContourTransportCompositionData
    {X Y Z : ContourAdmissibleBulk}
    {Sxy : AnalyticCorrespondenceSupport X Y}
    {Syz : AnalyticCorrespondenceSupport Y Z}
    (Sxz : AnalyticCorrespondenceSupport X Z)
    (Txy : AnalyticContourTransport Sxy)
    (Tyz : AnalyticContourTransport Syz) where
  compositeTransport : AnalyticContourTransport Sxz
  stage_comp :
    (s : X.contour.exhaustion.Stage) →
      compositeTransport.pushforward.stageMap s =
        Tyz.pushforward.stageMap (Txy.pushforward.stageMap s)

namespace AnalyticContourTransportCompositionData

/-- The selected composite contour transport. -/
def transport {X Y Z : ContourAdmissibleBulk}
    {Sxy : AnalyticCorrespondenceSupport X Y}
    {Syz : AnalyticCorrespondenceSupport Y Z}
    {Sxz : AnalyticCorrespondenceSupport X Z}
    {Txy : AnalyticContourTransport Sxy}
    {Tyz : AnalyticContourTransport Syz}
    (C : AnalyticContourTransportCompositionData Sxz Txy Tyz) :
    AnalyticContourTransport Sxz :=
  C.compositeTransport

/-- The stage-level composition law for composed contour transport. -/
theorem stage_compose {X Y Z : ContourAdmissibleBulk}
    {Sxy : AnalyticCorrespondenceSupport X Y}
    {Syz : AnalyticCorrespondenceSupport Y Z}
    {Sxz : AnalyticCorrespondenceSupport X Z}
    {Txy : AnalyticContourTransport Sxy}
    {Tyz : AnalyticContourTransport Syz}
    (C : AnalyticContourTransportCompositionData Sxz Txy Tyz)
    (s : X.contour.exhaustion.Stage) :
    C.compositeTransport.pushforward.stageMap s =
      Tyz.pushforward.stageMap (Txy.pushforward.stageMap s) :=
  C.stage_comp s

end AnalyticContourTransportCompositionData

end AnalyticMotives
end LFunctions
end Boundary
