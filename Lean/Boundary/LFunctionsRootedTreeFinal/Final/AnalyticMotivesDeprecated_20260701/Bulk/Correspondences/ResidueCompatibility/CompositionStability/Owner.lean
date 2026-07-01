import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.ResidueCompatibility.Commutation.Owner

/-!
# Composition stability of residue compatibility

This file owns stability of residue-pushforward commutation under composition
of contour-compatible correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Composition-stability data for residue compatibility.  It records the
residue-commutation squares for a composite transport.  The aggregate
`AnalyticResidueCompatibility` structure consumes this data downstream.
-/
structure AnalyticResidueCompositionStabilityData
    {X Z : ContourAdmissibleBulk}
    {Sxz : AnalyticCorrespondenceSupport X Z}
    (Txz : AnalyticContourTransport Sxz) where
  compositeCommutation :
    (s : X.contour.exhaustion.Stage) →
      (i : X.boundary.FaceIndex) →
        AnalyticResidueCommutation (T := Txz) s i

namespace AnalyticResidueCompositionStabilityData

/-- The residue commutation datum selected for a composite transport. -/
def commutationAt {X Z : ContourAdmissibleBulk}
    {Sxz : AnalyticCorrespondenceSupport X Z}
    {Txz : AnalyticContourTransport Sxz}
    (C : AnalyticResidueCompositionStabilityData Txz)
    (s : X.contour.exhaustion.Stage) (i : X.boundary.FaceIndex) :
    AnalyticResidueCommutation (T := Txz) s i :=
  C.compositeCommutation s i

end AnalyticResidueCompositionStabilityData

end AnalyticMotives
end LFunctions
end Boundary
