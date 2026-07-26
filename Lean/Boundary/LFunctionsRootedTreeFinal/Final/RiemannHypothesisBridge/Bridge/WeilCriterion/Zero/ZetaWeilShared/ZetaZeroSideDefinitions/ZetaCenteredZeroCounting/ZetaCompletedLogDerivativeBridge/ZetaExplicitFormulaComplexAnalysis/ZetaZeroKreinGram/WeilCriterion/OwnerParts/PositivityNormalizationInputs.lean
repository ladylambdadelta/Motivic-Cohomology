import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.L5_MainTheoremAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.RightHalfPlaneGrowth.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part08_RightCriticalGrowth

/-!
# Normalization inputs for completed Weil positivity

This owner part exposes the already-proved completed-normalization packages
under short names for the final completed-Weil positivity assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Binet branch-tail absorption input for completed-Weil positivity. -/
theorem zetaWeilPositivity_binetBranchTailAbsorption_owner :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
  Complex.binetSecondFormulaBranchUniformTailAbsorption_owner

/-- Right boundary Abel partial-majorant input for completed-Weil positivity. -/
theorem zetaWeilPositivity_boundaryLineOneAbelPartialMajorant_owner :
    BoundaryLineOneAbelPartialMajorant :=
  boundaryLineOneAbelPartialMajorant_from_realParam

/-- Compact `1 ≤ Re s ≤ 2` pole-cleared boundary input for completed-Weil
positivity. -/
theorem zetaWeilPositivity_oneTwoStripCompactBoundaryBound_owner :
    PoleClearedOneTwoStripCompactBoundaryBound :=
  poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact

/-- Reflected left-boundary Abel partial-majorant input for completed-Weil
positivity. -/
theorem zetaWeilPositivity_reflectedBoundaryAbelPartialMajorant_owner :
    ReflectedBoundaryAbelPartialMajorant :=
  reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
    zetaWeilPositivity_boundaryLineOneAbelPartialMajorant_owner

/-- Compact right-critical-strip pole-cleared boundary input for completed-Weil
positivity. -/
theorem zetaWeilPositivity_rightCriticalStripCompactBoundaryBound_owner :
    PoleClearedRightCriticalStripCompactBoundaryBound :=
  poleClearedRightCriticalStripCompactBoundaryBound_from_compact

/-- Self-reflected zero-one strip vertical-tail envelope for completed-Weil
positivity. -/
theorem zetaWeilPositivity_zeroOneStripSelfReflectedVerticalTailEnvelope_owner :
    PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope :=
  poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_owner

/-- Right-critical-strip admissible growth input for completed-Weil positivity. -/
theorem zetaWeilPositivity_rightCriticalStripAdmissibleGrowth_owner :
    PoleClearedRightCriticalStripAdmissibleGrowth :=
  poleClearedRightCriticalStripAdmissibleGrowth_owner
    zetaWeilPositivity_binetBranchTailAbsorption_owner
    zetaWeilPositivity_zeroOneStripSelfReflectedVerticalTailEnvelope_owner

end

end LFunctions
end Boundary
