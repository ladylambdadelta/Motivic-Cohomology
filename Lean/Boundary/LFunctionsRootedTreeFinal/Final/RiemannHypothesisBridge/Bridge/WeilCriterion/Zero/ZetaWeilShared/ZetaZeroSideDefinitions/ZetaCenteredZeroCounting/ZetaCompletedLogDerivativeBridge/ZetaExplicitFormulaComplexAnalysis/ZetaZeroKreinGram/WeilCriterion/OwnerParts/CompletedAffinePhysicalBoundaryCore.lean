import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part05
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.NormalizedContourProjection

/-!
# Completed affine physical boundary core

This file owns the selector-free affine physical boundary channels used by the
Weil positivity bridge.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The physical affine subchannel seen by the completed right-minus-left
vertical packet before the explicit correction channel is normalized. -/
noncomputable def zetaCompletedAffinePhysicalBoundaryChannel
    (probe : ZetaAdmissibleFunction) : ℂ :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution probe +
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
      probe /
      ZetaAdmissibleFunction.explicitFormulaTwoPi

/-- The physical affine subchannel unfolds to prime plus the normalized raw
Hermitian archimedean affine contribution. -/
theorem zetaCompletedAffinePhysicalBoundaryChannel_eq
    (probe : ZetaAdmissibleFunction) :
    zetaCompletedAffinePhysicalBoundaryChannel probe =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
          probe +
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
          probe /
          ZetaAdmissibleFunction.explicitFormulaTwoPi :=
  rfl

/-- The affine pole-corrected subchannel obtained from the raw affine physical
subchannel by subtracting the completed pole-residue packet. -/
noncomputable def zetaCompletedAffinePoleCorrectedBoundaryChannel
    (probe : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedAffinePhysicalBoundaryChannel probe -
    ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum
      probe

/-- The affine pole-corrected subchannel unfolds by subtracting the completed
pole-residue packet from the affine physical subchannel. -/
theorem zetaCompletedAffinePoleCorrectedBoundaryChannel_eq
    (probe : ZetaAdmissibleFunction) :
    zetaCompletedAffinePoleCorrectedBoundaryChannel probe =
      zetaCompletedAffinePhysicalBoundaryChannel probe -
        ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum
          probe :=
  rfl

end

end LFunctions
end Boundary
