import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ProjectionPrimitives
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.BasicChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionContribution

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The three scheduled vertical channel projections used by the contour-spine bridge. -/
inductive ExplicitFormulaScheduledVerticalChannelProjection where
  | prime
  | archimedean
  | correction

/-- The realized vertical contour integral attached to a scheduled channel projection. -/
noncomputable def explicitFormulaScheduledVerticalChannelProjectionIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  match channel with
  | ExplicitFormulaScheduledVerticalChannelProjection.prime =>
      zetaCompletedExplicitFormulaPrimeVerticalChannel f F T
  | ExplicitFormulaScheduledVerticalChannelProjection.archimedean =>
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T
  | ExplicitFormulaScheduledVerticalChannelProjection.correction =>
      zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T

/-- The boundary contribution attached to a scheduled channel projection. -/
noncomputable def explicitFormulaScheduledVerticalChannelProjectionContribution
    (f : ZetaAdmissibleFunction)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  match channel with
  | ExplicitFormulaScheduledVerticalChannelProjection.prime =>
      zetaCompletedExplicitFormulaPrimeContribution f
  | ExplicitFormulaScheduledVerticalChannelProjection.archimedean =>
      zetaCompletedExplicitFormulaArchimedeanContribution f
  | ExplicitFormulaScheduledVerticalChannelProjection.correction =>
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f

/-- The transport remainder attached to a scheduled vertical channel projection. -/
noncomputable def explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledVerticalChannelProjectionIntegral f F T channel -
    explicitFormulaScheduledVerticalChannelProjectionContribution f channel

/-- The scheduled projected vertical-decomposition error is the selected channel transport
remainder at the scheduled height. -/
noncomputable def explicitFormulaScheduledProjectedVerticalDecompositionError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
    f F (h.height_schedule.height u) channel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
