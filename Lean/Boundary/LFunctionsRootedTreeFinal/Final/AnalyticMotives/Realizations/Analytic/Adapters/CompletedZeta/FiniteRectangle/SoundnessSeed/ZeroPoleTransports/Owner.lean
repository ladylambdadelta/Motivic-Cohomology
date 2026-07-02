import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleCertifiedPresentations.Owner

/-!
# Zero-pole trace transports

This file packages the two certified zero-pole seeds as one-step raw trace
transports.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The one-step rewrite path for the zero-pole finite-square residue seed. -/
def completedZetaZeroPoleResiduePath : TraceRewritePath :=
  TraceRewritePath.ofGenerator
    completedZetaZeroPoleFiniteSquareResidueGenerator

/-- The residue path starts at the finite-square boundary expression. -/
theorem completedZetaZeroPoleResiduePath_source :
    completedZetaZeroPoleResiduePath.source =
      completedZetaZeroPoleFiniteSquareBoundaryExpression :=
  completedZetaZeroPoleFiniteSquareResidueGenerator_source

/-- The residue path targets the finite-square residue expression. -/
theorem completedZetaZeroPoleResiduePath_target :
    completedZetaZeroPoleResiduePath.target =
      completedZetaZeroPoleFiniteSquareResidueExpression :=
  completedZetaZeroPoleFiniteSquareResidueGenerator_target

/-- The output presentation spine after the zero-pole residue extraction. -/
def completedZetaZeroPoleResidueOutputSpine :
    ResidueChannelPresentationSpine :=
  (completedZetaZeroPoleFiniteSquareResidueExpression,
    ResidueLedger.empty,
    ResidueChannelExpressionList.empty,
    TraceSchedule.empty)

/-- The residue output spine starts at the residue expression. -/
theorem completedZetaZeroPoleResidueOutputSpine_source :
    completedZetaZeroPoleResidueOutputSpine.source =
      completedZetaZeroPoleFiniteSquareResidueExpression :=
  rfl

/-- The certified output presentation after zero-pole residue extraction. -/
def completedZetaZeroPoleResidueOutput :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpine
    completedZetaZeroPoleResidueOutputSpine

/-- The certified residue output has the expected raw spine. -/
theorem completedZetaZeroPoleResidueOutput_spine :
    completedZetaZeroPoleResidueOutput.spine =
      completedZetaZeroPoleResidueOutputSpine :=
  rfl

/-- The residue output presentation has no imported finite-rectangle certificate atom. -/
theorem completedZetaZeroPoleResidueOutput_importedRectangleCount :
    completedZetaZeroPoleResidueOutput.importedRectangleCount =
      0 :=
  rfl

/-- The residue output presentation records its four component certificates. -/
theorem completedZetaZeroPoleResidueOutput_traceBookkeepingCount :
    completedZetaZeroPoleResidueOutput.traceBookkeepingCount =
      4 :=
  rfl

/-- The certified residue output starts at the residue expression. -/
theorem completedZetaZeroPoleResidueOutput_source :
    completedZetaZeroPoleResidueOutput.source =
      completedZetaZeroPoleFiniteSquareResidueExpression :=
  rfl

/-- The one-step trace transport for the zero-pole finite-square residue seed. -/
def completedZetaZeroPoleResidueTransport : TraceTransport :=
  {
    source := completedZetaZeroPoleResiduePresentation
    target := completedZetaZeroPoleResidueOutput
    path := completedZetaZeroPoleResiduePath
    path_source := completedZetaZeroPoleResiduePath_source
    path_target := completedZetaZeroPoleResiduePath_target
  }

/-- The residue transport starts at the certified residue presentation. -/
theorem completedZetaZeroPoleResidueTransport_source :
    completedZetaZeroPoleResidueTransport.source =
      completedZetaZeroPoleResiduePresentation :=
  rfl

/-- The residue transport targets the certified residue output. -/
theorem completedZetaZeroPoleResidueTransport_target :
    completedZetaZeroPoleResidueTransport.target =
      completedZetaZeroPoleResidueOutput :=
  rfl

/-- The residue transport carries the one-step residue path. -/
theorem completedZetaZeroPoleResidueTransport_path :
    completedZetaZeroPoleResidueTransport.path =
      completedZetaZeroPoleResiduePath :=
  rfl

/-- The current residue transport has no imported finite-rectangle certificate atom. -/
theorem completedZetaZeroPoleResidueTransport_importedRectangleCount :
    completedZetaZeroPoleResidueTransport.importedRectangleCount =
      0 :=
  rfl

/-- The current residue transport records both endpoints and its one-step rewrite path. -/
theorem completedZetaZeroPoleResidueTransport_traceBookkeepingCount :
    completedZetaZeroPoleResidueTransport.traceBookkeepingCount =
      9 :=
  rfl

/-- The one-step rewrite path for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleChannelPath : TraceRewritePath :=
  TraceRewritePath.ofGenerator
    completedZetaZeroPoleChannelGenerator

/-- The channel path starts at the left vertical channel expression. -/
theorem completedZetaZeroPoleChannelPath_source :
    completedZetaZeroPoleChannelPath.source =
      completedZetaZeroPoleChannelSourceExpression :=
  completedZetaZeroPoleChannelGenerator_source

/-- The channel path targets the right/horizontal/boundary channel expression. -/
theorem completedZetaZeroPoleChannelPath_target :
    completedZetaZeroPoleChannelPath.target =
      completedZetaZeroPoleChannelTargetExpression :=
  completedZetaZeroPoleChannelGenerator_target

/-- The output presentation spine after the zero-pole channel decomposition. -/
def completedZetaZeroPoleChannelOutputSpine :
    ResidueChannelPresentationSpine :=
  (completedZetaZeroPoleChannelTargetExpression,
    ResidueLedger.empty,
    completedZetaZeroPoleChannelExpressionList,
    TraceSchedule.empty)

/-- The channel output spine starts at the channel target expression. -/
theorem completedZetaZeroPoleChannelOutputSpine_source :
    completedZetaZeroPoleChannelOutputSpine.source =
      completedZetaZeroPoleChannelTargetExpression :=
  rfl

/-- The certified output presentation after zero-pole channel decomposition. -/
def completedZetaZeroPoleChannelOutput :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpine
    completedZetaZeroPoleChannelOutputSpine

/-- The certified channel output has the expected raw spine. -/
theorem completedZetaZeroPoleChannelOutput_spine :
    completedZetaZeroPoleChannelOutput.spine =
      completedZetaZeroPoleChannelOutputSpine :=
  rfl

/-- The channel output presentation has no imported finite-rectangle certificate atom. -/
theorem completedZetaZeroPoleChannelOutput_importedRectangleCount :
    completedZetaZeroPoleChannelOutput.importedRectangleCount =
      0 :=
  rfl

/-- The channel output presentation records its four component certificates. -/
theorem completedZetaZeroPoleChannelOutput_traceBookkeepingCount :
    completedZetaZeroPoleChannelOutput.traceBookkeepingCount =
      4 :=
  rfl

/-- The certified channel output starts at the channel target expression. -/
theorem completedZetaZeroPoleChannelOutput_source :
    completedZetaZeroPoleChannelOutput.source =
      completedZetaZeroPoleChannelTargetExpression :=
  rfl

/-- The one-step trace transport for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleChannelTransport : TraceTransport :=
  {
    source := completedZetaZeroPoleChannelPresentation
    target := completedZetaZeroPoleChannelOutput
    path := completedZetaZeroPoleChannelPath
    path_source := completedZetaZeroPoleChannelPath_source
    path_target := completedZetaZeroPoleChannelPath_target
  }

/-- The channel transport starts at the certified channel presentation. -/
theorem completedZetaZeroPoleChannelTransport_source :
    completedZetaZeroPoleChannelTransport.source =
      completedZetaZeroPoleChannelPresentation :=
  rfl

/-- The channel transport targets the certified channel output. -/
theorem completedZetaZeroPoleChannelTransport_target :
    completedZetaZeroPoleChannelTransport.target =
      completedZetaZeroPoleChannelOutput :=
  rfl

/-- The channel transport carries the one-step channel path. -/
theorem completedZetaZeroPoleChannelTransport_path :
    completedZetaZeroPoleChannelTransport.path =
      completedZetaZeroPoleChannelPath :=
  rfl

/-- The current channel transport has no imported finite-rectangle certificate atom. -/
theorem completedZetaZeroPoleChannelTransport_importedRectangleCount :
    completedZetaZeroPoleChannelTransport.importedRectangleCount =
      0 :=
  rfl

/-- The current channel transport records both endpoints and its one-step rewrite path. -/
theorem completedZetaZeroPoleChannelTransport_traceBookkeepingCount :
    completedZetaZeroPoleChannelTransport.traceBookkeepingCount =
      9 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
