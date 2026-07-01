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

/-- The one-step trace transport for the zero-pole finite-square residue seed. -/
def completedZetaZeroPoleResidueTransport : TraceTransport :=
  (completedZetaZeroPoleResiduePresentationSpine,
    completedZetaZeroPoleResidueOutputSpine,
    completedZetaZeroPoleResiduePath)

/-- The residue transport starts at the certified residue presentation spine. -/
theorem completedZetaZeroPoleResidueTransport_source :
    completedZetaZeroPoleResidueTransport.source =
      completedZetaZeroPoleResiduePresentationSpine :=
  rfl

/-- The residue transport targets the residue output spine. -/
theorem completedZetaZeroPoleResidueTransport_target :
    completedZetaZeroPoleResidueTransport.target =
      completedZetaZeroPoleResidueOutputSpine :=
  rfl

/-- The residue transport carries the one-step residue path. -/
theorem completedZetaZeroPoleResidueTransport_path :
    completedZetaZeroPoleResidueTransport.path =
      completedZetaZeroPoleResiduePath :=
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

/-- The one-step trace transport for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleChannelTransport : TraceTransport :=
  (completedZetaZeroPoleChannelPresentationSpine,
    completedZetaZeroPoleChannelOutputSpine,
    completedZetaZeroPoleChannelPath)

/-- The channel transport starts at the certified channel presentation spine. -/
theorem completedZetaZeroPoleChannelTransport_source :
    completedZetaZeroPoleChannelTransport.source =
      completedZetaZeroPoleChannelPresentationSpine :=
  rfl

/-- The channel transport targets the channel output spine. -/
theorem completedZetaZeroPoleChannelTransport_target :
    completedZetaZeroPoleChannelTransport.target =
      completedZetaZeroPoleChannelOutputSpine :=
  rfl

/-- The channel transport carries the one-step channel path. -/
theorem completedZetaZeroPoleChannelTransport_path :
    completedZetaZeroPoleChannelTransport.path =
      completedZetaZeroPoleChannelPath :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
