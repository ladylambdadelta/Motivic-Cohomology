import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleGenerator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelGenerator.Owner

/-!
# Zero-pole presentation spines

This file packages the two completed-zeta zero-pole seeds as raw
residue-channel presentation spines.

These spines are finite bookkeeping objects.  The analytic certificates are
the concrete soundness theorems in `ZeroPoleGenerator` and
`ZeroPoleChannelGenerator`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The residue ledger entry created by the zero-pole finite-square residue seed. -/
def completedZetaZeroPoleResidueLedgerEntry : ResidueLedgerEntry :=
  (completedZetaZeroPoleFiniteSquareFace,
    completedZetaZeroPoleFiniteSquareResidueExpression)

/-- The residue ledger for the zero-pole finite-square residue seed. -/
def completedZetaZeroPoleResidueLedger : ResidueLedger :=
  ResidueLedger.cons
    completedZetaZeroPoleResidueLedgerEntry
    ResidueLedger.empty

/-- The raw presentation spine for the zero-pole finite-square residue seed. -/
def completedZetaZeroPoleResiduePresentationSpine :
    ResidueChannelPresentationSpine :=
  (completedZetaZeroPoleFiniteSquareBoundaryExpression,
    completedZetaZeroPoleResidueLedger,
    ResidueChannelExpressionList.empty,
    TraceSchedule.cons
      TraceRewriteKind.residue
      TraceSchedule.empty)

/-- The residue presentation spine starts at the finite-square boundary expression. -/
theorem completedZetaZeroPoleResiduePresentationSpine_source :
    completedZetaZeroPoleResiduePresentationSpine.source =
      completedZetaZeroPoleFiniteSquareBoundaryExpression :=
  rfl

/-- The residue presentation spine records the finite-square zero-pole residue ledger. -/
theorem completedZetaZeroPoleResiduePresentationSpine_ledger :
    completedZetaZeroPoleResiduePresentationSpine.ledger =
      completedZetaZeroPoleResidueLedger :=
  rfl

/-- The residue presentation spine has no channel outputs. -/
theorem completedZetaZeroPoleResiduePresentationSpine_channels :
    completedZetaZeroPoleResiduePresentationSpine.channels =
      ResidueChannelExpressionList.empty :=
  rfl

/-- The residue presentation spine has a one-step residue schedule. -/
theorem completedZetaZeroPoleResiduePresentationSpine_schedule :
    completedZetaZeroPoleResiduePresentationSpine.schedule =
      TraceSchedule.cons
        TraceRewriteKind.residue
        TraceSchedule.empty :=
  rfl

/-- The right vertical channel expression in the zero-pole channel seed. -/
def completedZetaZeroPoleRightVerticalChannelExpression :
    ResidueChannelExpression :=
  (completedZetaZeroPoleRightVerticalChannel,
    QTraceExpression.singleton
      1
      completedZetaZeroPoleRightVerticalAtom)

/-- The horizontal channel expression in the zero-pole channel seed. -/
def completedZetaZeroPoleHorizontalChannelExpression :
    ResidueChannelExpression :=
  (completedZetaZeroPoleHorizontalChannel,
    QTraceExpression.singleton
      1
      completedZetaZeroPoleHorizontalAtom)

/-- The visible channel list for the zero-pole channel seed. -/
def completedZetaZeroPoleChannelExpressionList :
    ResidueChannelExpressionList :=
  completedZetaZeroPoleRightVerticalChannelExpression ::
    completedZetaZeroPoleHorizontalChannelExpression ::
      []

/-- The raw presentation spine for the zero-pole scheduled channel seed. -/
def completedZetaZeroPoleChannelPresentationSpine :
    ResidueChannelPresentationSpine :=
  (completedZetaZeroPoleChannelSourceExpression,
    ResidueLedger.empty,
    completedZetaZeroPoleChannelExpressionList,
    TraceSchedule.cons
      TraceRewriteKind.channel
      TraceSchedule.empty)

/-- The channel presentation spine starts at the left vertical channel. -/
theorem completedZetaZeroPoleChannelPresentationSpine_source :
    completedZetaZeroPoleChannelPresentationSpine.source =
      completedZetaZeroPoleChannelSourceExpression :=
  rfl

/-- The channel presentation spine has no residue ledger entries. -/
theorem completedZetaZeroPoleChannelPresentationSpine_ledger :
    completedZetaZeroPoleChannelPresentationSpine.ledger =
      ResidueLedger.empty :=
  rfl

/-- The channel presentation spine records the right and horizontal channels. -/
theorem completedZetaZeroPoleChannelPresentationSpine_channels :
    completedZetaZeroPoleChannelPresentationSpine.channels =
      completedZetaZeroPoleChannelExpressionList :=
  rfl

/-- The channel presentation spine has a one-step channel schedule. -/
theorem completedZetaZeroPoleChannelPresentationSpine_schedule :
    completedZetaZeroPoleChannelPresentationSpine.schedule =
      TraceSchedule.cons
        TraceRewriteKind.channel
        TraceSchedule.empty :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
