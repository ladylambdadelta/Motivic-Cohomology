import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Owner

/-!
# Composite transport defect filtrations

This file relates the defect filtration attached to a binary transport
composition to the finite-chain associated-graded defect filtration of its two
factors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The associated-graded defect ledger attached to a binary transport
composition, viewed as the finite chain of its two factors. -/
def TraceTransport.compAssociatedGradedDefect
    (first second : TraceTransport) :
    ResidueChannelCertificateLedger :=
  TraceTransport.finiteChainAssociatedGradedDefect [first, second]

/-- The composite associated-graded defect agrees with the finite-chain
two-factor construction. -/
theorem TraceTransport.compAssociatedGradedDefect_eq_finiteChain
    (first second : TraceTransport) :
    TraceTransport.compAssociatedGradedDefect first second =
      TraceTransport.finiteChainAssociatedGradedDefect [first, second] :=
  rfl

/-- The composite associated-graded defect agrees with the two-step
associated-graded defect. -/
theorem TraceTransport.compAssociatedGradedDefect_eq_twoStep
    (first second : TraceTransport) :
    TraceTransport.compAssociatedGradedDefect first second =
      TraceTransport.twoStepAssociatedGradedDefect first second :=
  TraceTransport.finiteChainAssociatedGradedDefect_pair
    first
    second

/-- The composite associated-graded defect rewrite-step count is the two-step
associated-graded rewrite-step count. -/
theorem TraceTransport.compAssociatedGradedDefect_rewriteStepCount_eq_twoStep
    (first second : TraceTransport) :
    (TraceTransport.compAssociatedGradedDefect first second).rewriteStepCount =
      (TraceTransport.twoStepAssociatedGradedDefect
        first
        second).rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceTransport.compAssociatedGradedDefect_eq_twoStep first second)

/-- The composite associated-graded defect imported-rectangle count is the
two-step associated-graded imported-rectangle count. -/
theorem TraceTransport.compAssociatedGradedDefect_importedRectangleCount_eq_twoStep
    (first second : TraceTransport) :
    (TraceTransport.compAssociatedGradedDefect first second).importedRectangleCount =
      (TraceTransport.twoStepAssociatedGradedDefect
        first
        second).importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceTransport.compAssociatedGradedDefect_eq_twoStep first second)

/-- The composite associated-graded defect rectangle list is the two-step
associated-graded rectangle list. -/
theorem TraceTransport.compAssociatedGradedDefect_importedRectangles_eq_twoStep
    (first second : TraceTransport) :
    (TraceTransport.compAssociatedGradedDefect first second).importedRectangles =
      (TraceTransport.twoStepAssociatedGradedDefect
        first
        second).importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceTransport.compAssociatedGradedDefect_eq_twoStep first second)

/-- The composite associated-graded defect bookkeeping count is the two-step
associated-graded bookkeeping count. -/
theorem TraceTransport.compAssociatedGradedDefect_traceBookkeepingCount_eq_twoStep
    (first second : TraceTransport) :
    (TraceTransport.compAssociatedGradedDefect first second).traceBookkeepingCount =
      (TraceTransport.twoStepAssociatedGradedDefect
        first
        second).traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceTransport.compAssociatedGradedDefect_eq_twoStep first second)

end AnalyticMotives
end LFunctions
end Boundary
