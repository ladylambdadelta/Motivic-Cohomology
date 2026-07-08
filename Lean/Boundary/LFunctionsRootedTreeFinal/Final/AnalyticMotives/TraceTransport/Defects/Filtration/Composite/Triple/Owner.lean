import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.Composite.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Associativity.Rebracketing.Owner

/-!
# Triple composite defect filtrations

This file relates the left- and right-associated three-factor defect
filtrations through the finite-chain rebracketing theorem.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated three-factor associated-graded defect ledger. -/
def TraceTransport.leftTripleAssociatedGradedDefect
    (first second third : TraceTransport) :
    ResidueChannelCertificateLedger :=
  TraceTransport.finiteChainAssociatedGradedDefect
    (([first] ++ [second]) ++ [third])

/-- The right-associated three-factor associated-graded defect ledger. -/
def TraceTransport.rightTripleAssociatedGradedDefect
    (first second third : TraceTransport) :
    ResidueChannelCertificateLedger :=
  TraceTransport.finiteChainAssociatedGradedDefect
    ([first] ++ ([second] ++ [third]))

/-- The left-associated triple defect ledger is the finite-chain defect of the
left-associated singleton block decomposition. -/
theorem TraceTransport.leftTripleAssociatedGradedDefect_eq
    (first second third : TraceTransport) :
    TraceTransport.leftTripleAssociatedGradedDefect first second third =
      TraceTransport.finiteChainAssociatedGradedDefect
        (([first] ++ [second]) ++ [third]) :=
  rfl

/-- The right-associated triple defect ledger is the finite-chain defect of the
right-associated singleton block decomposition. -/
theorem TraceTransport.rightTripleAssociatedGradedDefect_eq
    (first second third : TraceTransport) :
    TraceTransport.rightTripleAssociatedGradedDefect first second third =
      TraceTransport.finiteChainAssociatedGradedDefect
        ([first] ++ ([second] ++ [third])) :=
  rfl

/-- Rebracketing a three-factor composite preserves the associated-graded
defect ledger. -/
theorem TraceTransport.tripleAssociatedGradedDefect_rebracket
    (first second third : TraceTransport) :
    TraceTransport.leftTripleAssociatedGradedDefect first second third =
      TraceTransport.rightTripleAssociatedGradedDefect first second third :=
  TraceTransport.finiteChainAssociatedGradedDefect_rebracket
    [first]
    [second]
    [third]

/-- Rebracketing a three-factor composite preserves imported-rectangle counts. -/
theorem TraceTransport.tripleAssociatedGradedDefect_rebracket_importedRectangleCount
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).importedRectangleCount =
      (TraceTransport.rightTripleAssociatedGradedDefect
        first
        second
        third).importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceTransport.tripleAssociatedGradedDefect_rebracket
      first
      second
      third)

/-- Rebracketing a three-factor composite preserves imported-rectangle lists. -/
theorem TraceTransport.tripleAssociatedGradedDefect_rebracket_importedRectangles
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).importedRectangles =
      (TraceTransport.rightTripleAssociatedGradedDefect
        first
        second
        third).importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceTransport.tripleAssociatedGradedDefect_rebracket
      first
      second
      third)

/-- Rebracketing a three-factor composite preserves bookkeeping counts. -/
theorem TraceTransport.tripleAssociatedGradedDefect_rebracket_traceBookkeepingCount
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).traceBookkeepingCount =
      (TraceTransport.rightTripleAssociatedGradedDefect
        first
        second
        third).traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceTransport.tripleAssociatedGradedDefect_rebracket
      first
      second
      third)

/-- Rebracketing a three-factor composite preserves rewrite-step counts. -/
theorem TraceTransport.tripleAssociatedGradedDefect_rebracket_rewriteStepCount
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).rewriteStepCount =
      (TraceTransport.rightTripleAssociatedGradedDefect
        first
        second
        third).rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceTransport.tripleAssociatedGradedDefect_rebracket
      first
      second
      third)

end AnalyticMotives
end LFunctions
end Boundary
