import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Associativity.Owner

/-!
# Rebracketing finite-chain defect filtrations

This file records that reassociating the list of transport-chain blocks does
not change the finite-chain associated-graded defect ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rebracketing three finite transport-chain blocks preserves the associated
graded defect ledger. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_rebracket
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third) =
      TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third)) :=
  congrArg
    TraceTransport.finiteChainAssociatedGradedDefect
    (List.append_assoc first second third)

/-- Rebracketing three finite transport-chain blocks preserves imported
rectangle counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_rebracket_importedRectangleCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceTransport.finiteChainAssociatedGradedDefect_rebracket
      first
      second
      third)

/-- Rebracketing three finite transport-chain blocks preserves imported
rectangle lists. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_rebracket_importedRectangles
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceTransport.finiteChainAssociatedGradedDefect_rebracket
      first
      second
      third)

/-- Rebracketing three finite transport-chain blocks preserves bookkeeping
counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_rebracket_traceBookkeepingCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceTransport.finiteChainAssociatedGradedDefect_rebracket
      first
      second
      third)

/-- Rebracketing three finite transport-chain blocks preserves rewrite-step
counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_rebracket_rewriteStepCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect
        (first ++ (second ++ third))).rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceTransport.finiteChainAssociatedGradedDefect_rebracket
      first
      second
      third)

end AnalyticMotives
end LFunctions
end Boundary
