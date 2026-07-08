import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Append.Owner

/-!
# Unit laws for finite-chain defect filtrations

This file records the empty-chain unit laws for finite-chain
associated-graded defect ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Appending an empty chain on the left preserves the associated-graded defect
ledger. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_empty_append
    (chain : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect ([] ++ chain) =
      TraceTransport.finiteChainAssociatedGradedDefect chain :=
  rfl

/-- Appending an empty chain on the right preserves the associated-graded defect
ledger. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_empty
    (chain : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect (chain ++ []) =
      TraceTransport.finiteChainAssociatedGradedDefect chain :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append
      chain
      [])
    (ResidueChannelCertificateLedger.append_empty
      (TraceTransport.finiteChainAssociatedGradedDefect chain))

/-- Empty left append preserves finite-chain imported-rectangle counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_empty_append_importedRectangleCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceTransport.finiteChainAssociatedGradedDefect_empty_append chain)

/-- Empty right append preserves finite-chain imported-rectangle counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_empty_importedRectangleCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceTransport.finiteChainAssociatedGradedDefect_append_empty chain)

/-- Empty left append preserves finite-chain rectangle lists. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_empty_append_importedRectangles
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceTransport.finiteChainAssociatedGradedDefect_empty_append chain)

/-- Empty right append preserves finite-chain rectangle lists. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_empty_importedRectangles
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceTransport.finiteChainAssociatedGradedDefect_append_empty chain)

/-- Empty left append preserves finite-chain bookkeeping counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_empty_append_traceBookkeepingCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceTransport.finiteChainAssociatedGradedDefect_empty_append chain)

/-- Empty right append preserves finite-chain bookkeeping counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_empty_traceBookkeepingCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceTransport.finiteChainAssociatedGradedDefect_append_empty chain)

/-- Empty left append preserves finite-chain rewrite-step counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_empty_append_rewriteStepCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ([] ++ chain)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceTransport.finiteChainAssociatedGradedDefect_empty_append chain)

/-- Empty right append preserves finite-chain rewrite-step counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_empty_rewriteStepCount
    (chain : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (chain ++ [])).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect chain).rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceTransport.finiteChainAssociatedGradedDefect_append_empty chain)

end AnalyticMotives
end LFunctions
end Boundary
