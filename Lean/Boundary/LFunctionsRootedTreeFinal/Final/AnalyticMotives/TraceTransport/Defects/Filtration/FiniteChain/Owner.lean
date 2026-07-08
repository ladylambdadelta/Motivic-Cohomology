import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.TwoStep.Owner

/-!
# Finite-chain filtrations of transport defects

This file extends the two-step associated-graded defect ledger to finite lists
of trace transports.  The construction is concrete: it recursively appends the
path-defect ledger of each transport in the list.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The associated-graded defect ledger for a finite transport chain. -/
def TraceTransport.finiteChainAssociatedGradedDefect :
    List TraceTransport → ResidueChannelCertificateLedger
  | [] => ResidueChannelCertificateLedger.empty
  | transport :: tail =>
      ResidueChannelCertificateLedger.append
        transport.defectLedger
        (TraceTransport.finiteChainAssociatedGradedDefect tail)

/-- The empty transport chain has empty associated-graded defect ledger. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_nil :
    TraceTransport.finiteChainAssociatedGradedDefect [] =
      ResidueChannelCertificateLedger.empty :=
  rfl

/-- A nonempty transport chain splits into the head defect ledger and the tail
associated-graded defect ledger. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_cons
    (transport : TraceTransport)
    (tail : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect
      (transport :: tail) =
      ResidueChannelCertificateLedger.append
        transport.defectLedger
        (TraceTransport.finiteChainAssociatedGradedDefect tail) :=
  rfl

/-- A singleton transport chain has the transport's defect ledger. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_singleton
    (transport : TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect [transport] =
      transport.defectLedger :=
  ResidueChannelCertificateLedger.append_empty
    transport.defectLedger

/-- A two-element chain recovers the two-step associated-graded defect ledger. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_pair
    (first second : TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect [first, second] =
      TraceTransport.twoStepAssociatedGradedDefect first second :=
  congrArg
    (fun ledger =>
      ResidueChannelCertificateLedger.append
        first.defectLedger
        ledger)
    (TraceTransport.finiteChainAssociatedGradedDefect_singleton second)

/-- The imported-rectangle count of a nonempty finite-chain associated-graded
defect splits into the head defect and tail chain counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_cons_importedRectangleCount
    (transport : TraceTransport)
    (tail : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (transport :: tail)).importedRectangleCount =
      transport.defectLedger.importedRectangleCount +
        (TraceTransport.finiteChainAssociatedGradedDefect tail).importedRectangleCount :=
  ResidueChannelCertificateLedger.append_importedRectangleCount
    transport.defectLedger
    (TraceTransport.finiteChainAssociatedGradedDefect tail)

/-- The rectangle list of a nonempty finite-chain associated-graded defect
splits into the head defect list and tail chain list. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_cons_importedRectangles
    (transport : TraceTransport)
    (tail : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (transport :: tail)).importedRectangles =
      transport.defectLedger.importedRectangles ++
        (TraceTransport.finiteChainAssociatedGradedDefect tail).importedRectangles :=
  ResidueChannelCertificateLedger.append_importedRectangles
    transport.defectLedger
    (TraceTransport.finiteChainAssociatedGradedDefect tail)

/-- The bookkeeping count of a nonempty finite-chain associated-graded defect
splits into the head defect and tail chain counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_cons_traceBookkeepingCount
    (transport : TraceTransport)
    (tail : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (transport :: tail)).traceBookkeepingCount =
      transport.defectLedger.traceBookkeepingCount +
        (TraceTransport.finiteChainAssociatedGradedDefect tail).traceBookkeepingCount :=
  ResidueChannelCertificateLedger.append_traceBookkeepingCount
    transport.defectLedger
    (TraceTransport.finiteChainAssociatedGradedDefect tail)

/-- The rewrite-step count of a nonempty finite-chain associated-graded defect
splits into the head defect and tail chain counts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_cons_rewriteStepCount
    (transport : TraceTransport)
    (tail : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (transport :: tail)).rewriteStepCount =
      transport.defectLedger.rewriteStepCount +
        (TraceTransport.finiteChainAssociatedGradedDefect tail).rewriteStepCount :=
  ResidueChannelCertificateLedger.append_rewriteStepCount
    transport.defectLedger
    (TraceTransport.finiteChainAssociatedGradedDefect tail)

end AnalyticMotives
end LFunctions
end Boundary
