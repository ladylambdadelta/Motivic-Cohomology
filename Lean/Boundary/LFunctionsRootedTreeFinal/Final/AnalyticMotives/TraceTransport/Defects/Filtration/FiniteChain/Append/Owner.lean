import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Owner

/-!
# Append compatibility for finite-chain defect filtrations

This file proves that the associated-graded defect ledger of a concatenated
transport chain is the append of the associated-graded defect ledgers of the
two chains.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Associated-graded transport defects preserve concatenation of finite
transport chains. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append
    (first second : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second) =
      ResidueChannelCertificateLedger.append
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (TraceTransport.finiteChainAssociatedGradedDefect second) :=
  match first with
  | [] =>
      Eq.symm
        (ResidueChannelCertificateLedger.empty_append
          (TraceTransport.finiteChainAssociatedGradedDefect second))
  | transport :: tail =>
      Eq.trans
        (congrArg
          (fun ledger =>
            ResidueChannelCertificateLedger.append
              transport.defectLedger
              ledger)
          (TraceTransport.finiteChainAssociatedGradedDefect_append
            tail
            second))
        (Eq.symm
          (ResidueChannelCertificateLedger.append_assoc
            transport.defectLedger
            (TraceTransport.finiteChainAssociatedGradedDefect tail)
            (TraceTransport.finiteChainAssociatedGradedDefect second)))

/-- The rewrite-step payload of a concatenated finite-chain associated-graded
defect splits across the two chain parts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_rewriteStepCount
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).rewriteStepCount +
        (TraceTransport.finiteChainAssociatedGradedDefect second).rewriteStepCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.rewriteStepCount
      (TraceTransport.finiteChainAssociatedGradedDefect_append
        first
        second))
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      (TraceTransport.finiteChainAssociatedGradedDefect first)
      (TraceTransport.finiteChainAssociatedGradedDefect second))

/-- The imported-rectangle payload of a concatenated finite-chain
associated-graded defect splits across the two chain parts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_importedRectangleCount
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangleCount +
        (TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangleCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangleCount
      (TraceTransport.finiteChainAssociatedGradedDefect_append
        first
        second))
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      (TraceTransport.finiteChainAssociatedGradedDefect first)
      (TraceTransport.finiteChainAssociatedGradedDefect second))

/-- The imported-rectangle list of a concatenated finite-chain associated-graded
defect splits across the two chain parts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_importedRectangles
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangles ++
        (TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangles :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangles
      (TraceTransport.finiteChainAssociatedGradedDefect_append
        first
        second))
    (ResidueChannelCertificateLedger.append_importedRectangles
      (TraceTransport.finiteChainAssociatedGradedDefect first)
      (TraceTransport.finiteChainAssociatedGradedDefect second))

/-- The bookkeeping payload of a concatenated finite-chain associated-graded
defect splits across the two chain parts. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_traceBookkeepingCount
    (first second : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      (first ++ second)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).traceBookkeepingCount +
        (TraceTransport.finiteChainAssociatedGradedDefect second).traceBookkeepingCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.traceBookkeepingCount
      (TraceTransport.finiteChainAssociatedGradedDefect_append
        first
        second))
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      (TraceTransport.finiteChainAssociatedGradedDefect first)
      (TraceTransport.finiteChainAssociatedGradedDefect second))

end AnalyticMotives
end LFunctions
end Boundary
